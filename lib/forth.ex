defmodule Forth do
  defmodule StackUnderflow do
    defexception []
    def message(_), do: "stack underflow"
  end

  defmodule InvalidWord do
    defexception word: nil
    def message(e), do: "invalid word: #{inspect(e.word)}"
  end

  defmodule UnknownWord do
    defexception word: nil
    def message(e), do: "unknown word: #{inspect(e.word)}"
  end

  defmodule DivisionByZero do
    defexception []
    def message(_), do: "division by zero"
  end

  defmodule Parser do
    def digit(), do: satisfy(char(), fn c -> c in ?0..?9 end)
    def char(ch), do: satisfy(char(), fn c -> c == ch end)
    def string(s), do: satisfy(count(char(), String.length(s)), fn t -> t == String.to_charlist(s) end)
    def ascii_letter(), do: satisfy(char(), fn c -> c in ?A..?Z or c in ?a..?z end)
    def whitespace(), do: one_or_more(char(?\s))
    def str_token(s), do: token(string(s))
    def case_insensitive_token(s), do: token(case_insensitive(s))

    def case_insensitive(s), do: satisfy(count(char(), String.length(s)), fn t -> String.downcase(to_string(t)) == String.downcase(s) end)

    def raise_on_fail(parser, exception) do
      fn input ->
        with {:error, _} <- parser.(input),
          do: raise exception
      end
    end

    def token(parser, separator),
      do: sequence([zero_or_more(separator), parser, separator])
          |> map(fn [_, token, _] -> token end)
    def token(parser), do: token(parser, whitespace())

    def map(parser, f) do
      fn input ->
        with {:ok, term, rest} <- parser.(input),
             do: {:ok, f.(term), rest}
      end
    end

    def sequence([]), do: &({:ok, [], &1})
    def sequence([p|ps]) do
      fn input ->
        with {:ok, term, rest} <- p.(input),
             {:ok, terms, rest} <- sequence(ps).(rest),
             do: {:ok, [term|terms], rest}
      end
    end

    def count(_, 0), do: fn i -> {:ok, [], i} end
    def count(parser, n) do
      fn input ->
        with {:ok, c, rest} <- parser.(input),
             {:ok, cs, rest} <- count(parser, n-1).(rest),
             do: {:ok, [c|cs], rest}
      end
    end

    def choice([]), do: fn _ -> {:error, [message: "no parsers succeeded"]} end
    def choice([p|ps]) do
      fn input ->
        with {:error, _} <- p.(input),
             do: choice(ps).(input)
      end
    end

    def zero_or_more(parser) do
      fn input ->
        case parser.(input) do
          {:error, _} -> {:ok, [], input}
          {:ok, term, rest} ->
            {:ok, other_terms, rest} = zero_or_more(parser).(rest)
            {:ok, [term | other_terms], rest}
        end
      end
    end

    def one_or_more(parser) do
      fn input ->
        with {:ok, term, rest} <- parser.(input) do
          case zero_or_more(parser).(rest) do
            {:ok, terms, rest} -> {:ok, [term | terms], rest}
            {:error, _}        -> {:ok, term, rest}
          end
        end
      end
    end

    def satisfy(parser, condition) do
      fn input ->
        with {:ok, term, rest} <- parser.(input) do
          if condition.(term),
            do: {:ok, term, rest},
            else: {:error, [message: "term rejected: #{term}, rest: #{inspect(rest)}"]}
        end
      end
    end

    def char() do
      fn input ->
        case input do
          "" -> {:error, "unexpected eos"}
          <<char::utf8, rest::binary>> -> {:ok, char, rest}
        end
      end
    end
  end

  @spec const(any) :: any
  defp const(x), do: fn _ -> x end

  defp map_word(parser, a), do: Parser.map(parser, const({:word, a}))

  @type word :: atom
  @type forth_word :: {:word, word}
  @type forth_number :: {:number, integer}
  @type forth_ast :: :plus
                   | :minus
                   | :multiply
                   | :divide
                   | :dup
                   | :drop
                   | :swap
                   | :over
                   | forth_number
                   | forth_word
                   | {:def, forth_word, [forth_ast]}

  @spec parse(String.t()) :: [forth_ast]
  defp parse(s) do
    parse_construct = Parser.choice([parse_def(), parse_any()]) |> Parser.one_or_more

    parse_construct.(s)
  end

  defp parse_separator(), do: Parser.char() |> Parser.satisfy(fn c -> c in 0..?\s or c == ?  end)
  defp parse_symbol(), do: Parser.char() |> Parser.satisfy(fn c -> c in ?!..?) or c in ?,..?. or c in ?<..?~ or c == ?€ end)
  defp parse_forth_token(parser), do: Parser.token(parser, parse_separator())
  defp parse_plus(), do: Parser.char(?+) |> parse_forth_token |> map_word(:plus)
  defp parse_minus(), do: Parser.char(?-) |> parse_forth_token |> map_word(:minus)
  defp parse_mult(), do: Parser.char(?*) |> parse_forth_token |> map_word(:mult)
  defp parse_div(), do: Parser.char(?/) |> parse_forth_token |> map_word(:div)
  defp parse_math(), do: Parser.choice([parse_plus(), parse_minus(), parse_mult(), parse_div()])
  defp parse_dup(), do: Parser.case_insensitive_token("dup") |> map_word(:dup)
  defp parse_drop(), do: Parser.case_insensitive_token("drop") |> map_word(:drop)
  defp parse_swap(), do: Parser.case_insensitive_token("swap") |> map_word(:swap)
  defp parse_over(), do: Parser.case_insensitive_token("over") |> map_word(:over)
  defp parse_number() do
    Parser.digit()
    |> Parser.one_or_more
    |> parse_forth_token
    |> Parser.map(fn n ->
      with {n_int, ""} <- Integer.parse(to_string(n)),
           do: {:number, n_int}
      end)
  end
  defp parse_word() do
    Parser.choice([Parser.ascii_letter(), Parser.digit(), parse_symbol()])
    |> Parser.one_or_more
    |> parse_forth_token
    |> Parser.satisfy(fn w -> Enum.all?(w, &(&1 not in ?0..?9)) end)
    |> Parser.map(fn w -> {:word, w |> to_string |> String.downcase |> String.to_atom} end)
  end
  defp parse_def() do
    Parser.sequence([
      Parser.char(?:) |> parse_forth_token,
      parse_word() |> Parser.raise_on_fail(InvalidWord),
      parse_any() |> Parser.one_or_more,
      Parser.char(?;) |> parse_forth_token,
    ])
    |> Parser.map(fn [_, w, d, _] -> {:def, w, d} end)
  end
  defp parse_any(), do: Parser.choice([
    parse_math(),
    parse_dup(),
    parse_drop(),
    parse_swap(),
    parse_over(),
    parse_number(),
    parse_word()
  ])

  @opaque evaluator :: Evaluator.t()

  defmodule Evaluator do
    defstruct [stack: [], defines: %{}]

    @type def_body :: [Forth.forth_ast]
                    | fun

    @opaque t :: %__MODULE__{
      stack: [Forth.forth_number],
      defines: %{required(atom) => def_body}
    }
  end

  @doc """
  Create a new evaluator.
  """
  @spec new() :: evaluator
  def new() do
    %Evaluator{defines: %{
      :plus => &(List.wrap(&2+&1)),
      :minus => &(List.wrap(&2-&1)),
      :mult => &(List.wrap(&2*&1)),
      :div => &(List.wrap(div(&2,&1))),
      :dup => &(List.duplicate(&1, 2)),
      :drop => fn _ -> [] end,
      :swap => &([&2, &1]),
      :over => &([&2, &1, &2])
    }}
  end

  @doc """
  Return the current stack as a string with the element on top of the stack
  being the rightmost element in the string.
  """
  @spec format_stack(evaluator) :: String.t()
  def format_stack(ev) do
    ev.stack
    |> Enum.reverse
    |> Enum.map(&to_string/1)
    |> Enum.join(" ")
  end

  @doc """
  Evaluate an input string, updating the evaluator state.
  """
  @spec eval(evaluator, String.t()) :: evaluator
  def eval(ev, s) do
    # Add a space at the end to ensure last token is read.
    with {:ok, terms, ""} <- parse(s <> " ") do
      eval_terms(ev, terms)
    end
  end

  @spec eval_terms(evaluator, [forth_ast]) :: evaluator
  defp eval_terms(ev, []), do: ev
  defp eval_terms(ev, [t|ts]) do
    eval_terms(eval_term(ev, t), ts)
  end

  @spec eval_term(evaluator, forth_ast) :: evaluator
  defp eval_term(ev, t) do
    case t do
      {:number, n} -> %{ev | stack: [n|ev.stack]}
      {:def, {:word, word}, expr} -> %{ev | defines: Map.put(ev.defines, word, expr)}
      {:word, word} -> eval_word(ev, word)
    end
  end

  @spec eval_word(evaluator, atom) :: evaluator
  defp eval_word(ev, word) do
    case Map.fetch(ev.defines, word) do
      :error -> raise UnknownWord, word: word
      {:ok, fun_def} ->
        cond do
          is_list(fun_def) -> eval_terms(ev, fun_def)
          true -> eval_fun(ev, fun_def)
        end
    end
  end

  @spec eval_fun(evaluator, fun) :: evaluator
  defp eval_fun(ev, f) do
    arity = :erlang.fun_info(f)[:arity]
    {args, rest} = Enum.split(ev.stack, arity)
    if Enum.count(args) != arity do
      raise StackUnderflow
    else
      try do
        %{ev | stack: Enum.concat(apply(f, args), rest)}
      rescue
        _ in ArithmeticError -> raise DivisionByZero
      end
    end
  end
end
