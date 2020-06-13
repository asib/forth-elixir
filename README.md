# Forth evaluator

Basic evaluator for a very simple subset of Forth.

[Forth](https://en.wikipedia.org/wiki/Forth_%28programming_language%29)
is a stack-based programming language.

Supports the following words:

- `+`, `-`, `*`, `/` (integer arithmetic)
- `DUP`, `DROP`, `SWAP`, `OVER` (stack manipulation)

Also supports defining new words using the customary syntax: `: word-name definition ;`.
Words are case-insensitive.

The only supported datatype is signed integers of at least 16 bits size.

## Running tests

Execute the tests with:

```bash
$ mix test
```
