# calculator_rs

[![CI](https://github.com/mathink-way/calculator-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/mathink-way/calculator-rs/actions/workflows/ci.yml)

[![Coverage Status](https://coveralls.io/repos/github/mathink-way/calculator-rs/badge.svg?branch=main)](https://coveralls.io/github/mathink-way/calculator-rs?branch=main)

![GitHub top language](https://img.shields.io/github/languages/top/mathink-way/calculator-rs)

![GitHub license](https://img.shields.io/github/license/mathink-way/calculator-rs)

A simple command-line arithmetic calculator written in Rust.

## Features

- Integer arithmetic (`i64`)
- Binary operators: `+`, `-`, `*`, `/`
- Unary operators: `+`, `-`
- Parentheses for grouping
- Proper operator precedence
- Overflow and division-by-zero detection

## Grammar

The calculator implements standard arithmetic expression grammar:

```ebnf
expr   = term (('+' | '-') term)*
term   = unary (('*' | '/') unary)*
unary  = ('+' | '-')? factor
factor = NUMBER | '(' expr ')'
```

**Precedence** (highest to lowest):

1. Parentheses `()`
2. Unary `+`, `-`
3. Multiplication `*`, Division `/`
4. Addition `+`, Subtraction `-`

All binary operators are **left-associative**.

## Building

```bash
# Debug build
cargo build

# Release build
cargo build --release

# Run directly
cargo run
```

## Usage

### Interactive REPL

```bash
$ cargo run
Калькулятор. Введите выражение или 'q' для выхода.
> 2 + 3 * 4
14
> (2 + 3) * 4
20
> -5 + 10
5
> 1 / 0
Ошибка: деление на ноль
> q
До свидания!
```

Exit with `q`, `quit`, `exit`, or `Ctrl+D`.

### As a Library

```rust
use calculator_rs::evaluate;

fn main() {
    match evaluate("2 + 2 * 2") {
        Ok(result) => println!("Result: {result}"),
        Err(e) => eprintln!("Error: {e}"),
    }
}
```

## Project Structure

```tree
./calculator-rs/
├── src
│   ├── expression.rs           # AST and evaluation
│   ├── lib.rs                  # Library entry point, REPL logic
│   ├── main.rs                 # Binary entry point
│   ├── parser.rs               # Recursive descent parser
│   └── token.rs                # Lexer/tokenizer
├── tests
│   └── integration_tests.rs    # Integration tests
├── Cargo.lock
├── Cargo.toml
└── README.md
```

## Testing

```bash
# Run all tests
cargo test

# Run with output
cargo test -- --nocapture

# Run specific test
cargo test evaluate_simple
```

## Examples

| Expression | Result | Notes |
| ----------- | -------- | ------- |
| `2 + 3` | `5` | Addition |
| `10 - 3` | `7` | Subtraction |
| `4 * 5` | `20` | Multiplication |
| `7 / 3` | `2` | Integer division |
| `2 + 3 * 4` | `14` | Precedence: `2 + (3 * 4)` |
| `(2 + 3) * 4` | `20` | Parentheses |
| `-5` | `-5` | Unary minus |
| `--5` | `5` | Double negation |
| `1 - - 2` | `3` | `1 - (-2)` |

## Error Handling

The calculator handles errors gracefully:

- **Parse errors**: Invalid syntax, unbalanced parentheses
- **Evaluation errors**: Division by zero, integer overflow

```bash
> 1 / 0
Ошибка: деление на ноль

> 1 +
Ошибка: неожиданный конец ввода

> (1 + 2
Ошибка: отсутствует закрывающая скобка
```

## License

- MIT
