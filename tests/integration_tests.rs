//! Интеграционные тесты калькулятора.
//!
//! Тестируют публичный API библиотеки через функцию `evaluate`.

use calculator_rs::{CalcError, evaluate};

// ─────────────────────────────────────────────────────────────────────────────
// Базовые операции
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn basic_addition() {
    assert_eq!(evaluate("1 + 1").unwrap(), 2);
    assert_eq!(evaluate("100 + 200").unwrap(), 300);
    assert_eq!(evaluate("0 + 0").unwrap(), 0);
}

#[test]
fn basic_subtraction() {
    assert_eq!(evaluate("5 - 3").unwrap(), 2);
    assert_eq!(evaluate("3 - 5").unwrap(), -2);
    assert_eq!(evaluate("0 - 0").unwrap(), 0);
}

#[test]
fn basic_multiplication() {
    assert_eq!(evaluate("3 * 4").unwrap(), 12);
    assert_eq!(evaluate("0 * 100").unwrap(), 0);
    assert_eq!(evaluate("-3 * 4").unwrap(), -12);
}

#[test]
fn basic_division() {
    assert_eq!(evaluate("10 / 2").unwrap(), 5);
    assert_eq!(evaluate("7 / 3").unwrap(), 2); // целочисленное деление
    assert_eq!(evaluate("0 / 5").unwrap(), 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// Приоритет операций
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn precedence_mul_over_add() {
    assert_eq!(evaluate("2 + 3 * 4").unwrap(), 14); // не 20
    assert_eq!(evaluate("2 * 3 + 4").unwrap(), 10); // не 14
}

#[test]
fn precedence_div_over_sub() {
    assert_eq!(evaluate("10 - 6 / 2").unwrap(), 7); // не 2
}

#[test]
fn precedence_with_parens() {
    assert_eq!(evaluate("(2 + 3) * 4").unwrap(), 20);
    assert_eq!(evaluate("2 * (3 + 4)").unwrap(), 14);
    assert_eq!(evaluate("(10 - 6) / 2").unwrap(), 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// Унарные операторы
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn unary_minus() {
    assert_eq!(evaluate("-5").unwrap(), -5);
    assert_eq!(evaluate("--5").unwrap(), 5);
    assert_eq!(evaluate("-(-5)").unwrap(), 5);
}

#[test]
fn unary_plus() {
    assert_eq!(evaluate("+5").unwrap(), 5);
    assert_eq!(evaluate("++5").unwrap(), 5);
}

#[test]
fn unary_in_expression() {
    assert_eq!(evaluate("3 * -2").unwrap(), -6);
    assert_eq!(evaluate("3 + -2").unwrap(), 1);
    assert_eq!(evaluate("-3 + -2").unwrap(), -5);
}

// ─────────────────────────────────────────────────────────────────────────────
// Сложные выражения
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn complex_nested() {
    assert_eq!(evaluate("((1 + 2) * (3 + 4))").unwrap(), 21);
    assert_eq!(evaluate("((2))").unwrap(), 2);
    assert_eq!(evaluate("(((1 + 2)))").unwrap(), 3);
}

#[test]
fn complex_mixed() {
    assert_eq!(evaluate("1 + 2 * 3 - 4 / 2").unwrap(), 5);
    assert_eq!(evaluate("10 / 2 + 3 * 4 - 5").unwrap(), 12);
}

#[test]
fn long_chain() {
    assert_eq!(evaluate("1 + 2 + 3 + 4 + 5").unwrap(), 15);
    assert_eq!(evaluate("100 - 10 - 20 - 30").unwrap(), 40);
    assert_eq!(evaluate("2 * 2 * 2 * 2").unwrap(), 16);
}

// ─────────────────────────────────────────────────────────────────────────────
// Обработка ошибок
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn error_division_by_zero() {
    let result = evaluate("1 / 0");
    assert!(result.is_err());
    assert!(matches!(result, Err(CalcError::Eval(_))));
}

#[test]
fn error_division_by_zero_expr() {
    let result = evaluate("10 / (5 - 5)");
    assert!(result.is_err());
}

#[test]
fn error_empty_input() {
    assert!(evaluate("").is_err());
    assert!(evaluate("   ").is_err());
}

#[test]
fn error_invalid_syntax() {
    assert!(evaluate("1 +").is_err());
    assert!(evaluate("* 1").is_err());
    assert!(evaluate("1 2").is_err());
}

#[test]
fn error_unbalanced_parens() {
    assert!(evaluate("(1 + 2").is_err());
    assert!(evaluate("1 + 2)").is_err());
    assert!(evaluate("((1 + 2)").is_err());
}

#[test]
fn error_unknown_symbol() {
    assert!(evaluate("1 @ 2").is_err());
    assert!(evaluate("1 & 2").is_err());
}

// ─────────────────────────────────────────────────────────────────────────────
// Граничные случаи
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn whitespace_handling() {
    assert_eq!(evaluate("1+2").unwrap(), 3);
    assert_eq!(evaluate("  1  +  2  ").unwrap(), 3);
    assert_eq!(evaluate("\t1\t+\t2\t").unwrap(), 3);
}

#[test]
fn single_number() {
    assert_eq!(evaluate("42").unwrap(), 42);
    assert_eq!(evaluate("0").unwrap(), 0);
    assert_eq!(evaluate("  123  ").unwrap(), 123);
}

#[test]
fn large_numbers() {
    assert_eq!(evaluate("1000000 * 1000").unwrap(), 1_000_000_000);
    assert_eq!(evaluate("999999999 + 1").unwrap(), 1_000_000_000);
}

#[test]
fn overflow_detected() {
    let max = i64::MAX;
    let result = evaluate(&format!("{max} + 1"));
    assert!(result.is_err());

    let min = i64::MIN;
    let result = evaluate(&format!("{min} - 1"));
    assert!(result.is_err());
}
