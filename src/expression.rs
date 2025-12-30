//! Простое дерево выражений с вычислением (evaluate).
//!
//! Поддерживает литералы i64, унарные операции + и - и бинарные +, -, *, /.
//!
//! # Примеры (doctest)
//!
//! >>> use calculator_rs::expression::{Expr, UnaryOp, BinaryOp};
//! >>> let e = Expr::binary(BinaryOp::Add, Expr::literal(2), Expr::literal(3));
//! >>> assert_eq!(e.evaluate(), 5);
//!
//! >>> let e = Expr::unary(UnaryOp::Neg, Expr::literal(5));
//! >>> assert_eq!(e.evaluate(), -5);

/// Операции унарные.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Унарный плюс (идентичность).
    Plus,
    /// Унарный минус.
    Neg,
}

impl UnaryOp {
    /// Применить унарную операцию к значению.
    pub fn apply(self, value: i64) -> i64 {
        match self {
            UnaryOp::Plus => value,
            UnaryOp::Neg => -value,
        }
    }
}

/// Операции бинарные.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl BinaryOp {
    /// Применить бинарную операцию к операндам.
    ///
    /// # Panics
    ///
    /// Паникует при делении на ноль.
    pub fn apply(self, left: i64, right: i64) -> i64 {
        match self {
            BinaryOp::Add => left + right,
            BinaryOp::Sub => left - right,
            BinaryOp::Mul => left * right,
            BinaryOp::Div => left / right,
        }
    }
}

/// Дерево выражений.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Литеральное целое значение.
    Literal(i64),
    /// Унарная операция.
    Unary { kind: UnaryOp, child: Box<Expr> },
    /// Бинарная операция.
    Binary {
        kind: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
}

impl Expr {
    /// Создать литерал.
    pub fn literal(value: i64) -> Self {
        Expr::Literal(value)
    }

    /// Создать унарное выражение.
    pub fn unary(kind: UnaryOp, child: Expr) -> Self {
        Expr::Unary {
            kind,
            child: Box::new(child),
        }
    }

    /// Создать бинарное выражение.
    pub fn binary(kind: BinaryOp, left: Expr, right: Expr) -> Self {
        Expr::Binary {
            kind,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Вычислить значение выражения.
    ///
    /// Выполняет рекурсивную оценку дерева. Деление — целочисленное.
    pub fn evaluate(&self) -> i64 {
        match self {
            Expr::Literal(v) => *v,
            Expr::Unary { kind, child } => kind.apply(child.evaluate()),
            Expr::Binary { kind, left, right } => {
                let l = left.evaluate();
                let r = right.evaluate();
                kind.apply(l, r)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_eval() {
        assert_eq!(Expr::literal(0).evaluate(), 0);
        assert_eq!(Expr::literal(42).evaluate(), 42);
        assert_eq!(Expr::literal(-7).evaluate(), -7);
    }

    #[test]
    fn unary_plus_neg() {
        let e = Expr::unary(UnaryOp::Plus, Expr::literal(5));
        assert_eq!(e.evaluate(), 5);

        let e = Expr::unary(UnaryOp::Neg, Expr::literal(5));
        assert_eq!(e.evaluate(), -5);
    }

    #[test]
    fn binary_arithmetic() {
        let a = Expr::literal(10);
        let b = Expr::literal(3);

        assert_eq!(
            Expr::binary(BinaryOp::Add, a.clone(), b.clone()).evaluate(),
            13
        );
        assert_eq!(
            Expr::binary(BinaryOp::Sub, a.clone(), b.clone()).evaluate(),
            7
        );
        assert_eq!(
            Expr::binary(BinaryOp::Mul, a.clone(), b.clone()).evaluate(),
            30
        );
        assert_eq!(
            Expr::binary(BinaryOp::Div, a.clone(), b.clone()).evaluate(),
            3
        ); // 10 / 3 == 3
    }

    #[test]
    fn nested_expressions() {
        // (2 + 3) * -(4 - 6) = 5 * -(-2) = 5 * 2 = 10
        let expr = Expr::binary(
            BinaryOp::Mul,
            Expr::binary(BinaryOp::Add, Expr::literal(2), Expr::literal(3)),
            Expr::unary(
                UnaryOp::Neg,
                Expr::binary(BinaryOp::Sub, Expr::literal(4), Expr::literal(6)),
            ),
        );
        assert_eq!(expr.evaluate(), 10);
    }

    #[test]
    #[should_panic]
    fn div_by_zero_panics() {
        let expr = Expr::binary(BinaryOp::Div, Expr::literal(1), Expr::literal(0));
        let _ = expr.evaluate();
    }

    #[test]
    fn ops_apply_match() {
        // Проверим напрямую apply
        assert_eq!(UnaryOp::Plus.apply(5), 5);
        assert_eq!(UnaryOp::Neg.apply(5), -5);

        assert_eq!(BinaryOp::Add.apply(2, 3), 5);
        assert_eq!(BinaryOp::Sub.apply(5, 3), 2);
        assert_eq!(BinaryOp::Mul.apply(4, 3), 12);
        assert_eq!(BinaryOp::Div.apply(7, 2), 3);
    }

    #[test]
    fn eq_and_clone() {
        let a = Expr::binary(BinaryOp::Add, Expr::literal(1), Expr::literal(2));
        let b = a.clone();
        assert_eq!(a, b);
    }
}
