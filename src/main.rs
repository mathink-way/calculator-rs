use std::io::{self, Write};

use calculator_rs::run;

fn main() {
    print!("> ");
    if let Err(e) = io::stdout().flush() {
        eprintln!("Ошибка вывода: {e}");
        std::process::exit(1);
    }

    if let Err(e) = run() {
        eprintln!("Ошибка: {e}");
        std::process::exit(1);
    }
}
