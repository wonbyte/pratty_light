use std::fmt::{Display, Formatter, Result};
use std::io::BufRead;

/// Represents a Lisp-style S-expression.
enum S {
    /// Represents an atomic S-expression containing a single character.
    Atom(char),
    /// Represents a compound S-expression consisting of a character and a
    /// vector of sub-expressions.
    Cons(char, Vec<S>),
}

impl Display for S {
    /// Formats the S-expression as a string.
    ///
    /// # Examples
    ///
    /// ```
    /// let s = S::Cons('a', vec![
    ///     S::Atom('b'),
    ///     S::Cons('c', vec![S::Atom('d'), S::Atom('e')])
    /// ]);
    ///
    /// assert_eq!(s.to_string(), "(a b (c d e))");
    /// ```
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            S::Atom(i) => write!(f, "{}", i),
            S::Cons(head, rest) => {
                write!(f, "({}", head)?;
                for s in rest {
                    write!(f, " {}", s)?
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// Represents a token in the lexer.
enum Token {
    /// Represents an atomic token containing a single character.
    Atom(char),
    /// Represents an operator token containing a single character.
    Op(char),
    /// Represents the end-of-file token.
    Eof,
}

/// Lexer struct is responsible for tokenizing input strings.
struct Lexer {
    /// Vector of tokens produced by the lexer.
    tokens: Vec<Token>,
}

impl Lexer {
    /// Creates a new instance of Lexer by tokenizing the input string.
    ///
    /// # Arguments
    ///
    /// * `input` - The input string to tokenize.
    ///
    /// # Examples
    ///
    /// ```
    /// let lexer = Lexer::new("123 + abc");
    /// let tokens = lexer.tokens;
    /// assert_eq!(tokens.len(), 5);
    /// ```
    fn new(input: &str) -> Lexer {
        let mut tokens = input
            .chars()
            .filter(|it| !it.is_ascii_whitespace())
            .map(|c| match c {
                '0'..='9' | 'a'..='z' | 'A'..='Z' => Token::Atom(c),
                _ => Token::Op(c),
            })
            .collect::<Vec<_>>();
        tokens.reverse();
        Lexer { tokens }
    }

    /// Retrieves the next token from the lexer.
    ///
    /// If there are remaining tokens in the lexer, the last token from the
    /// vector is retrieved and removed. If the lexer is empty, the end-of-file
    /// (Eof) token is returned instead.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut lexer = Lexer::new("123 + abc");
    ///
    /// let token = lexer.next();
    /// assert_eq!(token, Token::Atom('c'));
    ///
    /// let token = lexer.next();
    /// assert_eq!(token, Token::Op(' '));
    /// ```
    fn next(&mut self) -> Token {
        self.tokens.pop().unwrap_or(Token::Eof)
    }

    /// Retrieves the next token from the lexer without consuming it.
    ///
    /// If there are remaining tokens in the lexer, the last token from the
    /// vector is retrieved without removing it. If the lexer is empty, the
    /// end-of-file (Eof) token is returned instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use mylexer::{Lexer, Token};
    ///
    /// let mut lexer = Lexer::new("123 + abc");
    ///
    /// let token = lexer.peek();
    /// assert_eq!(token, Token::Atom('c'));
    ///
    /// let token = lexer.peek();
    /// assert_eq!(token, Token::Atom('c'));
    /// ```
    fn peek(&mut self) -> Token {
        self.tokens.last().copied().unwrap_or(Token::Eof)
    }
}

/// Parses and evaluates an expression from the input string.
///
/// This function uses the `Lexer` to tokenize the input string and then
/// calls the `expr_bp` function to perform expression parsing and evaluation.
///
/// # Arguments
///
/// * `input` - The input string representing an expression.
///
/// # Examples
///
/// ```
/// let result = expr("2 + 3 * 4");
/// assert_eq!(result, S::Cons('+', vec![
///     S::Atom('2'),
///     S::Cons('*', vec![
///         S::Atom('3'),
///         S::Atom('4')
///     ])
/// ]));
/// ```
fn expr(input: &str) -> S {
    let mut lexer = Lexer::new(input);
    println!("\n{}", input);

    let e = expr_bp(&mut lexer, 0);
    println!();

    e
}

/// Parses and evaluates an expression with operator precedence using the
/// provided lexer.
///
/// This function recursively parses the expression based on the operator
/// precedence, following the precedence and associativity rules defined in the
/// binding power functions.
///
/// # Arguments
///
/// * `lexer` - A mutable reference to the lexer used for tokenization.
/// * `min_bp` - The minimum binding power of the operators to consider during
/// parsing.
///
/// # Examples
///
/// ```
/// let mut lexer = Lexer::new("2 + 3 * 4");
/// let result = expr_bp(&mut lexer, 0);
/// assert_eq!(result, S::Cons('+', vec![
///     S::Atom('2'),
///     S::Cons('*', vec![
///         S::Atom('3'),
///         S::Atom('4')
///     ])
/// ]));
/// ```
fn expr_bp(lexer: &mut Lexer, min_bp: u8) -> S {
    let mut lhs = match lexer.next() {
        Token::Atom(it) => {
            print!("{} ", it);
            S::Atom(it)
        }
        Token::Op('(') => {
            let lhs = expr_bp(lexer, 0);
            assert_eq!(lexer.next(), Token::Op(')'));
            lhs
        }
        Token::Op(op) => {
            let ((), r_bp) = prefix_binding_power(op);
            let rhs = expr_bp(lexer, r_bp);
            print!("{} ", op);
            S::Cons(op, vec![rhs])
        }
        t => panic!("bad token: {:?}", t),
    };

    loop {
        let op = match lexer.peek() {
            Token::Eof => break,
            Token::Op(op) => op,
            t => panic!("bad token: {:?}", t),
        };

        if let Some((l_bp, ())) = postfix_binding_power(op) {
            if l_bp < min_bp {
                break;
            }
            lexer.next();

            lhs = if op == '[' {
                let rhs = expr_bp(lexer, 0);
                assert_eq!(lexer.next(), Token::Op(']'));
                S::Cons(op, vec![lhs, rhs])
            } else {
                S::Cons(op, vec![lhs])
            };
            continue;
        }

        if let Some((l_bp, r_bp)) = infix_binding_power(op) {
            if l_bp < min_bp {
                break;
            }
            lexer.next();

            lhs = if op == '?' {
                let mhs = expr_bp(lexer, 0);
                assert_eq!(lexer.next(), Token::Op(':'));
                let rhs = expr_bp(lexer, r_bp);
                S::Cons(op, vec![lhs, mhs, rhs])
            } else {
                let rhs = expr_bp(lexer, r_bp);
                S::Cons(op, vec![lhs, rhs])
            };
            continue;
        }

        break;
    }

    lhs
}

/// Determines the prefix binding power and the right binding power for the
/// given operator.
///
/// This function matches the operator character to determine its prefix
/// binding power and the right binding power. It returns a tuple containing the
/// prefix binding power and the right binding power.
///
/// # Arguments
///
/// * `op` - The operator character.
///
/// # Panics
///
/// This function panics if the operator character is not supported.
///
/// # Examples
///
/// ```
/// let (prefix_bp, right_bp) = prefix_binding_power('-');
/// assert_eq!(prefix_bp, ());
/// assert_eq!(right_bp, 9);
/// ```
fn prefix_binding_power(op: char) -> ((), u8) {
    match op {
        '+' | '-' => ((), 9),
        _ => panic!("bad op: {:?}", op),
    }
}

/// Determines the postfix binding power and the left binding power for the
/// given operator.
///
/// This function matches the operator character to determine its postfix
/// binding power and the left binding power. It returns an `Option` containing
/// a tuple with the postfix binding power and the left binding power. If the
/// operator is not supported, `None` is returned.
///
/// # Arguments
///
/// * `op` - The operator character.
///
/// # Returns
///
/// An `Option` containing a tuple with the postfix binding power and the left
/// binding power if the operator is supported, otherwise `None`.
///
/// # Examples
///
/// ```
/// let result = postfix_binding_power('!');
/// assert_eq!(result, Some((11, ())));
///
/// let result = postfix_binding_power('[');
/// assert_eq!(result, Some((11, ())));
///
/// let result = postfix_binding_power('+');
/// assert_eq!(result, None);
/// ```
fn postfix_binding_power(op: char) -> Option<(u8, ())> {
    let res = match op {
        '!' => (11, ()),
        '[' => (11, ()),
        _ => return None,
    };
    Some(res)
}

/// Determines the infix binding power for the given operator.
///
/// # Arguments
///
/// * `op` - The operator character.
///
/// # Returns
///
/// An `Option` containing a tuple with the left binding power and the right
/// binding power if the operator is supported, otherwise `None`.
///
/// # Examples
///
/// ```
/// let result = infix_binding_power('=');
/// assert_eq!(result, Some((2, 1)));
///
/// let result = infix_binding_power('?');
/// assert_eq!(result, Some((4, 3)));
///
/// let result = infix_binding_power('+');
/// assert_eq!(result, Some((5, 6)));
///
/// let result = infix_binding_power('.');
/// assert_eq!(result, Some((14, 13)));
///
/// let result = infix_binding_power('%');
/// assert_eq!(result, None);
/// ```
fn infix_binding_power(op: char) -> Option<(u8, u8)> {
    let res = match op {
        '=' => (2, 1),
        '?' => (4, 3),
        '+' | '-' => (5, 6),
        '*' | '/' => (7, 8),
        '.' => (14, 13),
        _ => return None,
    };
    Some(res)
}

#[test]
fn pratty_tests() {
    let s = expr("1");
    assert_eq!(s.to_string(), "1");

    let s = expr("1 + 2 * 3");
    assert_eq!(s.to_string(), "(+ 1 (* 2 3))");

    let s = expr("a + b * c * d + e");
    assert_eq!(s.to_string(), "(+ (+ a (* (* b c) d)) e)");

    let s = expr("f . g . h");
    assert_eq!(s.to_string(), "(. f (. g h))");

    let s = expr("1 + 2 + f . g . h * 3 * 4");
    assert_eq!(s.to_string(), "(+ (+ 1 2) (* (* (. f (. g h)) 3) 4))");

    let s = expr("--1 * 2");
    assert_eq!(s.to_string(), "(* (- (- 1)) 2)");

    let s = expr("--f . g");
    assert_eq!(s.to_string(), "(- (- (. f g)))");

    let s = expr("-9!");
    assert_eq!(s.to_string(), "(- (! 9))");

    let s = expr("f . g !");
    assert_eq!(s.to_string(), "(! (. f g))");

    let s = expr("(((0)))");
    assert_eq!(s.to_string(), "0");

    let s = expr("x[0][1]");
    assert_eq!(s.to_string(), "([ ([ x 0) 1)");

    let s = expr(
        "a ? b :
         c ? d
         : e",
    );
    assert_eq!(s.to_string(), "(? a b (? c d e))");

    let s = expr("a = 0 ? b : c = d");
    assert_eq!(s.to_string(), "(= a (= (? 0 b c) d))")
}

fn main() {
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();

        if line.is_empty() {
            println!("bye");
            break;
        }

        let s = expr(&line);
        println!("{}", s)
    }
}
