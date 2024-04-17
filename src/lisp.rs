//! Parsing for a Lisp-like front-end.
//!
//! # Grammar
//!
//! The original, reference grammar:
//!
//! ```bnf
//! exp ::=
//!     | -?\d+        { s => Num(s) }
//!     | [^\s\(\)'"]+ { s => Sym(s) }
//!     | "'" exp      { s => Pair(Sym("quote"), Pair(s, Sym("."))) }
//!     | "()"         { _ => Sym(".") }
//!     | "(" exps ")" { vs => vs }
//!
//! exps ::=
//!     | exp exps     { v, vs => Pair(v, vs) }
//!     | ε            { _ => Sym(".") }
//!
//! ws ::=
//!     | (\s|;[^\n]*\n?)+
//! ```
//!
//! In this implementation, unlike the original, `+` sign is allowed for
//! integers, `;` is not allowed in symbols, and spaces are allowed in unit.

use std::rc::Rc;
use std::str;

use winnow::{
    ascii::{dec_int, multispace1, till_line_ending},
    combinator::{alt, cut_err, delimited, opt, preceded, repeat},
    error::{ContextError, ParseError, StrContext},
    prelude::*,
    token::take_while,
};

use crate::base::Val;

pub fn parse(input: &str) -> Result<Rc<Val>, ParseError<&str, ContextError>> {
    delimited(ws0, value, ws0).parse(input)
}

fn value(input: &mut &str) -> PResult<Rc<Val>> {
    alt((
        dec_int.map(Val::num),
        symbol.map(|sym| Val::sym(sym)),
        quote,
        list,
    ))
    .context(StrContext::Label("value"))
    .parse_next(input)
}

fn symbol<'i>(input: &mut &'i str) -> PResult<&'i str> {
    take_while(1.., |ch| {
        ('!'..='~').contains(&ch) && !matches!(ch, '"' | '\'' | '(' | ')' | ';')
    })
    .context(StrContext::Label("symbol"))
    .parse_next(input)
}

fn quote(input: &mut &str) -> PResult<Rc<Val>> {
    preceded(
        ("'", ws0),
        value.map(|v| Val::pair(Val::sym("quote"), Val::pair(v, Val::sym(".")))),
    )
    .context(StrContext::Label("quote"))
    .parse_next(input)
}

fn list(input: &mut &str) -> PResult<Rc<Val>> {
    delimited(
        '(',
        preceded(ws0, alt((list_elements, unit))),
        cut_err(preceded(ws0, ')')),
    )
    .context(StrContext::Label("list"))
    .parse_next(input)
}

fn list_elements(input: &mut &str) -> PResult<Rc<Val>> {
    let mut acc = value.parse_next(input)?;
    while let Some(v) = opt(preceded(ws1, value)).parse_next(input)? {
        acc = Val::pair(acc, v)
    }
    Ok(acc)
}

fn unit(input: &mut &str) -> PResult<Rc<Val>> {
    ().map(|_| Val::sym(".")).parse_next(input)
}

fn ws0(input: &mut &str) -> PResult<()> {
    repeat(0.., ws).parse_next(input)
}

fn ws1(input: &mut &str) -> PResult<()> {
    repeat(1.., ws).parse_next(input)
}

fn ws(input: &mut &str) -> PResult<()> {
    alt((multispace1.void(), (';', till_line_ending).void())).parse_next(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_example() {
        let code = "
            (let code (trans '(lambda _ x (+ x 42)))
              ; hello
              code)
        ";
        let parsed = Val::pair(
            Val::sym("let"),
            Val::pair(
                Val::sym("code"),
                Val::pair(
                    Val::pair(
                        Val::sym("trans"),
                        Val::pair(
                            Val::pair(
                                Val::sym("quote"),
                                Val::pair(
                                    Val::pair(
                                        Val::sym("lambda"),
                                        Val::pair(
                                            Val::sym("_"),
                                            Val::pair(
                                                Val::sym("x"),
                                                Val::pair(
                                                    Val::pair(
                                                        Val::sym("+"),
                                                        Val::pair(
                                                            Val::sym("x"),
                                                            Val::pair(Val::num(42), Val::sym(".")),
                                                        ),
                                                    ),
                                                    Val::sym("."),
                                                ),
                                            ),
                                        ),
                                    ),
                                    Val::sym("."),
                                ),
                            ),
                            Val::sym("."),
                        ),
                    ),
                    Val::pair(Val::sym("code"), Val::sym(".")),
                ),
            ),
        );
        assert_eq!(parse(code), Ok(parsed));
    }
}
