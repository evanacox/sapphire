//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use std::iter::Peekable;
use std::str::Chars;
use unicode_segmentation::{UWordBoundIndices, UnicodeSegmentation};

/// An instruction opcode, e.g. the `iadd` in `iadd i32 %0, %1`.
#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Opcode {
    /// `call`
    Call,
    /// `indirectcall`
    IndirectCall,
    /// `fcmp`
    FCmp,
    /// `icmp`
    ICmp,
    /// `sel`
    Sel,
    /// `br`
    Br,
    /// `condbr`
    CondBr,
    /// `unreachable`
    Unreachable,
    /// `ret`
    Ret,
    /// `and`
    And,
    /// `or`
    Or,
    /// `xor`
    Xor,
    /// `shl`
    Shl,
    /// `ashr`
    AShr,
    /// `lshr`
    LShr,
    /// `iadd`
    IAdd,
    /// `isub`
    ISub,
    /// `imul`
    IMul,
    /// `sdiv`
    SDiv,
    /// `udiv`
    UDiv,
    /// `srem`
    SRem,
    /// `urem`
    URem,
    /// `fneg`
    FNeg,
    /// `fadd`
    FAdd,
    /// `fsub`
    FSub,
    /// `fmul`
    FMul,
    /// `fdiv`
    FDiv,
    /// `frem`
    FRem,
    /// `alloca`
    Alloca,
    /// `load`
    Load,
    /// `store`
    Store,
    /// `offset`
    Offset,
    /// `extract`
    Extract,
    /// `insert`
    Insert,
    /// `elemptr`
    ElemPtr,
    /// `sext`
    Sext,
    /// `zext`
    Zext,
    /// `trunc`
    Trunc,
    /// `itob`
    IToB,
    /// `btoi`
    BToI,
    /// `sitof`
    SIToF,
    /// `uitof`
    UIToF,
    /// `ftosi`
    FToSI,
    /// `ftoui`
    FToUI,
    /// `fext`
    FExt,
    /// `ftrunc`
    FTrunc,
    /// `itop`
    IToP,
    /// `ptoi`
    PToI,
    /// `iconst`
    IConst,
    /// `fconst`
    FConst,
    /// `bconst`
    BConst,
    /// `null`
    Null,
    /// `undef`
    Undef,
    /// `stackslot`
    StackSlot,
    /// `globaladdr`
    GlobalAddr,
}

/// The comparison performed by a given `icmp` or `fcmp` instruction.
/// They are in the same lex type because there is overlap between them.
#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum CompareOpcode {
    /// `eq`
    Eq,
    /// `ne`
    Ne,
    /// `ugt`
    Ugt,
    /// `ult`
    Ult,
    /// `uge`
    Uge,
    /// `ule`
    Ule,
    /// `sgt`
    Sgt,
    /// `slt`
    Slt,
    /// `sge`
    Sge,
    /// `sle`
    Sle,
    /// `ord`
    Ord,
    /// `uno`
    Uno,
    /// `ueq`
    Ueq,
    /// `une`
    Une,
    /// `oeq`
    Oeq,
    /// `one`
    One,
    /// `ogt`
    Ogt,
    /// `olt`
    Olt,
    /// `oge`
    Oge,
    /// `ole`
    Ole,
}

/// Different types of (unparsed) integer literals
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum IntLiteral<'a> {
    /// A hex literal, e.g. `0xdeadbeef` or `0xDEADBEEF`
    Hex(&'a str),
    /// A binary literal, e.g. `0b1010`
    Binary(&'a str),
    /// An octal literal, e.g. `0o715`
    Octal(&'a str),
    /// A decimal literal, e.g. `-1` or `42`
    Decimal(&'a str),
}

/// Different types of (unparsed) floating-point literals
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum FloatLiteral<'a> {
    /// Standard float notation, e.g. `3.141592`
    Standard(&'a str),
    /// C-style scientific notation, e.g. `0.3e9`, `1.0e-9`
    Scientific(&'a str),
    /// A way of representing raw byte values for floating-point values,
    /// e.g. `0xfpFFFFFFFFFFFFFFFF`.
    Raw(&'a str),
    /// `NaN`
    NaN,
}

/// A single lex token
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Token<'a> {
    /// A local identifier, `%ident`
    LocalIdent(&'a str),
    /// A stack identifier, `$ident`
    StackIdent(&'a str),
    /// A global identifier, `@ident`
    GlobalIdent(&'a str),
    /// A label identifier, `ident`
    LabelIdent(&'a str),
    /// `bool`
    Bool,
    /// `ptr`
    Ptr,
    /// `i8`
    I8,
    /// `i16`
    I16,
    /// `i32`
    I32,
    /// `i64`
    I64,
    /// `f32`
    F32,
    /// `f64`
    F64,
    /// `void`
    Void,
    /// `...`
    Variadic,
    /// `fn`
    Fn,
    /// `{`
    CurlyOpen,
    /// `}`
    CurlyClose,
    /// `(`
    ParenOpen,
    /// `)`
    ParenClose,
    /// `=`
    Eq,
    /// `:`
    Colon,
    /// `,`
    Comma,
    /// An instruction opcode
    Opcode(Opcode),
    /// An opcode for `icmp` or `fcmp`
    CmpOpcode(CompareOpcode),
    /// An integer literal
    /// A hex literal, e.g. `0xdeadbeef` or `0xDEADBEEF`
    IntLitHex(&'a str),
    /// A binary literal, e.g. `0b1010`
    IntLitBinary(&'a str),
    /// An octal literal, e.g. `0o715`
    IntLitOctal(&'a str),
    /// A decimal literal, e.g. `-1` or `42`
    IntLitDecimal(&'a str),
    /// A floating-point literal
    /// Standard float notation, e.g. `3.141592`
    FloatLitStandard(&'a str),
    /// C-style scientific notation, e.g. `0.3e9`, `1.0e-9`
    FloatLitScientific(&'a str),
    /// A way of representing raw byte values for floating-point values,
    /// e.g. `0xfpFFFFFFFFFFFFFFFF`.
    FloatLitRaw(&'a str),
    /// `NaN`
    FloatLitNaN,
    /// A `bool` literal
    BoolLit(bool),
    /// An unknown token, almost certainly an error
    Unknown(&'a str),
}

static_assertions::assert_eq_size!(Token<'static>, [usize; 3]);

/// A token yielded by the lexer, containing line/col information as well
/// as raw token data.
pub struct TokPair<'a> {
    /// The raw token data
    pub tok: Token<'a>,
    /// The line in the original source that the token is located at
    pub line: u32,
    /// The column in the original source that the token is located at
    pub col: u32,
}

static_assertions::assert_eq_size!(TokPair<'static>, [usize; 4]);

/// A lexer that lazily produces tokens.
pub struct Lex<'a> {
    source: &'a str,
    words: Peekable<UWordBoundIndices<'a>>,
    line: usize,
    col: usize,
}

impl<'a> Lex<'a> {
    /// Creates a new [`Lex`] based on a given source file.
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            words: source.split_word_bound_indices().peekable(),
            line: 1,
            col: 1,
        }
    }

    /// Produces the next token, if one exists. If `None` is returned,
    /// EOF has been reached.
    pub fn next(&mut self) -> Option<TokPair<'a>> {
        let (index, string) = self.take_next_word()?;
        let tok = match string {
            "%" => {
                let (index, tok) = self.take_next_word()?;

                Token::LocalIdent(self.try_lex_ident(tok, tok.chars(), index))
            }
            "$" => {
                let (index, tok) = self.take_next_word()?;

                Token::StackIdent(self.try_lex_ident(tok, tok.chars(), index))
            }
            "@" => {
                let (index, tok) = self.take_next_word()?;

                Token::GlobalIdent(self.try_lex_ident(tok, tok.chars(), index))
            }
            "bool" => Token::Bool,
            "ptr" => Token::Ptr,
            "i8" => Token::I8,
            "i16" => Token::I16,
            "i32" => Token::I32,
            "i64" => Token::I64,
            "f32" => Token::F32,
            "f64" => Token::F64,
            "void" => Token::Void,
            "..." => Token::Variadic,
            "fn" => Token::Fn,
            "{" => Token::CurlyOpen,
            "}" => Token::CurlyClose,
            "(" => Token::ParenOpen,
            ")" => Token::ParenClose,
            "=" => Token::Eq,
            ":" => Token::Colon,
            "," => Token::Comma,
            "call" => Token::Opcode(Opcode::Call),
            "indirectcall" => Token::Opcode(Opcode::IndirectCall),
            "fcmp" => Token::Opcode(Opcode::FCmp),
            "icmp" => Token::Opcode(Opcode::ICmp),
            "sel" => Token::Opcode(Opcode::Sel),
            "br" => Token::Opcode(Opcode::Br),
            "condbr" => Token::Opcode(Opcode::CondBr),
            "unreachable" => Token::Opcode(Opcode::Unreachable),
            "ret" => Token::Opcode(Opcode::Ret),
            "and" => Token::Opcode(Opcode::And),
            "or" => Token::Opcode(Opcode::Or),
            "xor" => Token::Opcode(Opcode::Xor),
            "shl" => Token::Opcode(Opcode::Shl),
            "ashr" => Token::Opcode(Opcode::AShr),
            "lshr" => Token::Opcode(Opcode::LShr),
            "iadd" => Token::Opcode(Opcode::IAdd),
            "isub" => Token::Opcode(Opcode::ISub),
            "imul" => Token::Opcode(Opcode::IMul),
            "sdiv" => Token::Opcode(Opcode::SDiv),
            "udiv" => Token::Opcode(Opcode::UDiv),
            "srem" => Token::Opcode(Opcode::SRem),
            "urem" => Token::Opcode(Opcode::URem),
            "fneg" => Token::Opcode(Opcode::FNeg),
            "fadd" => Token::Opcode(Opcode::FAdd),
            "fsub" => Token::Opcode(Opcode::FSub),
            "fmul" => Token::Opcode(Opcode::FMul),
            "fdiv" => Token::Opcode(Opcode::FDiv),
            "frem" => Token::Opcode(Opcode::FRem),
            "alloca" => Token::Opcode(Opcode::Alloca),
            "load" => Token::Opcode(Opcode::Load),
            "store" => Token::Opcode(Opcode::Store),
            "offset" => Token::Opcode(Opcode::Offset),
            "extract" => Token::Opcode(Opcode::Extract),
            "insert" => Token::Opcode(Opcode::Insert),
            "elemPtr" => Token::Opcode(Opcode::ElemPtr),
            "sext" => Token::Opcode(Opcode::Sext),
            "zext" => Token::Opcode(Opcode::Zext),
            "trunc" => Token::Opcode(Opcode::Trunc),
            "itob" => Token::Opcode(Opcode::IToB),
            "btoi" => Token::Opcode(Opcode::BToI),
            "sitof" => Token::Opcode(Opcode::SIToF),
            "uitof" => Token::Opcode(Opcode::UIToF),
            "ftosi" => Token::Opcode(Opcode::FToSI),
            "ftoui" => Token::Opcode(Opcode::FToUI),
            "fext" => Token::Opcode(Opcode::FExt),
            "ftrunc" => Token::Opcode(Opcode::FTrunc),
            "itop" => Token::Opcode(Opcode::IToP),
            "ptoi" => Token::Opcode(Opcode::PToI),
            "iconst" => Token::Opcode(Opcode::IConst),
            "fconst" => Token::Opcode(Opcode::FConst),
            "bconst" => Token::Opcode(Opcode::BConst),
            "null" => Token::Opcode(Opcode::Null),
            "undef" => Token::Opcode(Opcode::Undef),
            "stackslot" => Token::Opcode(Opcode::StackSlot),
            "globaladdr" => Token::Opcode(Opcode::GlobalAddr),
            "eq" => Token::CmpOpcode(CompareOpcode::Eq),
            "ne" => Token::CmpOpcode(CompareOpcode::Ne),
            "ugt" => Token::CmpOpcode(CompareOpcode::Ugt),
            "ult" => Token::CmpOpcode(CompareOpcode::Ult),
            "uge" => Token::CmpOpcode(CompareOpcode::Uge),
            "ule" => Token::CmpOpcode(CompareOpcode::Ule),
            "sgt" => Token::CmpOpcode(CompareOpcode::Sgt),
            "slt" => Token::CmpOpcode(CompareOpcode::Slt),
            "sge" => Token::CmpOpcode(CompareOpcode::Sge),
            "sle" => Token::CmpOpcode(CompareOpcode::Sle),
            "ord" => Token::CmpOpcode(CompareOpcode::Ord),
            "uno" => Token::CmpOpcode(CompareOpcode::Uno),
            "ueq" => Token::CmpOpcode(CompareOpcode::Ueq),
            "une" => Token::CmpOpcode(CompareOpcode::Une),
            "oeq" => Token::CmpOpcode(CompareOpcode::Oeq),
            "one" => Token::CmpOpcode(CompareOpcode::One),
            "ogt" => Token::CmpOpcode(CompareOpcode::Ogt),
            "olt" => Token::CmpOpcode(CompareOpcode::Olt),
            "oge" => Token::CmpOpcode(CompareOpcode::Oge),
            "ole" => Token::CmpOpcode(CompareOpcode::Ole),
            "true" => Token::BoolLit(true),
            "false" => Token::BoolLit(false),
            "NaN" => Token::FloatLitNaN,
            x => self.try_lex_unknown(x, index),
        };

        Some(TokPair {
            tok,
            line: self.line as u32,
            col: self.col as u32,
        })
    }

    fn try_lex_unknown(&mut self, tok: &'a str, index: usize) -> Token<'a> {
        if !tok.is_ascii() || tok.is_empty() {
            return Token::Unknown(tok);
        }

        let mut chs = tok.chars();

        match chs.next().expect("just checked if empty") {
            '0' => self.try_lex_formatted_lit(tok, chs),
            c if c.is_ascii_alphabetic() => Token::LabelIdent(self.try_lex_ident(tok, chs, index)),
            d if d.is_ascii_digit() || d == '-' => self.try_lex_int_or_float_lit(tok, chs, index),
            _ => Token::Unknown(tok),
        }
    }

    fn try_lex_formatted_lit(&self, tok: &'a str, chars: Chars<'a>) -> Token<'a> {
        if tok.starts_with("0x") {
            if chars
                .skip(2)
                .any(|c| !(c.is_ascii_digit() || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')))
            {
                Token::Unknown(tok)
            } else if tok.starts_with("0xfp") {
                Token::FloatLitRaw(tok)
            } else {
                Token::IntLitHex(tok)
            }
        } else if tok.starts_with("0o") {
            if chars.skip(2).any(|c| !('0' <= c && c <= '7')) {
                Token::Unknown(tok)
            } else {
                Token::IntLitOctal(tok)
            }
        } else if tok.starts_with("0b") {
            if chars.skip(2).any(|c| c != '0' && c != '1') {
                Token::Unknown(tok)
            } else {
                Token::IntLitBinary(tok)
            }
        } else {
            // we don't support `0123`, only `123`
            Token::Unknown(tok)
        }
    }

    fn try_lex_ident(&mut self, tok: &'a str, chars: Chars<'a>, begin_at: usize) -> &'a str {
        // weird case for something like `builtin.x86_64.nop`, it will split that
        // into "builtin.x86_64", ".", "nop". it does this when there's a digit then a `.`
        match chars.last() {
            // we don't want to start the loop unless we need to
            Some(last) if last.is_ascii_digit() => {
                let mut end_at = begin_at + tok.len();
                let mut need_continue = true;

                'outer: while need_continue {
                    // if the next token is a "." or an alphanumeric/dot/underscore identifier,
                    // keep parsing until we hit the end.
                    //
                    //
                    let (index, included_tok) = match self.words.peek() {
                        Some((_, ".")) => {
                            // need_continue is maintained, if prev piece needed a continue
                            // and we hit a dot we still need to continue
                            self.words.next().unwrap()
                        }
                        Some((_, s)) => {
                            // this will get eaten later
                            if !s.is_ascii() {
                                break 'outer;
                            }

                            let mut last = char::default();

                            for ch in s.chars() {
                                last = ch;

                                if !(ch.is_ascii_alphanumeric() || ch == '.' || ch == '_') {
                                    break 'outer;
                                }
                            }

                            // need_continue is dependent on whether or not `last` is a digit, just
                            // like when we first started the loop
                            need_continue = last.is_ascii_digit();

                            self.words.next().unwrap()
                        }
                        _ => break,
                    };

                    end_at = index + included_tok.len();
                }

                &self.source[begin_at..end_at]
            }
            _ => tok,
        }
    }

    fn try_lex_int_or_float_lit(
        &mut self,
        tok: &'a str,
        mut chars: Chars<'a>,
        begins_at: usize,
    ) -> Token<'a> {
        if tok.contains('e') {
            // the unicode word splitter doesn't split some scientific notation
            // correctly, so we'd have to do special handling here.
            //
            // e.g. "1.0e-9" is split as "1.0e", "-", "9"
            panic!("scientific notation not implemented")
        }

        if !chars.all(|c| c.is_ascii_digit() || c == '.') {
            return Token::Unknown(tok);
        }

        // negatives require us to take the rest manually
        if tok == "-" {
            // ensure we never recurse more than once
            let &(index, next) = match self.words.peek() {
                Some((_, "-")) | None => return Token::Unknown(tok),
                Some(s) => s,
            };

            let full = &self.source[begins_at..(index + next.len())];

            // we go ahead and do the parsing logic on the next, it determines the
            // result for full too (since full is just the inner + a negative sign)
            match self.try_lex_int_or_float_lit(next, next.chars(), index) {
                Token::FloatLitStandard(_) => {
                    self.words.next(); // consume the token we already pre-lexed

                    Token::FloatLitStandard(full)
                }
                Token::IntLitDecimal(_) => {
                    self.words.next(); // consume the token we already pre-lexed

                    Token::IntLitDecimal(full)
                }
                Token::Unknown(_) => Token::Unknown(tok),
                _ => unreachable!(),
            }
        } else if tok.contains('.') {
            Token::FloatLitStandard(tok)
        } else {
            Token::IntLitDecimal(tok)
        }
    }

    fn take_next_word(&mut self) -> Option<(usize, &'a str)> {
        // if we have any 'words', try to take the next. we also try to skip any
        // whitespace and comments while we do that, they are ignored at lex time.
        while let Some((index, string)) = self.words.next() {
            let trimmed = string.trim();

            // if we hit whitespace, skip it and try to take next token
            if trimmed.is_empty() {
                continue;
            }

            // if we get the beginning of a comment, skip until newline or EOF and try to loop again
            if trimmed == ";" {
                // this covers both LF and CRLF
                while self.words.peek().is_some_and(|&(_, s)| !s.contains("\n")) {
                    self.words.next();
                }

                // consume the newline, if it exists. if we're already at the end,
                // this doesn't actually do anything
                self.words.next();

                continue;
            }

            return Some((index, trimmed));
        }

        // we hit EOF inside the loop
        return None;
    }
}
