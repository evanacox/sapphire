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
use std::str::Bytes;

/// A lexer for SIR that lazily produces tokens.
pub struct Lex<'a> {
    raw: RawLex<'a>,
    next: Option<TokPair<'a>>,
}

impl<'a> Lex<'a> {
    /// Creates a new [`Lex`] based on a given source file.
    pub fn new(source: &'a str) -> Self {
        let mut raw = RawLex::new(source);
        let first = raw.next();

        Self { raw, next: first }
    }

    /// Produces the next token, if one exists. If `None` is returned,
    /// EOF has been reached.
    pub fn next_token(&mut self) -> Option<TokPair<'a>> {
        // instead of just directly returning the yielded token, we stay "one ahead"
        // this allows us to implement `is_at_end` in a way that doesn't need `&mut self`
        // and makes `peek` trivial
        let old = self.next.take();

        self.next = self.raw.next();

        old
    }

    /// Returns whether or not the lexer is able to yield more tokens via [`Self::next_token`]
    pub fn is_at_end(&self) -> bool {
        self.next.is_none()
    }

    /// Peek at the next token to be yielded, if there are any
    pub fn peek_token(&self) -> Option<TokPair<'a>> {
        self.next
    }
}

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
    /// `[`
    SquareOpen,
    /// `]`
    SquareClose,
    /// `=`
    Eq,
    /// `:`
    Colon,
    /// `x`
    X,
    /// `,`
    Comma,
    /// `byval`
    ByVal,
    /// `noalias`
    NoAlias,
    /// `nonnull`
    NonNull,
    /// `ccc`
    CCC,
    /// `sysv`
    SysV,
    /// `win64`
    Win64,
    /// `volatile`
    Volatile,
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
    /// `stack`
    Stack,
    /// An unknown token, almost certainly an error
    Unknown(&'a str),
}

impl<'a> Token<'a> {
    /// If `self` is one of the integer literals, returns it in
    /// a nicer-to-work-with form.
    ///
    /// Unfortunately [`Token`] has to work like this to fit in 24 bytes,
    /// if it just held [`IntLiteral`] in the variants it would be 32.
    #[inline]
    pub fn as_int_lit(self) -> Option<IntLiteral<'a>> {
        match self {
            Self::IntLitHex(s) => Some(IntLiteral::Hex(s)),
            Self::IntLitOctal(s) => Some(IntLiteral::Octal(s)),
            Self::IntLitBinary(s) => Some(IntLiteral::Binary(s)),
            Self::IntLitDecimal(s) => Some(IntLiteral::Decimal(s)),
            _ => None,
        }
    }

    /// If `self` is one of the float literals, returns it in
    /// a nicer-to-work-with form.
    ///
    /// Unfortunately [`Token`] has to work like this to fit in 24 bytes,
    /// if it just held [`FloatLiteral`] in the variants it would be 32.
    #[inline]
    pub fn as_float_lit(self) -> Option<FloatLiteral<'a>> {
        match self {
            Self::FloatLitRaw(s) => Some(FloatLiteral::Raw(s)),
            Self::FloatLitStandard(s) => Some(FloatLiteral::Standard(s)),
            Self::FloatLitScientific(s) => Some(FloatLiteral::Scientific(s)),
            Self::FloatLitNaN => Some(FloatLiteral::NaN),
            _ => None,
        }
    }
}

static_assertions::assert_eq_size!(Token<'static>, [usize; 3]);

/// A token yielded by the lexer, containing line/col information as well
/// as raw token data.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct TokPair<'a> {
    /// The raw token data
    pub tok: Token<'a>,
    /// The line in the original source that the token is located at
    pub line: u32,
    /// The column in the original source that the token is located at
    pub col: u16,
    /// The total length of the token
    pub len: u16,
}

static_assertions::assert_eq_size!(TokPair<'static>, [usize; 4]);

// implements lexicographic string comparisons at compile time
//
// this is equivalent to `Ord<str, str>`, just written in a way that
// is actually usable inside `const` functions
const fn less_than(left: &'static str, right: &'static str) -> bool {
    let left = left.as_bytes();
    let right = right.as_bytes();
    let mut i = 0;
    let min_length = if left.len() > right.len() {
        right.len()
    } else {
        left.len()
    };

    while i < min_length {
        if left[i] != right[i] {
            return left[i] < right[i];
        }

        i += 1;
    }

    left.len() < right.len()
}

// insertion sort for our lex pairs at compile time, this is used to sort
// our pairs array to enable binary-searching while lexing
const fn sort_array<const N: usize>(
    mut arr: [(&'static str, Token<'static>); N],
) -> [(&'static str, Token<'static>); N] {
    let mut i = 1;

    while i < N {
        let mut j = i;

        while j > 0 && !less_than(arr[j - 1].0, arr[j].0) {
            let tmp = arr[j - 1];
            arr[j - 1] = arr[j];
            arr[j] = tmp;
            j -= 1;
        }

        i += 1;
    }

    arr
}

// this is our mapping in an unsorted (and easy to modify) format
// we do a sort at compile time, and assign the result to `SORTED_IDENT_TOKENS`
const IDENT_TOKENS: [(&str, Token<'static>); 97] = [
    ("bool", Token::Bool),
    ("ptr", Token::Ptr),
    ("i8", Token::I8),
    ("i16", Token::I16),
    ("i32", Token::I32),
    ("i64", Token::I64),
    ("f32", Token::F32),
    ("f64", Token::F64),
    ("fn", Token::Fn),
    ("void", Token::Void),
    ("call", Token::Opcode(Opcode::Call)),
    ("indirectcall", Token::Opcode(Opcode::IndirectCall)),
    ("fcmp", Token::Opcode(Opcode::FCmp)),
    ("icmp", Token::Opcode(Opcode::ICmp)),
    ("sel", Token::Opcode(Opcode::Sel)),
    ("br", Token::Opcode(Opcode::Br)),
    ("condbr", Token::Opcode(Opcode::CondBr)),
    ("unreachable", Token::Opcode(Opcode::Unreachable)),
    ("ret", Token::Opcode(Opcode::Ret)),
    ("and", Token::Opcode(Opcode::And)),
    ("or", Token::Opcode(Opcode::Or)),
    ("xor", Token::Opcode(Opcode::Xor)),
    ("shl", Token::Opcode(Opcode::Shl)),
    ("ashr", Token::Opcode(Opcode::AShr)),
    ("lshr", Token::Opcode(Opcode::LShr)),
    ("iadd", Token::Opcode(Opcode::IAdd)),
    ("isub", Token::Opcode(Opcode::ISub)),
    ("imul", Token::Opcode(Opcode::IMul)),
    ("sdiv", Token::Opcode(Opcode::SDiv)),
    ("udiv", Token::Opcode(Opcode::UDiv)),
    ("srem", Token::Opcode(Opcode::SRem)),
    ("urem", Token::Opcode(Opcode::URem)),
    ("fneg", Token::Opcode(Opcode::FNeg)),
    ("fadd", Token::Opcode(Opcode::FAdd)),
    ("fsub", Token::Opcode(Opcode::FSub)),
    ("fmul", Token::Opcode(Opcode::FMul)),
    ("fdiv", Token::Opcode(Opcode::FDiv)),
    ("frem", Token::Opcode(Opcode::FRem)),
    ("alloca", Token::Opcode(Opcode::Alloca)),
    ("load", Token::Opcode(Opcode::Load)),
    ("store", Token::Opcode(Opcode::Store)),
    ("offset", Token::Opcode(Opcode::Offset)),
    ("extract", Token::Opcode(Opcode::Extract)),
    ("insert", Token::Opcode(Opcode::Insert)),
    ("elemptr", Token::Opcode(Opcode::ElemPtr)),
    ("sext", Token::Opcode(Opcode::Sext)),
    ("zext", Token::Opcode(Opcode::Zext)),
    ("trunc", Token::Opcode(Opcode::Trunc)),
    ("itob", Token::Opcode(Opcode::IToB)),
    ("btoi", Token::Opcode(Opcode::BToI)),
    ("sitof", Token::Opcode(Opcode::SIToF)),
    ("uitof", Token::Opcode(Opcode::UIToF)),
    ("ftosi", Token::Opcode(Opcode::FToSI)),
    ("ftoui", Token::Opcode(Opcode::FToUI)),
    ("fext", Token::Opcode(Opcode::FExt)),
    ("ftrunc", Token::Opcode(Opcode::FTrunc)),
    ("itop", Token::Opcode(Opcode::IToP)),
    ("ptoi", Token::Opcode(Opcode::PToI)),
    ("iconst", Token::Opcode(Opcode::IConst)),
    ("fconst", Token::Opcode(Opcode::FConst)),
    ("bconst", Token::Opcode(Opcode::BConst)),
    ("null", Token::Opcode(Opcode::Null)),
    ("undef", Token::Opcode(Opcode::Undef)),
    ("stackslot", Token::Opcode(Opcode::StackSlot)),
    ("globaladdr", Token::Opcode(Opcode::GlobalAddr)),
    ("eq", Token::CmpOpcode(CompareOpcode::Eq)),
    ("ne", Token::CmpOpcode(CompareOpcode::Ne)),
    ("ugt", Token::CmpOpcode(CompareOpcode::Ugt)),
    ("ult", Token::CmpOpcode(CompareOpcode::Ult)),
    ("uge", Token::CmpOpcode(CompareOpcode::Uge)),
    ("ule", Token::CmpOpcode(CompareOpcode::Ule)),
    ("sgt", Token::CmpOpcode(CompareOpcode::Sgt)),
    ("slt", Token::CmpOpcode(CompareOpcode::Slt)),
    ("sge", Token::CmpOpcode(CompareOpcode::Sge)),
    ("sle", Token::CmpOpcode(CompareOpcode::Sle)),
    ("ord", Token::CmpOpcode(CompareOpcode::Ord)),
    ("uno", Token::CmpOpcode(CompareOpcode::Uno)),
    ("ueq", Token::CmpOpcode(CompareOpcode::Ueq)),
    ("une", Token::CmpOpcode(CompareOpcode::Une)),
    ("oeq", Token::CmpOpcode(CompareOpcode::Oeq)),
    ("one", Token::CmpOpcode(CompareOpcode::One)),
    ("ogt", Token::CmpOpcode(CompareOpcode::Ogt)),
    ("olt", Token::CmpOpcode(CompareOpcode::Olt)),
    ("oge", Token::CmpOpcode(CompareOpcode::Oge)),
    ("ole", Token::CmpOpcode(CompareOpcode::Ole)),
    ("true", Token::BoolLit(true)),
    ("false", Token::BoolLit(false)),
    ("NaN", Token::FloatLitNaN),
    ("byval", Token::ByVal),
    ("noalias", Token::NoAlias),
    ("nonnull", Token::NonNull),
    ("ccc", Token::CCC),
    ("sysv", Token::SysV),
    ("win64", Token::Win64),
    ("volatile", Token::Volatile),
    ("x", Token::X),
    ("stack", Token::Stack),
];

const SORTED_IDENT_TOKENS: [(&str, Token<'static>); 97] = sort_array(IDENT_TOKENS);

struct RawLex<'a> {
    source: &'a str,
    chars: Peekable<Bytes<'a>>,
    current: usize,
    last: usize,
    line: usize,
    col: usize,
}

impl<'a> RawLex<'a> {
    /// Creates a new [`Lex`] based on a given source file.
    fn new(source: &'a str) -> Self {
        Self {
            source,
            current: 0,
            last: 0,
            line: 1,
            col: 1,
            chars: source.bytes().peekable(),
        }
    }

    /// Produces the next token, if one exists. If `None` is returned,
    /// EOF has been reached.
    fn next(&mut self) -> Option<TokPair<'a>> {
        let ch = self.take_next()?;
        let start = self.current - 1;
        let col = self.col;
        let line = self.line;

        let tok = match ch {
            '%' => match self.try_lex_ident_without_first() {
                Some(ident) => Token::LocalIdent(ident),
                None => Token::Unknown(self.last_consumed_as_str()),
            },
            '$' => match self.try_lex_ident_without_first() {
                Some(ident) => Token::StackIdent(ident),
                None => Token::Unknown(self.last_consumed_as_str()),
            },
            '@' => match self.try_lex_ident_without_first() {
                Some(ident) => Token::GlobalIdent(ident),
                None => Token::Unknown(self.last_consumed_as_str()),
            },
            '{' => Token::CurlyOpen,
            '}' => Token::CurlyClose,
            '(' => Token::ParenOpen,
            ')' => Token::ParenClose,
            '[' => Token::SquareOpen,
            ']' => Token::SquareClose,
            ':' => Token::Colon,
            ',' => Token::Comma,
            '=' => Token::Eq,
            '.' => self.try_lex_variadic(),
            '0' => self.try_lex_prefixed_literal(),
            '-' => self.try_lex_decimal(),
            c if c.is_ascii_digit() => self.try_lex_decimal(),
            c if c.is_ascii_alphabetic() || c == '_' => self.try_lex_ident_with_first(),
            c => Token::Unknown(self.last_consumed_as_str()),
        };

        Some(TokPair {
            tok,
            line: line as u32,
            col: col as u16,
            len: (self.current - start) as u16,
        })
    }

    // used to directly lex identifiers from a starting index onwards, implementation
    // of the main two lex identifier methods
    fn lex_ident_raw(&mut self, start: usize) -> &'a str {
        while let Some(c) = self.peek_next() {
            if !(c.is_ascii_alphanumeric() || c == '.' || c == '_') {
                break;
            }

            self.consume_next();
        }

        &self.source[start..self.current]
    }

    // lexes an identifier where the first character hasn't been consumed yet. If no
    // identifier-compatible characters are lexed, this returns `None`
    //
    // this is only used for prefixed identifiers like `@foo` or `$bar`
    fn try_lex_ident_without_first(&mut self) -> Option<&'a str> {
        let full = self.lex_ident_raw(self.current);

        (!full.is_empty()).then_some(full)
    }

    // lexes an identifier where the first character has been consumed
    fn try_lex_ident_with_first(&mut self) -> Token<'a> {
        let full = self.lex_ident_raw(self.current - 1);

        // we binary-search the array we sorted at compile time, and use that as our fast
        // lookup for "is this identifier actually a keyword?"
        if let Ok(idx) = SORTED_IDENT_TOKENS.binary_search_by_key(&full, |(s, _)| *s) {
            SORTED_IDENT_TOKENS[idx].1
        } else {
            Token::LabelIdent(full)
        }
    }

    // lexes decimal numbers where the first character has already been consumed
    //
    // supports an optional `-` sign and optional fractional part
    fn try_lex_decimal(&mut self) -> Token<'a> {
        let start = self.current - 1;

        // eat while c is a digit or `.`
        while let Some(c) = self.peek_next() {
            if !(c.is_ascii_digit() || c == '.') {
                break;
            }

            self.consume_next();
        }

        let full = &self.source[start..self.current];

        if full.contains('.') {
            Token::FloatLitStandard(full)
        } else {
            Token::IntLitDecimal(full)
        }
    }

    // lexes `...` where the first `.` has already been consumed
    fn try_lex_variadic(&mut self) -> Token<'a> {
        let start = self.current - 1;

        // try to lex 2 more `.`s, if we fail we mark all the ones we
        // consumed as an unknown token. if we succeed, we break out of the loop
        for _ in 0..2 {
            if let Some('.') = self.peek_next() {
                self.consume_next();
            } else {
                return Token::Unknown(&self.source[start..self.current]);
            }
        }

        Token::Variadic
    }

    // lexes integer literals that start with 0{letters}, where the `0` has already been consumed
    //
    // e.g. `0xdeadbeef`, `0b101`, `0xfpFFFFFFFF`
    fn try_lex_prefixed_literal(&mut self) -> Token<'a> {
        let start = self.current - 1;
        let next = match self.peek_next() {
            Some(ch) => ch,
            None => return Token::IntLitDecimal(&self.source[start..(start + 1)]),
        };

        match next {
            'x' => {
                self.consume_next();
                self.consume_while(|c| {
                    c.is_ascii_digit() || ('a'..='f').contains(&c) || ('A'..='F').contains(&c)
                });

                Token::IntLitHex(&self.source[start..self.current])
            }
            'o' => {
                self.consume_next();
                self.consume_while(|c| ('0'..='7').contains(&c));

                Token::IntLitOctal(&self.source[start..self.current])
            }
            'b' => {
                self.consume_next();
                self.consume_while(|c| c == '0' || c == '1');

                Token::IntLitBinary(&self.source[start..self.current])
            }
            'f' => {
                self.consume_next();
                self.consume_while(|c| {
                    c.is_ascii_digit() || ('a'..='f').contains(&c) || ('A'..='F').contains(&c)
                });

                Token::FloatLitRaw(&self.source[start..self.current])
            }
            _ => Token::IntLitDecimal(&self.source[start..self.current]),
        }
    }

    fn take_next(&mut self) -> Option<char> {
        // if we have any 'words', try to take the next. we also try to skip any
        // whitespace and comments while we do that, they are ignored at lex time.
        while let Some(ch) = self.consume_next() {
            // if we hit whitespace, skip it and try to take next token
            if ch.is_ascii_whitespace() {
                continue;
            }

            // if we get the beginning of a comment, skip until newline or EOF and try to loop again
            if ch == ';' {
                // this covers both LF and CRLF
                while self.peek_next().is_some_and(|c| c != '\n') {
                    self.consume_next();
                }

                // consume the newline, if it exists. if we're already at the end,
                // this doesn't actually do anything
                self.consume_next();

                continue;
            }

            return Some(ch);
        }

        // we hit EOF inside the loop
        None
    }

    fn consume_next(&mut self) -> Option<char> {
        let ch = self.chars.next();

        if let Some(ch) = ch {
            if ch == b'\n' {
                self.line += 1;
                self.col = 0;
            } else {
                self.col += 1;
            }

            self.current += 1;
        }

        ch.map(|ch| ch as char)
    }

    fn consume_while(&mut self, f: impl Fn(char) -> bool) {
        while let Some(ch) = self.peek_next() {
            if f(ch) {
                self.consume_next();
            } else {
                return;
            }
        }
    }

    #[inline]
    fn peek_next(&mut self) -> Option<char> {
        self.chars.peek().map(|&ch| ch as char)
    }

    #[inline]
    fn last_consumed_as_str(&self) -> &'a str {
        &self.source[self.current - 1..self.current]
    }
}
