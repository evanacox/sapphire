//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::SecondaryMap;
use crate::codegen::x86_64::*;
use crate::codegen::{
    Emitter, Extern, MIRBlock, MIRFuncData, MIRFunction, MIRModule, PReg, Reg, RegClass, TargetPair,
};
use crate::ir::{FloatFormat, UType};
use crate::utility::{SaHashMap, StringPool};
use smallvec::SmallVec;
use std::iter;
use std::str::FromStr;

/// Different assembly formats for x86-64
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum X86_64Assembly {
    /// Output compatible with GNU `as`
    GNU,
    /// Output compatible with GNU `as`, but in Intel syntax
    GNUIntel,
    /// Output compatible with NASM
    NASM,
    /// Output compatible with MASM
    MASM,
}

#[inline]
fn format_int_reg(
    byte: &'static str,
    word: &'static str,
    dword: &'static str,
    qword: &'static str,
    width: Width,
) -> &'static str {
    match width {
        Width::Byte => byte,
        Width::Word => word,
        Width::Dword => dword,
        Width::Qword => qword,
        Width::Xmmword => panic!("tried to access 64-bit register as an xmmword"),
    }
}

/// Formats the "canonical" assembly form of an x86-64 register
pub fn format_reg(reg: Reg, width: Width, syntax: X86_64Assembly) -> String {
    let asm_prefix = if syntax == X86_64Assembly::GNU {
        "%"
    } else {
        ""
    };

    if let Some(vreg) = reg.as_vreg() {
        let number = vreg.hw_number();
        let prefix = match vreg.class() {
            RegClass::Float => "f",
            RegClass::Int => "i",
        };

        format!("{asm_prefix}v{prefix}{number}")
    } else {
        let preg = reg.as_preg().unwrap();

        if preg.class() == RegClass::Float {
            let n = preg.hw_number();

            return format!("{asm_prefix}xmm{n}");
        }

        let name = match preg {
            X86_64::RAX => format_int_reg("al", "ax", "eax", "rax", width),
            X86_64::RBX => format_int_reg("bl", "bx", "ebx", "rbx", width),
            X86_64::RCX => format_int_reg("cl", "cx", "ecx", "rcx", width),
            X86_64::RDX => format_int_reg("dl", "dx", "edx", "rdx", width),
            X86_64::RSI => format_int_reg("sil", "si", "esi", "rsi", width),
            X86_64::RDI => format_int_reg("dil", "di", "edi", "rdi", width),
            X86_64::RBP => format_int_reg("bpl", "bp", "ebp", "rbp", width),
            X86_64::RSP => format_int_reg("spl", "sp", "esp", "rsp", width),
            X86_64::R8 => format_int_reg("r8b", "r8w", "r8d", "r8", width),
            X86_64::R9 => format_int_reg("r9b", "r9w", "r9d", "r9", width),
            X86_64::R10 => format_int_reg("r10b", "r10w", "r10d", "r10", width),
            X86_64::R11 => format_int_reg("r11b", "r11w", "r11d", "r11", width),
            X86_64::R12 => format_int_reg("r12b", "r12w", "r12d", "r12", width),
            X86_64::R13 => format_int_reg("r13b", "r13w", "r13d", "r13", width),
            X86_64::R14 => format_int_reg("r14b", "r14w", "r14d", "r14", width),
            X86_64::R15 => format_int_reg("r15b", "r15w", "r15d", "r15", width),
            _ => unreachable!(),
        };

        format!("{asm_prefix}{name}")
    }
}

impl FromStr for X86_64Assembly {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "gnu" => Ok(Self::GNU),
            "gnu-intel" => Ok(Self::GNUIntel),
            "nasm" => Ok(Self::NASM),
            "masm" => Ok(Self::MASM),
            _ => Err(
                "only available x86-64 assembly formats are `gnu`, `gnu-intel`, `nasm` and `masm`",
            ),
        }
    }
}

/// Different object file formats for x86-64
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum X86_64ObjectFile {
    /// The ELF object format
    ELF,
    /// The Mach-O object format
    MachO,
    /// The PE object format
    PE,
}

impl FromStr for X86_64ObjectFile {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "elf" => Ok(Self::ELF),
            "macho" => Ok(Self::MachO),
            "pe" => Ok(Self::PE),
            _ => Err("only available x86-64 assembly formats are `elf`, `macho`, and `pe`"),
        }
    }
}

/// The x86-64 emitter. This delegates to more specialized (and internal) mechanisms
/// to do the actual emitting.
pub struct Emit;

impl Emitter<X86_64> for Emit {
    type AssemblyFormat = X86_64Assembly;
    type ObjectCodeFormat = X86_64ObjectFile;

    fn assembly(
        module: &MIRModule<Inst>,
        format: Self::AssemblyFormat,
        target: TargetPair,
        fixed_interval_comments: bool,
    ) -> String {
        let emitter = AsmEmitter {
            mode: format,
            pair: target,
            state: String::default(),
            pool: module.symbols().clone(),
            label_count: 0,
            block_names: SecondaryMap::default(),
            data_names: SecondaryMap::default(),
            fixed_interval_comments,
        };

        emitter.emit(module)
    }

    fn object(module: &MIRModule<Inst>, format: Self::ObjectCodeFormat) -> Vec<u8> {
        todo!()
    }
}

type FixedBeginEndAndCallerDefined = (
    SaHashMap<usize, SmallVec<[PReg; 2]>>,
    SaHashMap<usize, SmallVec<[PReg; 2]>>,
    Vec<PReg>,
);

struct AsmEmitter {
    mode: X86_64Assembly,
    pair: TargetPair,
    state: String,
    pool: StringPool,
    label_count: usize,
    block_names: SecondaryMap<MIRBlock, String>,
    data_names: SecondaryMap<MIRFuncData, String>,
    fixed_interval_comments: bool,
}

impl AsmEmitter {
    fn emit(mut self, module: &MIRModule<Inst>) -> String {
        self.pool = module.symbols().clone();

        if self.mode == X86_64Assembly::GNUIntel {
            self.state += "    .intel_syntax noprefix\n";
        }

        self.emit_global_symbols(module);
        self.emit_extern_symbols(module);

        for (function, frame) in module.functions() {
            let name = self.correct_symbol_name(
                module
                    .symbols()
                    .get(function.name())
                    .expect("should have name"),
            );

            self.emit_function(&name, function);
        }

        if self.mode == X86_64Assembly::MASM {
            self.state += "END\n"
        }

        self.state
    }

    #[inline]
    fn is_mac_os(&self) -> bool {
        matches!(self.pair, TargetPair::X86_64macOS | TargetPair::Arm64macOS)
    }

    fn correct_symbol_name(&self, name: &str) -> String {
        if self.is_mac_os() {
            format!("_{name}")
        } else {
            name.to_string()
        }
    }

    fn emit_global_symbols(&mut self, module: &MIRModule<Inst>) {
        let strings = module.symbols();

        for (function, frame) in module.functions() {
            let name =
                self.correct_symbol_name(strings.get(function.name()).expect("should have name"));

            let real = match self.mode {
                X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                    format!("    .globl {name}\n")
                }
                X86_64Assembly::NASM => format!("    global {name}\n"),
                X86_64Assembly::MASM => format!("PUBLIC {name}:PROC \n"),
            };

            self.state += &real;
        }
    }

    fn emit_extern_masm(&self, name: &str, ty: Extern) -> String {
        let ty = match ty {
            Extern::Function => "PROC",
            Extern::Object(ty) => match ty.unpack() {
                UType::Bool(_) | UType::Array(_) | UType::Struct(_) => "BYTE",
                UType::Ptr(_) => "QWORD",
                UType::Int(int) => match int.width() {
                    8 => "BYTE",
                    16 => "WORD",
                    32 => "DWORD",
                    64 => "QWORD",
                    _ => unreachable!(),
                },
                UType::Float(float) => match float.format() {
                    FloatFormat::Single => "DWORD",
                    FloatFormat::Double => "QWORD",
                },
            },
        };

        format!("EXTRN {name}:{ty} \n")
    }

    fn emit_extern_symbols(&mut self, module: &MIRModule<Inst>) {
        if self.mode == X86_64Assembly::MASM || self.mode == X86_64Assembly::NASM {
            for &(name, ty) in module.externals() {
                let formatted = {
                    let real = self.pool.get(name).expect("external name must be valid");

                    if self.mode == X86_64Assembly::MASM {
                        self.emit_extern_masm(real, ty)
                    } else {
                        format!("    .extern {real}")
                    }
                };

                self.state += &formatted;
            }
        }
    }

    fn emit_section_text(&mut self) {
        let s = match self.pair {
            TargetPair::X86_64Linux | TargetPair::Aarch64Linux | TargetPair::Debug3Reg => {
                match self.mode {
                    X86_64Assembly::GNU | X86_64Assembly::GNUIntel => "    .text",
                    X86_64Assembly::NASM => "    section .text",
                    X86_64Assembly::MASM => {
                        panic!("cannot create MASM assembly output when targeting Linux")
                    }
                }
            }
            TargetPair::X86_64macOS | TargetPair::Arm64macOS => match self.mode {
                X86_64Assembly::GNU | X86_64Assembly::GNUIntel => "    .text",
                X86_64Assembly::NASM => "    section __TEXT,__text",
                X86_64Assembly::MASM => {
                    panic!("cannot create MASM assembly output when targeting macOS")
                }
            },
            TargetPair::X86_64Windows | TargetPair::Arm64Windows => match self.mode {
                X86_64Assembly::GNU | X86_64Assembly::GNUIntel => "    .text",
                X86_64Assembly::NASM => "    section .text",
                X86_64Assembly::MASM => "_TEXT SEGMENT",
            },
        };

        self.state += s;
        self.state += "\n";
    }

    fn emit_section_constant(&mut self, constant: &Constant) {
        const SECTION_NAMES: [[&str; 7]; 2] = [
            // Linux
            [
                ".rodata.cst8,\"aM\",@progbits,8",    // quad-label
                ".rodata.cst8,\"aM\",@progbits,8",    // quad
                ".rodata.cst4,\"aM\",@progbits,4",    // long
                ".rodata.cst2,\"aM\",@progbits,2",    // short
                ".rodata.cst1,\"aM\",@progbits,1",    // byte
                ".rodata,\"a\",@progbits",            // array
                ".rodata.str1.1,\"aMS\",@progbits,1", // string: MUST HAVE .size FOLLOWING IT
            ],
            // macOS
            [
                "__TEXT,__literal8", // quad-label
                "__TEXT,__literal8", // quad
                "__TEXT,__literal4", // long
                "__TEXT,__const",    // short
                "__TEXT,__const",    // byte
                "__TEXT,__const",    // array
                "__TEXT,__cstring",  // string: MUST HAVE .size FOLLOWING IT
            ],
        ];

        fn index_align_of_constant(constant: &Constant) -> (usize, usize) {
            match &constant {
                Constant::QuadLabel(_) => (0, 8),
                Constant::Quad(_) => (1, 8),
                Constant::Long(_) => (2, 4),
                Constant::Short(_) => (3, 2),
                Constant::Byte(_) => (4, 1),
                Constant::Array(inside) => {
                    // this is guaranteed to terminate eventually, we'll get the align of the innermost array element
                    // and then we'll know our minimum alignment for the array as a whole
                    (5, index_align_of_constant(constant).1)
                }
                Constant::String(_) => (6, 1),
            }
        }

        let (section_name_index, align) = index_align_of_constant(constant);

        let name = match self.pair {
            TargetPair::X86_64Linux | TargetPair::Aarch64Linux | TargetPair::Debug3Reg => {
                if !matches!(
                    self.mode,
                    X86_64Assembly::GNU | X86_64Assembly::GNUIntel | X86_64Assembly::NASM
                ) {
                    panic!("cannot create MASM assembly output when targeting Linux")
                }

                SECTION_NAMES[0][section_name_index]
            }
            TargetPair::X86_64macOS | TargetPair::Arm64macOS => {
                if !matches!(
                    self.mode,
                    X86_64Assembly::GNU | X86_64Assembly::GNUIntel | X86_64Assembly::NASM
                ) {
                    panic!("cannot create MASM assembly output when targeting macOS")
                }

                SECTION_NAMES[1][section_name_index]
            }
            TargetPair::X86_64Windows | TargetPair::Arm64Windows => ".rdata",
        };

        let line = match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => format!("    .section {name}"),
            X86_64Assembly::NASM => format!("    section {name}"),
            X86_64Assembly::MASM => "CONST SEGMENT".to_string(),
        };

        self.state += &line;
        self.state += "\n";

        match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                self.state += &format!("    .align {align}\n");
            }
            X86_64Assembly::NASM => {
                self.state += &format!("    align {align}\n");
            }
            X86_64Assembly::MASM => {
                // we don't have to worry about it for MASM
            }
        }
    }

    fn emit_function_name(&mut self, name: &str, defined_by_caller: &[PReg]) {
        self.emit_section_text();

        let name = match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                self.state += "    .align 32\n";

                format!("{name}:")
            }
            X86_64Assembly::NASM => {
                self.state += "    align 32\n";

                format!("{name}:")
            }
            X86_64Assembly::MASM => {
                format!("{name} PROC")
            }
        };

        self.state += &name;

        if self.fixed_interval_comments && !defined_by_caller.is_empty() {
            // append spaces if name isn't obscenely long
            if name.len() < 50 {
                self.state.extend(iter::repeat(' ').take(50 - name.len()));
            } else {
                self.state += " ";
            }

            self.state += &format!("{} def by caller:", self.comment_char());

            for &reg in defined_by_caller {
                let r = self.emit_reg(Reg::from_preg(reg), Width::Qword);

                self.state += &format!(" {r},");
            }

            // remove last ,
            self.state.pop();
        }

        self.state += "\n";
    }

    fn emit_single_constant(&mut self, key: MIRFuncData, constant: &Constant) {
        self.emit_section_constant(constant);

        let constant = match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => match constant {
                Constant::QuadLabel(block) => {
                    let name = &self.block_names[*block];

                    format!("    .quad {name}")
                }
                Constant::Quad(value) => format!("    .quad 0x{value:016x}"),
                Constant::Long(value) => format!("    .long 0x{value:08x}"),
                Constant::Short(value) => format!("   .short 0x{value:04x}"),
                Constant::Byte(value) => format!("   .byte 0x{value:02x}"),
                Constant::Array(_) => todo!(),
                Constant::String(_) => todo!(),
            },
            X86_64Assembly::NASM => {
                todo!()
            }
            X86_64Assembly::MASM => {
                todo!()
            }
        };

        let label = format!("{}:\n", &self.data_names[key]);

        self.state += &label;
        self.state += &constant;
        self.state += "\n";
    }

    fn emit_function_data(&mut self, function: &MIRFunction<Inst>) {
        match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                for (key, data) in function.data() {
                    self.emit_single_constant(key, data);
                }
            }
            X86_64Assembly::NASM => {}
            X86_64Assembly::MASM => {}
        }
    }

    fn emit_function(&mut self, name: &str, function: &MIRFunction<Inst>) {
        self.block_names = SecondaryMap::default();
        self.data_names = SecondaryMap::default();

        let (fixed_begin_at, fixed_end_at, defined_by_caller) = self.fixed_begin_end(function);
        let mut i = 0usize;

        self.emit_function_name(name, &defined_by_caller);

        // skip 1, we don't want to put a label on the first block
        for &block in function.program_order().iter().skip(1) {
            let curr = self.label_count;
            let name = match self.mode {
                X86_64Assembly::MASM => format!("$L{curr}"),
                X86_64Assembly::NASM | X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                    format!(".L{curr}")
                }
            };

            self.label_count += 1;
            self.block_names.insert(block, name);
        }

        for (key, _) in function.data() {
            let curr = self.label_count;
            let name = match self.mode {
                X86_64Assembly::MASM => {
                    let name = self.pool.get(function.name()).unwrap();

                    format!("{name}_const_L{curr}")
                }
                X86_64Assembly::NASM | X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                    format!(".LC{curr}")
                }
            };

            self.label_count += 1;
            self.data_names.insert(key, name);
        }

        if self.mode == X86_64Assembly::MASM {
            self.emit_function_data(function);
        }

        for &block in function.program_order().iter() {
            if let Some(name) = self.block_names.get(block) {
                self.state += name;
                self.state += ":\n";
            }

            for &inst in function.block(block) {
                let asm = self.emit_inst(inst);

                self.emit_single_inst(i, asm, &fixed_begin_at, &fixed_end_at);

                i += 1;
            }
        }

        match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                self.state += "    .section \".note.GNU-stack\",\"\",@progbits\n";
            }
            X86_64Assembly::NASM => {
                self.state += "    section \".note.GNU-stack\",\"\",@progbits\n";
            }
            X86_64Assembly::MASM => self.state += "_TEXT ENDS\n",
        }

        if self.mode != X86_64Assembly::MASM {
            self.emit_function_data(function);
        }
    }

    fn fixed_begin_end(&mut self, function: &MIRFunction<Inst>) -> FixedBeginEndAndCallerDefined {
        let mut fixed_begin_at = SaHashMap::<usize, SmallVec<[PReg; 2]>>::default();
        let mut fixed_end_at = SaHashMap::<usize, SmallVec<[PReg; 2]>>::default();
        let mut defined_by_caller = Vec::<PReg>::default();

        for (reg, intervals) in function.fixed_intervals().all_intervals() {
            for &interval in intervals {
                match interval.first_defined_after() {
                    Some(idx) => {
                        fixed_begin_at.entry(idx as usize).or_default().push(reg);
                    }
                    None => {
                        defined_by_caller.push(reg);
                    }
                }

                fixed_end_at
                    .entry(interval.last_used_by() as usize)
                    .or_default()
                    .push(reg);
            }
        }

        (fixed_begin_at, fixed_end_at, defined_by_caller)
    }

    fn emit_fixed_regs(
        &mut self,
        prefix: &'static str,
        i: usize,
        map: &SaHashMap<usize, SmallVec<[PReg; 2]>>,
    ) {
        let mut looped = false;

        if let Some(vec) = map.get(&i) {
            self.state += " ";
            self.state += prefix;
            self.state += "( ";

            for &reg in map.get(&i).unwrap().iter() {
                looped = true;

                self.state += &format!("{}, ", self.emit_reg(Reg::from_preg(reg), Width::Qword));
            }

            if looped {
                self.state.pop();
                self.state.pop();
            }

            self.state += " )";
        }
    }

    fn emit_single_inst(
        &mut self,
        i: usize,
        asm: String,
        fixed_begin_at: &SaHashMap<usize, SmallVec<[PReg; 2]>>,
        fixed_end_at: &SaHashMap<usize, SmallVec<[PReg; 2]>>,
    ) {
        // if we begin or end any fixed intervals, we print it out here.
        //
        // we'll get a result that looks like this:
        //
        //     mov vi0, rax                      ; fixed: end rax
        //
        if self.fixed_interval_comments
            && (fixed_begin_at.contains_key(&i) || fixed_end_at.contains_key(&i))
        {
            let ch = self.comment_char();

            self.state += &format!("    {asm:<45} {ch} fixed:");
            self.emit_fixed_regs("begin", i, fixed_begin_at);
            self.emit_fixed_regs("end", i, fixed_end_at);

            self.state += "\n";
        } else {
            self.state += "    ";
            self.state += &asm;
            self.state += "\n";
        }
    }

    fn comment_char(&self) -> char {
        match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => '#',
            X86_64Assembly::NASM | X86_64Assembly::MASM => ';',
        }
    }

    fn emit_inst(&self, inst: Inst) -> String {
        match inst {
            Inst::Nop(_) => "nop".into(),
            Inst::Mov(mov) => self.emit_mov(mov),
            Inst::Movsx(movsx) => self.emit_movsx(movsx),
            Inst::Movzx(movzx) => self.emit_movzx(movzx),
            Inst::MovStore(mov) => self.emit_mov_store(mov),
            Inst::Movabs(movabs) => self.emit_movabs(movabs),
            Inst::Movaps(movaps) => self.emit_movaps(movaps),
            Inst::MovFloatLoad(movs) => self.emit_movs_load(movs),
            Inst::MovFloatStore(movs) => self.emit_movs_store(movs),
            Inst::Lea(lea) => self.emit_lea(lea),
            Inst::ALU(alu) => self.emit_alu(alu),
            Inst::Not(not) => self.emit_not(not),
            Inst::Neg(neg) => self.emit_neg(neg),
            Inst::IMul(imul) => self.emit_imul(imul),
            Inst::Cwd(_) => "cwd".into(),
            Inst::Cdq(_) => "cdq".into(),
            Inst::Cqo(_) => "cqo".into(),
            Inst::Div(div) => self.emit_div(div),
            Inst::IDiv(idiv) => self.emit_idiv(idiv),
            Inst::PXor(pxor) => self.emit_pxor(pxor),
            Inst::FloatArith(arith) => self.emit_float_alu(arith),
            Inst::Cmp(cmp) => self.emit_cmp(cmp),
            Inst::Test(test) => self.emit_test(test),
            Inst::Set(set) => self.emit_set(set),
            Inst::Push(push) => self.emit_push(push),
            Inst::Pop(pop) => self.emit_pop(pop),
            Inst::Call(call) => self.emit_call(call),
            Inst::IndirectCall(indirectcall) => self.emit_indirectcall(indirectcall),
            Inst::Jump(jump) => self.emit_jump(jump),
            Inst::Ret(_) => "ret".into(),
            Inst::Ud2(_) => "ud2".into(),
        }
    }

    fn emit_reg(&self, reg: Reg, width: Width) -> String {
        format_reg(reg, width, self.mode)
    }

    fn emit_indirect_address(&self, loc: IndirectAddress) -> String {
        match loc {
            IndirectAddress::Reg(reg) => {
                // while we may not be *loading* a qword, we want the full qword register
                // when we're dereferencing it. you wouldn't do `dword ptr [eax]`
                let emit = self.emit_reg(reg, Width::Qword);

                if self.mode == X86_64Assembly::GNU {
                    format!("({emit})")
                } else {
                    format!("[{emit}]")
                }
            }
            IndirectAddress::RegReg(r1, r2) => {
                let e1 = self.emit_reg(r1, Width::Qword);
                let e2 = self.emit_reg(r2, Width::Qword);

                if self.mode == X86_64Assembly::GNU {
                    format!("({e1}, {e2})")
                } else {
                    format!("[{e1} + {e2}]")
                }
            }
            IndirectAddress::StackOffset(offset, _, _) => {
                let emit = self.emit_reg(Reg::from_preg(X86_64::RSP), Width::Qword);

                if self.mode == X86_64Assembly::GNU {
                    format!("__pseudo_stackoffset {offset}({emit})")
                } else if offset >= 0 {
                    format!("__pseudo_stackoffset [{emit} + {offset}]")
                } else {
                    let abs = offset.abs();

                    format!("__pseudo_stackoffset [{emit} - {abs}]")
                }
            }
            IndirectAddress::RegOffset(reg, offset) => {
                let emit = self.emit_reg(reg, Width::Qword);

                if self.mode == X86_64Assembly::GNU {
                    if offset != 0 {
                        format!("{offset}({emit})")
                    } else {
                        format!("({emit})")
                    }
                } else if offset == 0 {
                    format!("[{emit}]")
                } else if offset >= 0 {
                    format!("[{emit} + {offset}]")
                } else {
                    let abs = offset.abs();

                    format!("[{emit} - {abs}]")
                }
            }
            IndirectAddress::ScaledReg(reg, scale) => {
                let emit = self.emit_reg(reg, Width::Qword);
                let integral: i32 = scale.into();

                if self.mode == X86_64Assembly::GNU {
                    format!("({emit},{integral})")
                } else {
                    format!("[{emit}*{integral}]")
                }
            }
            IndirectAddress::RegScaledReg(r1, r2, scale) => {
                let e1 = self.emit_reg(r1, Width::Qword);
                let e2 = self.emit_reg(r2, Width::Qword);
                let integral: i32 = scale.into();

                if self.mode == X86_64Assembly::GNU {
                    format!("({e1},{e2},{integral})")
                } else {
                    format!("[{e1} + {e2}*{integral}]")
                }
            }
            IndirectAddress::RegScaledRegIndex(r1, r2, scale_offset) => {
                let e1 = self.emit_reg(r1, Width::Qword);
                let e2 = self.emit_reg(r2, Width::Qword);
                let (scale, offset) = scale_offset.expand();
                let integral: i32 = scale.into();

                if self.mode == X86_64Assembly::GNU {
                    format!("{offset}({e1},{e2},{integral})")
                } else {
                    format!("[{e1} + {e2}*{integral} + {offset}]")
                }
            }
            IndirectAddress::RipLocalData(data) => {
                let string = &self.data_names[data];

                match self.mode {
                    X86_64Assembly::GNU => format!("{string}(%rip)"),
                    X86_64Assembly::NASM => format!("[rel {string}]"),
                    X86_64Assembly::GNUIntel | X86_64Assembly::MASM => format!("{string}[rip]"),
                }
            }
            IndirectAddress::RipLocalLabel(bb) => {
                let string = &self.block_names[bb];

                match self.mode {
                    X86_64Assembly::GNU => format!("{string}(%rip)"),
                    X86_64Assembly::NASM => format!("[rel {string}]"),
                    X86_64Assembly::GNUIntel | X86_64Assembly::MASM => format!("{string}[rip]"),
                }
            }
            IndirectAddress::RipGlobal(global) => {
                let string = self.pool.get(global).expect("invalid symbol key");

                match self.mode {
                    X86_64Assembly::GNU => format!("{string}(%rip)"),
                    X86_64Assembly::NASM => format!("[rel {string}]"),
                    X86_64Assembly::GNUIntel | X86_64Assembly::MASM => format!("{string}[rip]"),
                }
            }
        }
    }

    fn emit_mem_location(&self, loc: IndirectAddress, width: Width) -> String {
        let reference = self.emit_indirect_address(loc);
        let prefix = match self.mode {
            X86_64Assembly::GNU => "",
            X86_64Assembly::NASM => format_int_reg("byte ", "word ", "dword ", "qword ", width),
            X86_64Assembly::GNUIntel | X86_64Assembly::MASM => {
                format_int_reg("byte ptr ", "word ptr ", "dword ptr ", "qword ptr ", width)
            }
        };

        format!("{prefix}{reference}")
    }

    fn emit_rmi(&self, rmi: RegMemImm, width: Width) -> String {
        match rmi {
            RegMemImm::Reg(reg) => self.emit_reg(reg, width),
            RegMemImm::Mem(loc) => self.emit_mem_location(loc, width),
            RegMemImm::Imm(x) => {
                if self.mode == X86_64Assembly::GNU {
                    format!("${x}")
                } else {
                    format!("{x}")
                }
            }
        }
    }

    fn reorder_operands(&self, src: String, dest: String) -> (String, String) {
        match self.mode {
            X86_64Assembly::GNU => (src, dest),
            X86_64Assembly::GNUIntel | X86_64Assembly::NASM | X86_64Assembly::MASM => (dest, src),
        }
    }

    fn suffix(&self, width: Width) -> &'static str {
        if self.mode == X86_64Assembly::GNU {
            format_int_reg("b", "w", "l", "q", width)
        } else {
            ""
        }
    }

    fn emit_mov(&self, mov: Mov) -> String {
        let src = self.emit_rmi(mov.src, mov.width);
        let dest = self.emit_reg(mov.dest.to_reg(), mov.width);
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let suffix = self.suffix(mov.width);

        format!("mov{suffix} {lhs}, {rhs}")
    }

    fn extension_suffixes(&self, widths: WidthPair) -> (&'static str, &'static str, &'static str) {
        match self.mode {
            X86_64Assembly::GNU => (
                "",
                self.suffix(widths.src_width()),
                self.suffix(widths.dest_width()),
            ),
            X86_64Assembly::GNUIntel | X86_64Assembly::NASM | X86_64Assembly::MASM => ("x", "", ""),
        }
    }

    fn emit_movsx(&self, mov: Movsx) -> String {
        let src = self.emit_rmi(mov.src, mov.widths.src_width());
        let dest = self.emit_reg(mov.dest.to_reg(), mov.widths.dest_width());
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let (s1, s2, s3) = self.extension_suffixes(mov.widths);

        format!("movs{s1}{s2}{s3} {lhs}, {rhs}")
    }

    fn emit_movzx(&self, mov: Movzx) -> String {
        let src = self.emit_rmi(mov.src, mov.widths.src_width());
        let dest = self.emit_reg(mov.dest.to_reg(), mov.widths.dest_width());
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let (s1, s2, s3) = self.extension_suffixes(mov.widths);

        format!("movz{s1}{s2}{s3} {lhs}, {rhs}")
    }

    fn emit_mov_store(&self, mov: MovStore) -> String {
        let src = self.emit_rmi(mov.src.into(), mov.width);
        let dest = self.emit_mem_location(mov.dest, mov.width);
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let suffix = self.suffix(mov.width);

        format!("mov{suffix} {lhs}, {rhs}")
    }

    fn emit_movabs(&self, movabs: Movabs) -> String {
        let value = format!("{}", movabs.value);
        let dest = self.emit_reg(movabs.dest.to_reg(), Width::Qword);
        let (lhs, rhs) = self.reorder_operands(value, dest);

        format!("movabs {lhs}, {rhs}")
    }

    fn emit_movaps(&self, movaps: Movaps) -> String {
        let src = self.emit_reg(movaps.src, Width::Qword);
        let dest = self.emit_reg(movaps.dest.to_reg(), Width::Qword);
        let (lhs, rhs) = self.reorder_operands(src, dest);

        format!("movaps {lhs}, {rhs}")
    }

    fn emit_movs_load(&self, movs: MovFloatLoad) -> String {
        let src = self.emit_rmi(RegMemImm::Mem(movs.src), Width::Qword);
        let dest = self.emit_reg(movs.dest.to_reg(), Width::Qword);
        let suffix = Self::float_op_suffix(movs.format);
        let (lhs, rhs) = self.reorder_operands(src, dest);

        format!("movs{suffix} {lhs}, {rhs}")
    }

    fn emit_movs_store(&self, movs: MovFloatStore) -> String {
        let src = self.emit_reg(movs.src, Width::Qword);
        let dest = self.emit_rmi(RegMemImm::Mem(movs.dest), Width::Qword);
        let suffix = Self::float_op_suffix(movs.format);
        let (lhs, rhs) = self.reorder_operands(src, dest);

        format!("movs{suffix} {lhs}, {rhs}")
    }

    fn emit_lea(&self, lea: Lea) -> String {
        let address = self.emit_indirect_address(lea.src);
        let dest = self.emit_reg(lea.dest.to_reg(), Width::Qword);
        let (lhs, rhs) = self.reorder_operands(address, dest);
        let suffix = self.suffix(Width::Qword);

        format!("lea{suffix} {lhs}, {rhs}")
    }

    fn emit_alu(&self, alu: ALU) -> String {
        let src = self.emit_rmi(alu.rhs, alu.width);
        let dest = self.emit_reg(alu.lhs.to_reg(), alu.width);
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let suffix = self.suffix(alu.width);
        let opc = match alu.opc {
            ALUOpcode::And => "and",
            ALUOpcode::Or => "or",
            ALUOpcode::Xor => "xor",
            ALUOpcode::Shl => "shl",
            ALUOpcode::Sar => "sar",
            ALUOpcode::Shr => "shr",
            ALUOpcode::Add => "add",
            ALUOpcode::Sub => "sub",
        };

        format!("{opc}{suffix} {lhs}, {rhs}")
    }

    fn emit_not(&self, not: Not) -> String {
        let dest = self.emit_reg(not.reg.to_reg(), not.width);
        let suffix = self.suffix(not.width);

        format!("not{suffix} {dest}")
    }

    fn emit_neg(&self, neg: Neg) -> String {
        let dest = self.emit_reg(neg.reg.to_reg(), neg.width);
        let suffix = self.suffix(neg.width);

        format!("neg{suffix} {dest}")
    }

    fn emit_imul(&self, imul: IMul) -> String {
        let src = self.emit_rmi(imul.rhs, imul.width);
        let dest = self.emit_reg(imul.lhs.to_reg(), imul.width);
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let suffix = self.suffix(imul.width);

        format!("imul{suffix} {lhs}, {rhs}")
    }

    fn emit_div(&self, div: Div) -> String {
        let src = self.emit_rmi(div.divisor.into(), div.width);
        let suffix = self.suffix(div.width);

        format!("div{suffix} {src}")
    }

    fn emit_idiv(&self, idiv: IDiv) -> String {
        let src = self.emit_rmi(idiv.divisor.into(), idiv.width);
        let suffix = self.suffix(idiv.width);

        format!("idiv{suffix} {src}")
    }

    fn emit_pxor(&self, pxor: PXor) -> String {
        let src = self.emit_reg(pxor.rhs, Width::Xmmword);
        let dest = self.emit_reg(pxor.lhs.to_reg(), Width::Xmmword);
        let (lhs, rhs) = self.reorder_operands(src, dest);

        format!("pxor {lhs}, {rhs}")
    }

    fn emit_float_alu(&self, arith: FloatArith) -> String {
        let width = match arith.format {
            FloatFormat::Single => Width::Dword,
            FloatFormat::Double => Width::Qword,
        };

        let src = self.emit_rmi(arith.rhs.into(), width);
        let dest = self.emit_reg(arith.lhs.to_reg(), width);
        let suffix = Self::float_op_suffix(arith.format);
        let opc = match arith.opc {
            FloatArithOpcode::Add => "adds",
            FloatArithOpcode::Sub => "subs",
            FloatArithOpcode::Mul => "muls",
            FloatArithOpcode::Div => "divs",
        };

        let (lhs, rhs) = self.reorder_operands(src, dest);

        format!("{opc}{suffix} {lhs}, {rhs}")
    }

    fn emit_cmp(&self, cmp: Cmp) -> String {
        let src = self.emit_rmi(cmp.rhs, cmp.width);
        let dest = self.emit_reg(cmp.lhs, cmp.width);
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let suffix = self.suffix(cmp.width);

        format!("cmp{suffix} {lhs}, {rhs}")
    }

    fn emit_test(&self, test: Test) -> String {
        let src = self.emit_rmi(test.rhs, test.width);
        let dest = self.emit_reg(test.lhs, test.width);
        let (lhs, rhs) = self.reorder_operands(src, dest);
        let suffix = self.suffix(test.width);

        format!("test{suffix} {lhs}, {rhs}")
    }

    fn emit_push(&self, push: Push) -> String {
        let reg = self.emit_reg(push.value, push.width);
        let suffix = self.suffix(push.width);

        format!("push{suffix} {reg}")
    }

    fn emit_pop(&self, pop: Pop) -> String {
        let reg = self.emit_reg(pop.dest.to_reg(), pop.width);
        let suffix = self.suffix(pop.width);

        format!("pop{suffix} {reg}")
    }

    fn emit_call(&self, call: Call) -> String {
        let name = self.pool.get(call.func).unwrap();
        let suffix = match self.mode {
            X86_64Assembly::GNU => "q",
            X86_64Assembly::GNUIntel | X86_64Assembly::NASM | X86_64Assembly::MASM => "",
        };

        format!("call{suffix} {name}")
    }

    fn emit_indirectcall(&self, indirectcall: IndirectCall) -> String {
        let value = self.emit_rmi(indirectcall.func, Width::Qword);
        let (s1, s2) = match self.mode {
            X86_64Assembly::GNU => ("q", "*"),
            X86_64Assembly::GNUIntel | X86_64Assembly::NASM | X86_64Assembly::MASM => ("", ""),
        };

        format!("call{s1} {s2}{value}")
    }

    fn condition_code_suffix(condition: ConditionCode) -> &'static str {
        match condition {
            ConditionCode::E => "e",
            ConditionCode::NE => "ne",
            ConditionCode::Z => "z",
            ConditionCode::NZ => "nz",
            ConditionCode::G => "g",
            ConditionCode::GE => "ge",
            ConditionCode::L => "l",
            ConditionCode::LE => "le",
            ConditionCode::A => "a",
            ConditionCode::AE => "ae",
            ConditionCode::B => "b",
            ConditionCode::BE => "be",
            ConditionCode::S => "s",
            ConditionCode::NS => "ns",
            ConditionCode::O => "o",
            ConditionCode::NO => "no",
        }
    }

    fn float_op_suffix(format: FloatFormat) -> &'static str {
        match format {
            FloatFormat::Single => "s",
            FloatFormat::Double => "d",
        }
    }

    fn emit_set(&self, set: Set) -> String {
        let dest = self.emit_reg(set.dest.to_reg(), Width::Byte);
        let suffix = Self::condition_code_suffix(set.condition);

        format!("set{suffix} {dest}")
    }

    fn emit_jump(&self, jump: Jump) -> String {
        let name = match jump.target {
            JumpTarget::Global(name) => self.pool.get(name).unwrap(),
            JumpTarget::Local(bb) => &self.block_names[bb],
        };

        let suffix = match jump.condition {
            Some(cc) => Self::condition_code_suffix(cc),
            None => "mp",
        };

        format!("j{suffix} {name}")
    }
}
