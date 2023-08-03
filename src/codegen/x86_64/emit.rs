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
    Emitter, Extern, MIRBlock, MIRFunction, MIRModule, PReg, Reg, RegClass, TargetPair,
};
use crate::ir::{FloatFormat, UType};
use crate::utility::{SaHashMap, StringPool};
use smallvec::SmallVec;
use std::str::FromStr;
use std::{iter, mem};

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

fn into_mac_os_symbol_name(name: &str, is_mac: bool) -> String {
    if is_mac {
        format!("_{name}")
    } else {
        name.to_string()
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
            X86_64::RAX => match width {
                Width::Byte => "al",
                Width::Word => "ax",
                Width::Dword => "eax",
                Width::Qword => "rax",
            },
            X86_64::RBX => match width {
                Width::Byte => "bl",
                Width::Word => "bx",
                Width::Dword => "ebx",
                Width::Qword => "rbx",
            },
            X86_64::RCX => match width {
                Width::Byte => "cl",
                Width::Word => "cx",
                Width::Dword => "ecx",
                Width::Qword => "rcx",
            },
            X86_64::RDX => match width {
                Width::Byte => "dl",
                Width::Word => "dx",
                Width::Dword => "edx",
                Width::Qword => "rdx",
            },
            X86_64::RSI => match width {
                Width::Byte => "sil",
                Width::Word => "si",
                Width::Dword => "esi",
                Width::Qword => "rsi",
            },
            X86_64::RDI => match width {
                Width::Byte => "dil",
                Width::Word => "di",
                Width::Dword => "edi",
                Width::Qword => "rdi",
            },
            X86_64::RBP => match width {
                Width::Byte => "bpl",
                Width::Word => "bp",
                Width::Dword => "ebp",
                Width::Qword => "rbp",
            },
            X86_64::RSP => match width {
                Width::Byte => "spl",
                Width::Word => "sp",
                Width::Dword => "esp",
                Width::Qword => "rsp",
            },
            X86_64::R8 => match width {
                Width::Byte => "r8b",
                Width::Word => "r8w",
                Width::Dword => "r8d",
                Width::Qword => "r8",
            },
            X86_64::R9 => match width {
                Width::Byte => "r9b",
                Width::Word => "r9w",
                Width::Dword => "r9d",
                Width::Qword => "r9",
            },
            X86_64::R10 => match width {
                Width::Byte => "r10b",
                Width::Word => "r10w",
                Width::Dword => "r10d",
                Width::Qword => "r10",
            },
            X86_64::R11 => match width {
                Width::Byte => "r11b",
                Width::Word => "r11w",
                Width::Dword => "r11d",
                Width::Qword => "r11",
            },
            X86_64::R12 => match width {
                Width::Byte => "r12b",
                Width::Word => "r12w",
                Width::Dword => "r12d",
                Width::Qword => "r12",
            },
            X86_64::R13 => match width {
                Width::Byte => "r13b",
                Width::Word => "r13w",
                Width::Dword => "r13d",
                Width::Qword => "r13",
            },
            X86_64::R14 => match width {
                Width::Byte => "r14b",
                Width::Word => "r14w",
                Width::Dword => "r14d",
                Width::Qword => "r14",
            },
            X86_64::R15 => match width {
                Width::Byte => "r15b",
                Width::Word => "r15w",
                Width::Dword => "r15d",
                Width::Qword => "r15",
            },
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
            mac_os: matches!(target, TargetPair::X86_64macOS),
            state: String::default(),
            pool: module.symbols().clone(),
            label_count: 0,
            fixed_interval_comments,
        };

        emitter.emit(module)
    }

    fn object(module: &MIRModule<Inst>, format: Self::ObjectCodeFormat) -> Vec<u8> {
        todo!()
    }
}

struct AsmEmitter {
    mode: X86_64Assembly,
    mac_os: bool,
    state: String,
    pool: StringPool,
    label_count: usize,
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
            let name = into_mac_os_symbol_name(
                module
                    .symbols()
                    .get(function.name())
                    .expect("should have name"),
                self.mac_os,
            );

            self.emit_function(&name, function);
        }

        if self.mode == X86_64Assembly::MASM {
            self.state += "END\n"
        }

        self.state
    }

    fn emit_global_symbols(&mut self, module: &MIRModule<Inst>) {
        let strings = module.symbols();

        for (function, frame) in module.functions() {
            let name = into_mac_os_symbol_name(
                strings.get(function.name()).expect("should have name"),
                self.mac_os,
            );

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

    fn emit_function_name(&mut self, name: &str, defined_by_caller: &[PReg]) {
        let name = match self.mode {
            X86_64Assembly::GNU | X86_64Assembly::GNUIntel => {
                self.state += "    .text\n";

                format!("{name}:")
            }
            X86_64Assembly::NASM => {
                self.state += "    section .text\n";

                format!("{name}:")
            }
            X86_64Assembly::MASM => {
                self.state += "_TEXT SEGMENT\n";

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

    fn emit_function(&mut self, name: &str, function: &MIRFunction<Inst>) {
        let mut block_names = SecondaryMap::with_capacity(function.program_order().len());
        let (fixed_begin_at, fixed_end_at, defined_by_caller) = self.fixed_begin_end(function);
        let mut i = 0usize;

        self.emit_function_name(name, &defined_by_caller);

        // skip 1, we don't want to put a label on the first block
        for &block in function.program_order().iter().skip(1) {
            let curr = self.label_count;
            let next = mem::replace(&mut self.label_count, curr + 1);

            block_names.insert(block, format!(".L{next}"));
        }

        for &block in function.program_order().iter() {
            if let Some(name) = block_names.get(block) {
                self.state += name;
                self.state += ":\n";
            }

            for &inst in function.block(block) {
                let asm = self.emit_inst(inst, &block_names);

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
    }

    fn fixed_begin_end(
        &mut self,
        function: &MIRFunction<Inst>,
    ) -> (
        SaHashMap<usize, SmallVec<[PReg; 2]>>,
        SaHashMap<usize, SmallVec<[PReg; 2]>>,
        Vec<PReg>,
    ) {
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

    fn emit_inst(&self, inst: Inst, block_names: &SecondaryMap<MIRBlock, String>) -> String {
        match inst {
            Inst::Nop(_) => "nop".into(),
            Inst::Mov(mov) => self.emit_mov(mov),
            Inst::Movsx(movsx) => self.emit_movsx(movsx),
            Inst::Movzx(movzx) => self.emit_movzx(movzx),
            Inst::MovStore(mov) => self.emit_mov_store(mov),
            Inst::Movabs(movabs) => self.emit_movabs(movabs),
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
            Inst::Cmp(cmp) => self.emit_cmp(cmp),
            Inst::Test(test) => self.emit_test(test),
            Inst::Set(set) => self.emit_set(set),
            Inst::Push(push) => self.emit_push(push),
            Inst::Pop(pop) => self.emit_pop(pop),
            Inst::Call(call) => self.emit_call(call),
            Inst::IndirectCall(indirectcall) => self.emit_indirectcall(indirectcall),
            Inst::Jump(jump) => self.emit_jump(jump, block_names),
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
            X86_64Assembly::NASM => match width {
                Width::Byte => "byte ",
                Width::Word => "word ",
                Width::Dword => "dword ",
                Width::Qword => "qword ",
            },
            X86_64Assembly::GNUIntel | X86_64Assembly::MASM => match width {
                Width::Byte => "byte ptr ",
                Width::Word => "word ptr ",
                Width::Dword => "dword ptr ",
                Width::Qword => "qword ptr ",
            },
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
            match width {
                Width::Byte => "b",
                Width::Word => "w",
                Width::Dword => "l",
                Width::Qword => "q",
            }
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

    fn emit_set(&self, set: Set) -> String {
        let dest = self.emit_reg(set.dest.to_reg(), Width::Byte);
        let suffix = Self::condition_code_suffix(set.condition);

        format!("set{suffix} {dest}")
    }

    fn emit_jump(&self, jump: Jump, block_names: &SecondaryMap<MIRBlock, String>) -> String {
        let name = match jump.target {
            JumpTarget::Global(name) => self.pool.get(name).unwrap(),
            JumpTarget::Local(bb) => &block_names[bb],
        };

        let suffix = match jump.condition {
            Some(cc) => Self::condition_code_suffix(cc),
            None => "mp",
        };

        format!("j{suffix} {name}")
    }
}
