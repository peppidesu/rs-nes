
////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy)]
pub struct Opcode {    
    instruction: Instruction,
    addressing_mode: AddressingMode,
}

impl Opcode {
    pub fn from(opcode: u8) -> Option<Self> {
        OPCODES[opcode as usize]
    }
    pub fn execute(&self, cpu: &mut Cpu) {        
        self.instruction.execute(
            cpu, 
            &self.addressing_mode
        );        
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy)]
pub enum AddressingMode {
    Implied,
    Accumulator,
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Relative,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Indirect,
    IndexedIndirect,
    IndirectIndexed,
}

fn add_index_page_crossed(addr: u16, offset: u8) -> (u16, bool) {
    let new_addr = addr.wrapping_add(offset as u16);
    (new_addr, (new_addr & 0xFF00) != (addr & 0xFF00))
}

impl AddressingMode {
    pub fn size(&self) -> u8 {
        match self {
            Self::Implied => 1,
            Self::Accumulator => 1,
            Self::Immediate => 2,
            Self::ZeroPage => 2,
            Self::ZeroPageX => 2,
            Self::ZeroPageY => 2,
            Self::Relative => 2,
            Self::Absolute => 3,
            Self::AbsoluteX => 3,
            Self::AbsoluteY => 3,
            Self::Indirect => 3,
            Self::IndexedIndirect => 2,
            Self::IndirectIndexed => 2,
        }
    }

    fn read_addr(&self, cpu: &mut Cpu) -> u16 {
        match self {
            AddressingMode::Absolute => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                addr_lo | (addr_hi << 8)
            },
            AddressingMode::Indirect => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                let indirect_lo = cpu.address_space.read(address) as u16;
                let indirect_hi = cpu.address_space.read(address + 1) as u16;
                indirect_lo | (indirect_hi << 8)
            }
            _ => panic!("Invalid addressing mode for read16"),
        }
    }

    fn read(&self, cpu: &mut Cpu) -> u8 {
        match self {
            AddressingMode::Implied => 0,
            AddressingMode::Accumulator => cpu.a,
            AddressingMode::Immediate => {
                cpu.address_space.read(cpu.pc + 1)                
            },
            AddressingMode::ZeroPage => {
                let address = cpu.address_space.read(cpu.pc + 1) as u16;
                cpu.address_space.read(address)
            },
            AddressingMode::ZeroPageX => {
                let address = cpu.address_space.read(cpu.pc + 1).wrapping_add(cpu.x) as u16;
                cpu.address_space.read(address)
            },
            AddressingMode::ZeroPageY => {
                let address = cpu.address_space.read(cpu.pc + 1).wrapping_add(cpu.y) as u16;
                cpu.address_space.read(address)
            },
            AddressingMode::Relative => {
                let offset = cpu.address_space.read(cpu.pc + 1);
                cpu.cycles += 1;
                
                let pc_lo = cpu.pc & 0x00FF;

                if pc_lo.wrapping_add_signed(offset as i16) & 0xFF00 != 0 { 
                    cpu.cycles += 1;
                }
                
                offset
            },
            AddressingMode::Absolute => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                cpu.address_space.read(address)
            },
            AddressingMode::AbsoluteX => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                let (new_addr, page_crossed) = add_index_page_crossed(address, cpu.x);

                if page_crossed {
                    cpu.cycles += 1;
                }

                cpu.address_space.read(new_addr)
            },
            AddressingMode::AbsoluteY => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                let (new_addr, page_crossed) = add_index_page_crossed(address, cpu.y);

                if page_crossed {
                    cpu.cycles += 1;
                }

                cpu.address_space.read(new_addr)
            },
            AddressingMode::Indirect => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                let indirect_lo = cpu.address_space.read(address) as u16;
                let indirect_hi = cpu.address_space.read(address + 1) as u16;
                let indirect = indirect_lo | (indirect_hi << 8);

                cpu.address_space.read(indirect)
            },
            AddressingMode::IndexedIndirect => {
                let zp_addr = cpu.address_space.read(cpu.pc + 1).wrapping_add(cpu.x) as u16;
                let indirect_lo = cpu.address_space.read(zp_addr) as u16;
                let indirect_hi = cpu.address_space.read(zp_addr + 1) as u16;
                let indirect = indirect_lo | (indirect_hi << 8);

                cpu.address_space.read(indirect)
            },
            AddressingMode::IndirectIndexed => {
                let zp_addr = cpu.address_space.read(cpu.pc + 1) as u16;
                let indirect_lo = cpu.address_space.read(zp_addr) as u16;
                let indirect_hi = cpu.address_space.read(zp_addr + 1) as u16;
                let indirect = indirect_lo | (indirect_hi << 8);

                let (new_addr, page_crossed) = add_index_page_crossed(indirect, cpu.y);

                if page_crossed {
                    cpu.cycles += 1;
                }

                cpu.address_space.read(new_addr)
            }
        }
    }
    
    fn write(&self, cpu: &mut Cpu, value: u8) {
        match self {
            AddressingMode::Implied => {},
            AddressingMode::Accumulator => cpu.a = value,
            AddressingMode::Immediate => {},
            AddressingMode::ZeroPage => {
                let address = cpu.address_space.read(cpu.pc + 1) as u16;
                cpu.address_space.write(address, value);
            },
            AddressingMode::ZeroPageX => {
                let address = cpu.address_space.read(cpu.pc + 1).wrapping_add(cpu.x) as u16;
                cpu.address_space.write(address, value);
            },
            AddressingMode::ZeroPageY => {
                let address = cpu.address_space.read(cpu.pc + 1).wrapping_add(cpu.y) as u16;
                cpu.address_space.write(address, value);
            },
            AddressingMode::Relative => {},
            AddressingMode::Absolute => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                cpu.address_space.write(address, value);
            },
            AddressingMode::AbsoluteX => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                let (new_addr, _) = add_index_page_crossed(address, cpu.x);

                cpu.address_space.write(new_addr, value);
            },
            AddressingMode::AbsoluteY => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                let (new_addr, _) = add_index_page_crossed(address, cpu.y);

                cpu.address_space.write(new_addr, value);
            },
            AddressingMode::Indirect => {
                let addr_lo = cpu.address_space.read(cpu.pc + 1) as u16;
                let addr_hi = cpu.address_space.read(cpu.pc + 2) as u16;
                let address = addr_lo | (addr_hi << 8);

                let indirect_lo = cpu.address_space.read(address) as u16;
                let indirect_hi = cpu.address_space.read(address + 1) as u16;
                let indirect = indirect_lo | (indirect_hi << 8);

                cpu.address_space.write(indirect, value);
            },
            AddressingMode::IndexedIndirect => {
                let zp_addr = cpu.address_space.read(cpu.pc + 1).wrapping_add(cpu.x) as u16;
                let indirect_lo = cpu.address_space.read(zp_addr) as u16;
                let indirect_hi = cpu.address_space.read(zp_addr + 1) as u16;
                let indirect = indirect_lo | (indirect_hi << 8);

                cpu.address_space.write(indirect, value);
            },
            AddressingMode::IndirectIndexed => {
                let zp_addr = cpu.address_space.read(cpu.pc + 1) as u16;
                let indirect_lo = cpu.address_space.read(zp_addr) as u16;
                let indirect_hi = cpu.address_space.read(zp_addr + 1) as u16;
                let indirect = indirect_lo | (indirect_hi << 8);

                let (new_addr, _) = add_index_page_crossed(indirect, cpu.y);

                cpu.address_space.write(new_addr, value);
            },
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy)]
pub enum Instruction {
    ADC, AND, ASL, BCC, BCS, BEQ, BIT, BMI, 
    BNE, BPL, BRK, BVC, BVS, CLC, CLD, CLI, 
    CLV, CMP, CPX, CPY, DEC, DEX, DEY, EOR, 
    INC, INX, INY, JMP, JSR, LDA, LDX, LDY, 
    LSR, NOP, ORA, PHA, PHP, PLA, PLP, ROL, 
    ROR, RTI, RTS, SBC, SEC, SED, SEI, STA, 
    STX, STY, TAX, TAY, TSX, TXA, TXS, TYA
}

impl Instruction {
    pub fn execute(&self, cpu: &mut Cpu, addr_mode: &AddressingMode) {
        
        match self {
            Instruction::ADC => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_adc(value);
                cpu.a = result;
                cpu.pc += addr_mode.size() as u16;
            },
            Instruction::AND => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_and(value);
                cpu.a = result;
                cpu.pc += addr_mode.size() as u16;
            },
            Instruction::ASL => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_asl(value);
                addr_mode.write(cpu, result);
                cpu.pc += addr_mode.size() as u16;
            },
            Instruction::BCC => {
                if cpu.status & 0x01 == 0 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::BCS => {
                if cpu.status & 0x01 == 1 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::BEQ => {
                if cpu.status & 0x02 == 1 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::BIT => {
                let value = addr_mode.read(cpu);
                cpu.alu_and(value);
                cpu.pc += addr_mode.size() as u16;
            },
            Instruction::BMI => {
                if cpu.status & 0x80 == 1 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::BNE => {
                if cpu.status & 0x02 == 0 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::BPL => {
                if cpu.status & 0x80 == 0 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::BRK => {
                cpu.push(((cpu.pc >> 8) & 0xFF) as u8);
                cpu.push((cpu.pc & 0xFF) as u8);
                cpu.push(cpu.status | 0x10);
                cpu.set_flag(Flag::InterruptDisable, true);
                cpu.pc = cpu.address_space.read(0xFFFE) as u16
                       | (cpu.address_space.read(0xFFFF) as u16) << 8;
            },
            Instruction::BVC => {
                if cpu.status & 0x40 == 0 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::BVS => {
                if cpu.status & 0x40 == 1 {
                    cpu.cycles += 1;
                    let offset = addr_mode.read(cpu) as i16;
                    let pc = cpu.pc.wrapping_add_signed(offset);
                    cpu.pc = pc;
                }
            },
            Instruction::CLC => {
                cpu.set_flag(Flag::Carry, false);
            },
            Instruction::CLD => {
                cpu.set_flag(Flag::Decimal, false);
            },
            Instruction::CLI => {
                cpu.set_flag(Flag::InterruptDisable, false);
            },
            Instruction::CLV => {
                cpu.set_flag(Flag::Overflow, false);
            },
            Instruction::CMP => {
                let value = addr_mode.read(cpu);
                let result = cpu.a.wrapping_sub(value);
                cpu.set_flag(Flag::Carry, cpu.a >= value);
                cpu.set_nz_flags(result);
            },
            Instruction::CPX => {
                let value = addr_mode.read(cpu);
                let result = cpu.x.wrapping_sub(value);
                cpu.set_flag(Flag::Carry, cpu.x >= value);
                cpu.set_nz_flags(result);
            },
            Instruction::CPY => {
                let value = addr_mode.read(cpu);
                let result = cpu.y.wrapping_sub(value);
                cpu.set_flag(Flag::Carry, cpu.y >= value);
                cpu.set_nz_flags(result);
            },
            Instruction::DEC => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_dec(value);
                addr_mode.write(cpu, result);
            },
            Instruction::DEX => {
                cpu.x = cpu.alu_dec(cpu.x);
            },
            Instruction::DEY => {
                cpu.y = cpu.alu_dec(cpu.y);
            },
            Instruction::EOR => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_eor(value);
                cpu.a = result;
            },
            Instruction::INC => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_inc(value);
                addr_mode.write(cpu, result);
            },
            Instruction::INX => {
                cpu.x = cpu.alu_inc(cpu.x);
            },
            Instruction::INY => {
                cpu.y = cpu.alu_inc(cpu.y);
            },
            Instruction::JMP => {
                let address = addr_mode.read_addr(cpu);
                cpu.pc = address;
            },
            Instruction::JSR => {
                let address = addr_mode.read_addr(cpu);
                cpu.push(((cpu.pc >> 8) & 0xFF) as u8);
                cpu.push((cpu.pc & 0xFF) as u8);
                cpu.pc = address;
            },
            Instruction::LDA => {
                let value = addr_mode.read(cpu);
                cpu.a = value;
            },
            Instruction::LDX => {
                let value = addr_mode.read(cpu);
                cpu.x = value;
            },
            Instruction::LDY => {
                let value = addr_mode.read(cpu);
                cpu.y = value;
            },
            Instruction::LSR => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_lsr(value);
                addr_mode.write(cpu, result);
            },
            Instruction::NOP => {
                // Do nothing
            },
            Instruction::ORA => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_or(value);
                cpu.a = result;
            },
            Instruction::PHA => {
                cpu.push(cpu.a);
            },
            Instruction::PHP => {
                cpu.push(cpu.status | Flag::Break as u8 | Flag::Unused as u8);
            },
            Instruction::PLA => {
                cpu.a = cpu.pull();
                cpu.set_nz_flags(cpu.a);
            },
            Instruction::PLP => {
                cpu.status = cpu.pull() 
                    & !(Flag::Break as u8) 
                    & !(Flag::Unused as u8);
            },
            Instruction::ROL => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_rol(value);
                addr_mode.write(cpu, result);
            },
            Instruction::ROR => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_ror(value);
                addr_mode.write(cpu, result);
            },
            Instruction::RTI => {
                cpu.status = cpu.pull();
                cpu.set_flag(Flag::Break, false);
                cpu.set_flag(Flag::Unused, false);

                let lo = cpu.pull() as u16;
                let hi = cpu.pull() as u16;
                cpu.pc = lo | (hi << 8);
            },
            Instruction::RTS => {
                let lo = cpu.pull() as u16;
                let hi = cpu.pull() as u16;
                cpu.pc = lo | (hi << 8);
            },
            Instruction::SBC => {
                let value = addr_mode.read(cpu);
                let result = cpu.alu_sbc(value);
                cpu.a = result;
            },
            Instruction::SEC => {
                cpu.set_flag(Flag::Carry, true);
            },
            Instruction::SED => {
                cpu.set_flag(Flag::Decimal, true);
            },
            Instruction::SEI => {
                cpu.set_flag(Flag::InterruptDisable, true);
            },
            Instruction::STA => {
                let value = cpu.a;
                addr_mode.write(cpu, value);
            },
            Instruction::STX => {
                let value = cpu.x;
                addr_mode.write(cpu, value);
            },
            Instruction::STY => {
                let value = cpu.y;
                addr_mode.write(cpu, value);
            },
            Instruction::TAX => {
                cpu.x = cpu.a;
                cpu.set_nz_flags(cpu.x);
            },
            Instruction::TAY => {
                cpu.y = cpu.a;
                cpu.set_nz_flags(cpu.y);
            },
            Instruction::TSX => {
                cpu.x = cpu.sp;
                cpu.set_nz_flags(cpu.x);
            },
            Instruction::TXA => {
                cpu.a = cpu.x;
                cpu.set_nz_flags(cpu.a);
            },
            Instruction::TXS => {
                cpu.sp = cpu.x;
                cpu.set_nz_flags(cpu.sp);
            },
            Instruction::TYA => {
                cpu.a = cpu.y;
                cpu.set_nz_flags(cpu.a);
            },
        }
    
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub enum Flag {
    Carry               = (1 << 0),
    Zero                = (1 << 1),
    InterruptDisable    = (1 << 2),
    Decimal             = (1 << 3),
    Break               = (1 << 4),
    Unused              = (1 << 5),
    Overflow            = (1 << 6),
    Negative            = (1 << 7),
}

pub struct Cpu {
    a: u8,
    x: u8,
    y: u8,
    pc: u16,
    sp: u8,
    status: u8,
    address_space: AddressSpace,
    cycles: u8,
}

impl Cpu {
    /// Set a flag in the status register to the given value
    pub fn set_flag(&mut self, flag: Flag, value: bool) {
        match flag {
            Flag::Carry => {
                self.status = self.status & 0b_1111_1110 | value as u8;
            },
            Flag::Zero => {
                self.status = self.status & 0b_1111_1101 | (value as u8) << 1;
            },
            Flag::InterruptDisable => {
                self.status = self.status & 0b_1111_1011 | (value as u8) << 2;
            },
            Flag::Decimal => {
                self.status = self.status & 0b_1111_0111 | (value as u8) << 3;
            },
            Flag::Break => {                
                self.status = self.status & 0b_1110_1111 | (value as u8) << 4;
            },
            Flag::Unused => {
                self.status = self.status & 0b_1101_1111 | (value as u8) << 5;
            },
            Flag::Overflow => {
                self.status = self.status & 0b_1011_1111 | (value as u8) << 6;
            },
            Flag::Negative => {
                self.status = self.status & 0b_0111_1111 | (value as u8) << 7;
            },
        }
    }

    /// Set the zero and negative flags based on the value
    pub fn set_nz_flags(&mut self, value: u8) {
        self.set_flag(Flag::Zero, value == 0);
        self.set_flag(Flag::Negative, value & 0x80 != 0);
    }

    /// ALU add with carry; sets flags and returns result
    pub fn alu_adc(&mut self, value: u8) -> u8 {
        let carry = self.status & Flag::Carry as u8;

        let result = self.a.wrapping_add(value);
        self.set_flag(Flag::Carry, result < self.a);
        let result = result.wrapping_add(carry);

        // V is set when the sign of the result is different from that of both A and the operand
        self.set_flag(Flag::Overflow, (self.a ^ result) & (value ^ result) & 0x80 != 0);
        self.set_nz_flags(result);
        result
    }

    /// ALU subtract with carry; sets flags and returns result
    pub fn alu_sbc(&mut self, value: u8) -> u8 {
        let carry = self.status & Flag::Carry as u8;
        let result = self.a.wrapping_sub(value);
        self.set_flag(Flag::Carry, result > self.a);
        let result = result.wrapping_sub(carry);

        // V is set when the sign of the result is different from that of both A and the operand
        self.set_flag(Flag::Overflow, (self.a ^ result) & (!value ^ result) & 0x80 != 0);
        self.set_nz_flags(result);
        result
    }

    /// ALU increment; increments value, sets flags and returns result
    pub fn alu_inc(&mut self, value: u8) -> u8 {
        let result = value.wrapping_add(1);
        self.set_nz_flags(result);
        result
    }

    /// ALU decrement; decrements value, sets flags and returns result
    pub fn alu_dec(&mut self, value: u8) -> u8 {
        let result = value.wrapping_sub(1);
        self.set_nz_flags(result);
        result
    }

    /// ALU AND operation; sets flags and returns result
    pub fn alu_and(&mut self, value: u8) -> u8 {
        let result = self.a & value;
        self.set_nz_flags(result);
        result
    }

    /// ALU OR operation; sets flags and returns result
    pub fn alu_or(&mut self, value: u8) -> u8 {
        let result = self.a | value;
        self.set_nz_flags(result);
        result
    }

    /// ALU exclusive OR operation; sets flags and returns result
    pub fn alu_eor(&mut self, value: u8) -> u8 {
        let result = self.a ^ value;
        self.set_nz_flags(result);
        result
    }

    /// ALU arithmetic shift left; sets flags and returns result
    pub fn alu_asl(&mut self, value: u8) -> u8 {
        let result = value << 1;
        self.set_flag(Flag::Carry, value & 0x80 != 0);
        self.set_nz_flags(result);
        result
    }
    
    /// ALU logical shift right; sets flags and returns result
    pub fn alu_lsr(&mut self, value: u8) -> u8 {
        let result = value >> 1;
        self.set_flag(Flag::Carry, value & 0x01 != 0);
        self.set_nz_flags(result);
        result
    }

    /// ALU rotate left; sets flags and returns result
    pub fn alu_rol(&mut self, value: u8) -> u8 {
        let carry = self.status & 0x01;
        let result = (value << 1) | carry;
        self.set_flag(Flag::Carry, value & 0x80 != 0);
        self.set_nz_flags(result);
        result
    }

    /// ALU rotate right; sets flags and returns result
    pub fn alu_ror(&mut self, value: u8) -> u8 {
        let carry = self.status & 0x01;
        let result = (value >> 1) | (carry << 7);
        self.set_flag(Flag::Carry, value & 0x01 != 0);
        self.set_nz_flags(result);
        result
    }

    /// ALU push; sets flags and returns result
    pub fn push(&mut self, value: u8) {
        self.address_space.write(0x0100 | self.sp as u16, value);
        self.sp = self.sp.wrapping_sub(1);
    }

    /// ALU pull; sets flags and returns result
    pub fn pull(&mut self) -> u8 {
        self.sp = self.sp.wrapping_add(1);
        self.address_space.read(0x0100 | self.sp as u16)
    }

    /// Reset the CPU
    pub fn reset(&mut self) {
        self.a = 0;
        self.x = 0;
        self.y = 0;
        self.sp = 0xFD;
        self.status = 0 | Flag::Unused as u8;

        self.pc = self.address_space.read(0xFFFC) as u16 
                | (self.address_space.read(0xFFFD) as u16) << 8;
        self.cycles = 8;
    }

    pub fn step(&mut self) {
        if self.cycles == 0 {
            let opcode = self.address_space.read(self.pc);
            self.cycles = CYCLES[opcode as usize];

            let opcode = Opcode::from(opcode).unwrap();
            opcode.execute(self);
            
        }        
        self.cycles -= 1;
    }

    pub fn irq(&mut self) {
        if self.status & Flag::InterruptDisable as u8 == 0 {
            self.push(((self.pc >> 8) & 0xFF) as u8);
            self.push((self.pc & 0xFF) as u8);
            
            self.set_flag(Flag::Break, false);
            self.set_flag(Flag::Unused, true);
            self.set_flag(Flag::InterruptDisable, true);
            self.push(self.status);

            let lo = self.address_space.read(0xFFFE) as u16;
            let hi = self.address_space.read(0xFFFF) as u16;

            self.pc = (hi << 8) | lo;
            self.cycles = 7;
        }
    }

    pub fn nmi(&mut self) {
        self.push(((self.pc >> 8) & 0xFF) as u8);
        self.push((self.pc & 0xFF) as u8);
        
        self.set_flag(Flag::Break, false);
        self.set_flag(Flag::Unused, true);
        self.set_flag(Flag::InterruptDisable, true);
        self.push(self.status);

        let lo = self.address_space.read(0xFFFA) as u16;
        let hi = self.address_space.read(0xFFFB) as u16;

        self.pc = (hi << 8) | lo;

        self.cycles = 8;
    }

    
}

////////////////////////////////////////////////////////////////////////////////////////////////////

struct AddressSpace {
    memory: [u8; 0x800],
}

impl AddressSpace {
    fn read(&self, addr: u16) -> u8 {
        if addr <= 0x1fff {
            self.memory[addr as usize & 0x7FF]
        }
        else {
            unimplemented!()
        }
    }

    fn write(&mut self, addr: u16, value: u8) {
        self.memory[addr as usize] = value;
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

// Main

////////////////////////////////////////////////////////////////////////////////////////////////////

fn main() {
    println!("Hello, world!");
}

////////////////////////////////////////////////////////////////////////////////////////////////////

// Opcode Table

////////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! opcode_table {
    ($($opcode:expr => $instruction:ident $addressing_mode:ident, $cycles:expr);*$(;)?) => {
        pub const OPCODES: [Option<Opcode>; 256] = {
            let mut table = [None; 256];
            $(
                table[$opcode as usize] = Some(Opcode {                    
                    instruction: Instruction::$instruction,
                    addressing_mode: AddressingMode::$addressing_mode,
                });                
            )*
            table
        };
        pub const CYCLES: [u8; 256] = {
            let mut table = [0; 256];
            $(
                table[$opcode as usize] = $cycles;
            )*
            table
        };
    };
}

opcode_table! {
//  opcode  instruction        cycles
    0x69 => ADC Immediate,          2;          
    0x65 => ADC ZeroPage,           3;
    0x75 => ADC ZeroPageX,          4;          
    0x6D => ADC Absolute,           4;
    0x7D => ADC AbsoluteX,          4;          
    0x79 => ADC AbsoluteY,          4;
    0x61 => ADC IndexedIndirect,    6;    
    0x71 => ADC IndirectIndexed,    5;

    0x29 => AND Immediate,          2;          
    0x25 => AND ZeroPage,           3;
    0x35 => AND ZeroPageX,          4;          
    0x2D => AND Absolute,           4;
    0x3D => AND AbsoluteX,          4;          
    0x39 => AND AbsoluteY,          4;
    0x21 => AND IndexedIndirect,    6;    
    0x31 => AND IndirectIndexed,    5;
    
    0x0A => ASL Accumulator,        2;        
    0x06 => ASL ZeroPage,           5;
    0x16 => ASL ZeroPageX,          6;          
    0x0E => ASL Absolute,           6;
    0x1E => ASL AbsoluteX,          7;          
    
    0x90 => BCC Relative,           2;
    
    0xB0 => BCS Relative,           2;           
    
    0xF0 => BEQ Relative,           2;
    
    0x24 => BIT ZeroPage,           3;           
    0x2C => BIT Absolute,           4;
    
    0x30 => BMI Relative,           2;           
    
    0xD0 => BNE Relative,           2;
    
    0x10 => BPL Relative,           2;           
    
    0x00 => BRK Implied,            7;
    
    0x50 => BVC Relative,           2;           
    
    0x70 => BVS Relative,           2;
    
    0x18 => CLC Implied,            2;            
    
    0xD8 => CLD Implied,            2;
    
    0x58 => CLI Implied,            2;            
    
    0xB8 => CLV Implied,            2;
    
    0xC9 => CMP Immediate,          2;          
    0xC5 => CMP ZeroPage,           3;
    0xD5 => CMP ZeroPageX,          4;          
    0xCD => CMP Absolute,           4;
    0xDD => CMP AbsoluteX,          4;          
    0xD9 => CMP AbsoluteY,          4;
    0xC1 => CMP IndexedIndirect,    6;    
    0xD1 => CMP IndirectIndexed,    5;
    
    0xE0 => CPX Immediate,          2;          
    0xE4 => CPX ZeroPage,           3;
    0xEC => CPX Absolute,           4;           
    
    0xC0 => CPY Immediate,          2;
    0xC4 => CPY ZeroPage,           3;           
    0xCC => CPY Absolute,           4;
    
    0xC6 => DEC ZeroPage,           5;           
    0xD6 => DEC ZeroPageX,          6;
    0xCE => DEC Absolute,           6;           
    0xDE => DEC AbsoluteX,          7;
    
    0xCA => DEX Implied,            2;            
    
    0x88 => DEY Implied,            2;
    
    0x49 => EOR Immediate,          2;          
    0x45 => EOR ZeroPage,           3;
    0x55 => EOR ZeroPageX,          4;          
    0x4D => EOR Absolute,           4;
    0x5D => EOR AbsoluteX,          4;          
    0x59 => EOR AbsoluteY,          4;
    0x41 => EOR IndexedIndirect,    6;    
    0x51 => EOR IndirectIndexed,    5;
    
    0xE6 => INC ZeroPage,           5;           
    0xF6 => INC ZeroPageX,          6;
    0xEE => INC Absolute,           6;           
    0xFE => INC AbsoluteX,          7;
    
    0xE8 => INX Implied,            2;            
    
    0xC8 => INY Implied,            2;
    
    0x4C => JMP Absolute,           3;           
    0x6C => JMP Indirect,           5;
    
    0x20 => JSR Absolute,           6;           
    
    0xA9 => LDA Immediate,          2;
    0xA5 => LDA ZeroPage,           3;           
    0xB5 => LDA ZeroPageX,          4;
    0xAD => LDA Absolute,           4;           
    0xBD => LDA AbsoluteX,          4;
    0xB9 => LDA AbsoluteY,          4;          
    0xA1 => LDA IndexedIndirect,    6;
    0xB1 => LDA IndirectIndexed,    5;    
    
    0xA2 => LDX Immediate,          2;
    0xA6 => LDX ZeroPage,           3;           
    0xB6 => LDX ZeroPageY,          4;
    0xAE => LDX Absolute,           4;           
    0xBE => LDX AbsoluteY,          4;
    
    0xA0 => LDY Immediate,          2;          
    0xA4 => LDY ZeroPage,           3;
    0xB4 => LDY ZeroPageX,          4;          
    0xAC => LDY Absolute,           4;
    0xBC => LDY AbsoluteX,          4;          
    
    0x4A => LSR Accumulator,        2;
    0x46 => LSR ZeroPage,           5;           
    0x56 => LSR ZeroPageX,          6;
    0x4E => LSR Absolute,           6;           
    0x5E => LSR AbsoluteX,          7;
    
    0xEA => NOP Implied,            2;            
    
    0x09 => ORA Immediate,          2;
    0x05 => ORA ZeroPage,           3;           
    0x15 => ORA ZeroPageX,          4;
    0x0D => ORA Absolute,           4;           
    0x1D => ORA AbsoluteX,          4;
    0x19 => ORA AbsoluteY,          4;          
    0x01 => ORA IndexedIndirect,    6;
    0x11 => ORA IndirectIndexed,    5;    
    
    0x48 => PHA Implied,            3;
    
    0x08 => PHP Implied,            3;            
    
    0x68 => PLA Implied,            4;
    
    0x28 => PLP Implied,            4;            
    
    0x2A => ROL Accumulator,        2;
    0x26 => ROL ZeroPage,           5;           
    0x36 => ROL ZeroPageX,          6;
    0x2E => ROL Absolute,           6;           
    0x3E => ROL AbsoluteX,          7;
    
    0x6A => ROR Accumulator,        2;        
    0x66 => ROR ZeroPage,           5;
    0x76 => ROR ZeroPageX,          6;          
    0x6E => ROR Absolute,           6;
    0x7E => ROR AbsoluteX,          7;          
    
    0x40 => RTI Implied,            6;
    
    0x60 => RTS Implied,            6;            
    
    0xE9 => SBC Immediate,          2;
    0xE5 => SBC ZeroPage,           3;           
    0xF5 => SBC ZeroPageX,          4;
    0xED => SBC Absolute,           4;           
    0xFD => SBC AbsoluteX,          4;
    0xF9 => SBC AbsoluteY,          4;          
    0xE1 => SBC IndexedIndirect,    6;
    0xF1 => SBC IndirectIndexed,    5;    
    
    0x38 => SEC Implied,            2;

    0xF8 => SED Implied,            2;            

    0x78 => SEI Implied,            2;
    
    0x85 => STA ZeroPage,           3;           
    0x95 => STA ZeroPageX,          4;
    0x8D => STA Absolute,           4;           
    0x9D => STA AbsoluteX,          5;
    0x99 => STA AbsoluteY,          5;          
    0x81 => STA IndexedIndirect,    6;
    0x91 => STA IndirectIndexed,    6;    
    
    0x86 => STX ZeroPage,           3;
    0x96 => STX ZeroPageY,          4;          
    0x8E => STX Absolute,           4;
    
    0x84 => STY ZeroPage,           3;           
    0x94 => STY ZeroPageX,          4;
    0x8C => STY Absolute,           4;           
    
    0xAA => TAX Implied,            2;
    
    0xA8 => TAY Implied,            2;            
    
    0xBA => TSX Implied,            2;
    
    0x8A => TXA Implied,            2;            
    
    0x9A => TXS Implied,            2;
    
    0x98 => TYA Implied,            2;
}