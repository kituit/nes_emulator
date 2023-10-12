use ops::{AddressingMode, OpCode};

pub mod ops;

#[macro_use]
extern crate lazy_static;

use bitflags::bitflags;

const INDIRECT_ADDRESSING_MODE_6502_BUG: bool = true;

const STACK_BOTTOM: u16 = 0x0100;

fn main() {
    // println!("{:8b}", 8 as i8);
    // println!("{:b}", (8 as i8).wrapping_neg() as u8);
    let d: u8 = 0b0100_0000;
    println!("{}", (d & 0b0100_0000) >> 6)
}

bitflags! {
    pub struct CpuFlags: u8 {
        const NEGATIVE          = 0b1000_0000;
        const OVERFLOW          = 0b0100_0000;
        const OTHER             = 0b0010_0000;
        const B                 = 0b0001_0000;
        const DECIMAL           = 0b0000_1000;
        const INTERRUPT_DISABLE = 0b0000_0100;
        const ZERO              = 0b0000_0010;
        const CARRY             = 0b0000_0001;
    }
}

impl Default for CpuFlags {
    fn default() -> Self {
        CpuFlags::from_bits(0b0010_0100).unwrap()
    }
}

struct CPU {
    register_a: u8, // Accumulator, stores the results of arithmetic, logic, and memory access operations
    register_x: u8, // Used as an offset in specific memory addressing modes, can be used for auxiliary storage needs
    register_y: u8, // Similar use case to register_x
    status: CpuFlags,
    program_counter: u16,
    stack_pointer: u8, // Stack grows downwards. Points to the location of where next byte will be stored
    memory: [u8; 0xFFFF]
}

impl CPU {
    fn new() -> Self {
        Self {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: CpuFlags::default(),
            program_counter: 0,
            stack_pointer: 0,
            memory: [0; 0xFFFF]
        }
    }

    fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = CpuFlags::default();

        // Address at 0xFFFC defined to contain pointer to where program should start
        self.program_counter = self.mem_read_u16(0xFFFC);

        // Point to the top of stack and grow downwards;
        self.stack_pointer = 0xFF;
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        self.status.set(CpuFlags::ZERO, result == 0);

        // If result value is negative (7th bit set to 1)
        self.status.set(CpuFlags::NEGATIVE, result & 0b1000_0000 != 0);
    }

    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_read_u16(&self, addr: u16) -> u16 {
        let lo = self.mem_read(addr);
        let hi = self.mem_read(addr.wrapping_add(1));
        u16::from_le_bytes([lo, hi])
    }

    fn mem_write(&mut self, addr: u16, value: u8) {
        self.memory[addr as usize] = value
    }

    fn mem_write_u16(&mut self, addr: u16, value: u16) {
        let [lo, hi] = value.to_le_bytes();
        self.memory[addr as usize] = lo;
        self.memory[(addr + 1) as usize] = hi;
    }

    fn stack_address(&self) -> u16 {
        STACK_BOTTOM + (self.stack_pointer as u16)
    }

    fn stack_push(&mut self, value: u8) {
        self.mem_write(self.stack_address(), value);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1);
    }

    fn stack_push_u16(&mut self, value: u16) {
        let hi = (value >> 8) as u8;
        let lo = (value & 0x00FF) as u8;
        self.stack_push(lo);
        self.stack_push(hi);
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read(self.stack_address())
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let hi = self.stack_pop() as u16;
        let lo = self.stack_pop() as u16;
        hi << 8 | lo
    }

    fn load_program(&mut self, program: &[u8]) {
        // Copy program into ROM (0x8000 and above)
        self.memory[0x8000 .. (0x8000 + program.len())].copy_from_slice(program);
        self.mem_write_u16(0xFFFC, 0x8000); // Assuming we want program to start at 0x8000
    }

    fn load_and_run(&mut self, program: &[u8]) {
        self.load_program(program);
        self.reset();
        self.run();
    }

    fn next_u8(&mut self) -> u8 {
        let byte = self.mem_read(self.program_counter);
        self.program_counter += 1;
        byte
    }

    fn next_u16(&mut self) -> u16 {
        let word = self.mem_read_u16(self.program_counter);
        self.program_counter += 2;
        word
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {

        match mode {
            AddressingMode::Immediate => {
                // Specify 8 bit constant immediately following opcode
                self.program_counter
            },
            AddressingMode::ZeroPage  => {
                // Specify 8 bit address offset XX that yields full address 0x00XX
                // Allows efficient access to 0x0000 to 0x00FF
                let offset = self.mem_read(self.program_counter);
                // 0x0000 | offset as u16
                offset as u16
            }
            AddressingMode::Absolute => {
                // Specify full 16 bit address
                self.mem_read_u16(self.program_counter)
            },
            AddressingMode::ZeroPage_X => {
                // Specify 8 bit address that yields full address when added to current value of
                // x register
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                // Specify 8 bit address that yields full address when added to current value of
                // y register
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }
            AddressingMode::Absolute_X => {
                // Specify full 16 bit address, and then add the current value of the x register
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                // Specify full 16 bit address, and then add the current value of the y register
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }
            AddressingMode::Indirect => {
                // Specify full 16 bit address. This identifies the location of another 16 bit address which
                // is the real target of the instruction
                let indirect_addr = self.mem_read_u16(self.program_counter);

                // Original 6502 CPU has a bug when indirect_addr falls on a page boundary
                // (e.g 0xXXFF for XX in [00, FF]). In this case the LSB is fetched from 0xXXFF
                // but MSB is taken from 0xXX00 (https://www.nesdev.org/obelisk-6502-guide/reference.html#JMP)
                // Bug behaviour is enabled with INDIRECT_ADDRESSING_MODE_6502_BUG Flag
                let addr = if INDIRECT_ADDRESSING_MODE_6502_BUG && (indirect_addr & 0x00FF == 0x00FF) {
                    let lo = self.mem_read(indirect_addr);
                    let hi = self.mem_read(indirect_addr & 0xFF00);
                    (hi as u16) << 8 | (lo as u16)
                } else {
                    self.mem_read_u16(indirect_addr)
                };

                addr
            }
            AddressingMode::Indirect_X => {
                // Specify an 8 bit offset. This yields a 16 bit indirect address when added to the x register.
                // This identifies the location of another 16 bit address which is the real target of the instruction
                let base = self.mem_read(self.program_counter);

                let ptr = base.wrapping_add(self.register_x);
                self.mem_read_u16(ptr as u16)
            }
            AddressingMode::Indirect_Y => {
                // Specify an 8 bit offset XX which yields full 16 bit address 0x00FF. This 16 bit address points
                // to the least significant byte of a 16 bit address. The current value of the y register is then
                // added to yield the final address
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read(base.wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }
            AddressingMode::Relative => {
                // Specify a signed 8 bit relative offset (-128 to +127), which is added to the program counter
                let offset = self.mem_read(self.program_counter) as i8;
                // .wrapping_add(1) to account for the fact that program counter is incremented during execution
                self.program_counter.wrapping_add(1).wrapping_add_signed(offset as i16)
            }
            AddressingMode::Implicit | AddressingMode::Accumulator => {
                panic!("mode {:?} is not supported", mode);
            }
        }

    }

    fn run(&mut self) {
        loop {
            let code = self.next_u8();
            let program_counter_copy = self.program_counter;
            let opcode = ops::OPCODES_MAP.get(&code).unwrap();
            match opcode.op {
                ops::OP::ADC => self.adc(self.get_operand_address(&opcode.mode)),
                ops::OP::SBC => self.sbc(self.get_operand_address(&opcode.mode)),
                ops::OP::INC => self.inc(self.get_operand_address(&opcode.mode)),
                ops::OP::INX => self.inx(),
                ops::OP::INY => self.iny(),
                ops::OP::DEC => self.dec(self.get_operand_address(&opcode.mode)),
                ops::OP::DEX => self.dex(),
                ops::OP::DEY => self.dey(),
                ops::OP::CMP => self.compare(self.register_a, self.get_operand_address(&opcode.mode)),
                ops::OP::CPX => self.compare(self.register_x, self.get_operand_address(&opcode.mode)),
                ops::OP::CPY => self.compare(self.register_y, self.get_operand_address(&opcode.mode)),
                ops::OP::AND => self.and(self.get_operand_address(&opcode.mode)),
                ops::OP::EOR => self.eor(self.get_operand_address(&opcode.mode)),
                ops::OP::ORA => self.ora(self.get_operand_address(&opcode.mode)),
                ops::OP::ASL => {
                    if opcode.mode == AddressingMode::Accumulator {
                        self.asl_accumulator();
                    } else {
                        self.asl(self.get_operand_address(&opcode.mode));
                    }
                }
                ops::OP::LSR => {
                    if opcode.mode == AddressingMode::Accumulator {
                        self.lsr_accumulator();
                    } else {
                        self.lsr(self.get_operand_address(&opcode.mode));
                    }
                }
                ops::OP::ROL => {
                    if opcode.mode == AddressingMode::Accumulator {
                        self.rol_accumulator();
                    } else {
                        self.rol(self.get_operand_address(&opcode.mode));
                    }
                },
                ops::OP::ROR => {
                    if opcode.mode == AddressingMode::Accumulator {
                        self.ror_accumulator();
                    } else {
                        self.ror(self.get_operand_address(&opcode.mode));
                    }
                }
                ops::OP::JMP => self.jmp(self.get_operand_address(&opcode.mode)),
                ops::OP::JSR => self.jsr(&opcode),
                ops::OP::RTS => self.rts(),
                ops::OP::RTI => self.rti(),
                ops::OP::BNE => self.branch(self.get_operand_address(&opcode.mode), !self.status.contains(CpuFlags::ZERO)),
                ops::OP::BRK => return,
                ops::OP::LDA => self.lda(self.get_operand_address(&opcode.mode)),
                ops::OP::NOP => continue,
                ops::OP::STA => self.sta(self.get_operand_address(&opcode.mode)),
                ops::OP::TAX => self.tax(),
            };

            // Update program counter to account for additional bytes read
            // -1 as we have already incremented program counter after reading opcode
            // program_counter_copy == self.program_counter check for if pc was modified during an instruction (e.g jump command)
            // in which case we do not modify further
            if program_counter_copy == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }

        }
    }

    fn set_register_a(&mut self, byte: u8) {
        self.register_a = byte;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn set_register_x(&mut self, byte: u8) {
        self.register_x = byte;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn set_register_y(&mut self, byte: u8) {
        self.register_y = byte;
        self.update_zero_and_negative_flags(self.register_y);
    }


    // Ignoring decimal mode
    // http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
    fn add_to_register_a(&mut self, data: u8) {
        let carry_in = if self.status.contains(CpuFlags::CARRY) { 1 } else { 0 };
        let sum = self.register_a as u16 + data as u16 + carry_in;

        // Carry occurs when sum does not fit in 1 byte register
        let carry_out = sum > 0xFF;
        self.status.set(CpuFlags::CARRY, carry_out);

        let result = sum as u8;

        // Overflow occurs when sum oes not fit in 1 signed byte (i.e 7 bits)
        // e.g Sum two positive numbers overflows to create a negative number
        // See http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
        // for formula to determine overflow
        let overflow = (data ^ result) & (self.register_a ^ result) & 0x80 != 0;
        self.status.set(CpuFlags::OVERFLOW, overflow);

        self.set_register_a(result);
    }

    fn adc(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        self.add_to_register_a(data);
    }

    fn sbc(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        self.add_to_register_a((data as i8).wrapping_neg().wrapping_sub(1) as u8)
    }

    fn inc(&mut self, addr: u16) {
        let byte = self.mem_read(addr);
        let result = byte.wrapping_add(1);
        self.mem_write(addr, result);
        self.update_zero_and_negative_flags(result);
    }

    fn inx(&mut self) {
        self.set_register_x(self.register_x.wrapping_add(1));
    }

    fn iny(&mut self) {
        self.set_register_y(self.register_y.wrapping_add(1));
    }

    fn dec(&mut self, addr: u16) {
        let byte = self.mem_read(addr);
        let result = byte.wrapping_sub(1);
        self.mem_write(addr, result);
        self.update_zero_and_negative_flags(result);
    }

    fn dex(&mut self) {
        self.set_register_x(self.register_x.wrapping_sub(1));
    }

    fn dey(&mut self) {
        self.set_register_y(self.register_y.wrapping_sub(1));
    }

    fn compare(&mut self, value: u8, addr: u16) {
        let compare_with = self.mem_read(addr);
        self.status.set(CpuFlags::CARRY, value >= compare_with);
        self.status.set(CpuFlags::ZERO, value == compare_with);
        self.status.set(CpuFlags::NEGATIVE, value.wrapping_sub(compare_with) & 0b1000_0000 != 0);
    }

    fn and(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        self.set_register_a(self.register_a & data);
    }

    fn eor(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        self.set_register_a(self.register_a ^ data);
    }

    fn ora(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        self.set_register_a(self.register_a | data);
    }

    fn asl(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        // 7th bit is placed in the carry flag
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);
        let shifted = data << 1;
        self.mem_write(addr, shifted);
        self.update_zero_and_negative_flags(shifted);
    }

    fn asl_accumulator(&mut self) {
        let data = self.register_a;
        // 7th bit is placed in the carry flag
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);
        self.set_register_a(data << 1)
    }

    fn lsr(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        // 0th bit gets places in the carry flag
        self.status.set(CpuFlags::CARRY, (data & 0b0000_0001) == 1);
        let shifted = data >> 1;
        self.mem_write(addr, shifted);
        self.update_zero_and_negative_flags(shifted);
    }

    fn lsr_accumulator(&mut self) {
        let data = self.register_a;
        // 0th bit gets places in the carry flag
        self.status.set(CpuFlags::CARRY, (data & 0b0000_0001) == 1);
        self.set_register_a(data >> 1)
    }

    fn rol(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        let carry_in_bit: u8 = if self.status.contains(CpuFlags::CARRY) { 1 } else { 0 };

        // 7th bit moved to carry flag
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);

        let rotated = (data << 1) | carry_in_bit;
        self.mem_write(addr, rotated);
        self.update_zero_and_negative_flags(rotated);
    }

    fn rol_accumulator(&mut self) {
        let data = self.register_a;
        let carry_in_bit: u8 = if self.status.contains(CpuFlags::CARRY) { 1 } else { 0 };

        // 7th bit moved to carry flag
        self.status.set(CpuFlags::CARRY, data >> 7 == 1);

        let rotated = (data << 1) | carry_in_bit;
        self.set_register_a(rotated);
    }

    fn ror(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        let carry_in_bit = if self.status.contains(CpuFlags::CARRY) { 1 << 7 } else { 0 };

        // 0th bit moved to carry flag
        self.status.set(CpuFlags::CARRY, (data & 0b0000_0001) == 1);

        let rotated = (data >> 1) | carry_in_bit;
        self.mem_write(addr, rotated);
        self.update_zero_and_negative_flags(rotated);
    }

    fn ror_accumulator(&mut self) {
        let data = self.register_a;
        let carry_in_bit = if self.status.contains(CpuFlags::CARRY) { 1 << 7 } else { 0 };

        // 0th bit moved to carry flag
        self.status.set(CpuFlags::CARRY, (data & 0b0000_0001) == 1);

        let rotated = (data >> 1) | carry_in_bit;
        self.set_register_a(rotated);
    }

    fn jmp(&mut self, addr: u16) {
        self.program_counter = addr;
    }

    fn jsr(&mut self, op: &OpCode) {
        let next_op_address = self.program_counter + ((op.len - 1) as u16);
        self.stack_push_u16(next_op_address - 1);
        let target_address = self.get_operand_address(&op.mode);
        self.program_counter = target_address;
    }

    fn rts(&mut self) {
        self.program_counter = self.stack_pop_u16() + 1
    }

    fn rti(&mut self) {
        let flags = self.stack_pop();
        self.status = CpuFlags::from_bits_retain(flags);
        self.program_counter = self.stack_pop_u16();
    }

    fn branch(&mut self, addr: u16, condition: bool) {
        if condition {
            self.program_counter = addr;
        }
    }

    fn lda(&mut self, addr: u16) {
        let byte = self.mem_read(addr);
        self.register_a = byte;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn tax(&mut self) {
        self.set_register_x(self.register_a);
    }

    fn sta(&mut self, addr: u16) {
        self.mem_write(addr, self.register_a);
    }

}





#[cfg(test)]
mod test {
   use super::*;

   #[test]
   fn test_0xa9_lda_immediate_load_data() {
       let mut cpu = CPU::new();
       cpu.load_and_run(&[0xa9, 0x05, 0x00]);
       assert_eq!(cpu.register_a, 0x05);
       assert!(!cpu.status.contains(CpuFlags::ZERO));
       assert!(!cpu.status.contains(CpuFlags::NEGATIVE));
   }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[0xa9, 0x00, 0x00]);
        assert!(cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let mut cpu = CPU::new();
        cpu.load_program(&[0xaa, 0x00]);
        cpu.reset();
        cpu.register_a = 10;
        cpu.run();
        assert_eq!(cpu.register_x, 10)
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(&[0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

     #[test]
     fn test_inx_overflow() {
         let mut cpu = CPU::new();
         cpu.load_program(&[0xe8, 0xe8, 0x00]);
         cpu.reset();
         cpu.register_x = 0xff;
         cpu.run();

         assert_eq!(cpu.register_x, 1)
     }
}