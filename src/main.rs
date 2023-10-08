use ops::AddressingMode;

pub mod ops;

#[macro_use]
extern crate lazy_static;

use bitflags::bitflags;

fn main() {
    println!("{:8b}", 8 as i8);
    println!("{:b}", (8 as i8).wrapping_neg() as u8);
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

enum Instruction {
    ADC(u16), // Add with Carry
    SBC(u16), // Subtract with Carry
    AND(u16), // Logical AND
    BRK, // Force Interrupt
    LDA(u16), // Load Accumulator
    STA(u16), // Store Accumulator
    TAX, // Transfer accumulator to x,
    INX, // Increment X Register
}

struct CPU {
    register_a: u8, // Accumulator, stores the results of arithmetic, logic, and memory access operations
    register_x: u8, // Used as an offset in specific memory addressing modes, can be used for auxiliary storage needs
    register_y: u8, // Similar use case to register_x
    status: CpuFlags,
    program_counter: u16,
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
            memory: [0; 0xFFFF]
        }
    }

    fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = CpuFlags::default();

        // Address at 0xFFFC defined to contain pointer to where program should start
        self.program_counter = self.mem_read_u16((0xFFFC));
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        self.status.set(CpuFlags::ZERO, result == 0);

        // If result value is negative (8th bit set to 1)
        self.status.set(CpuFlags::NEGATIVE, result & 0b1000_0000 != 0);
    }

    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_read_u16(&self, addr: u16) -> u16 {
        let lo = self.memory[addr as usize];
        let hi = self.memory[(addr + 1) as usize];
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
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage  => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }
            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }

    }

    fn load_instruction(&mut self) -> Instruction {
        let code = self.next_u8();
        let opcode = ops::OPCODES_MAP.get(&code).unwrap();
        let instruction = match opcode.op {
            ops::OP::ADC => {
                let addr = self.get_operand_address(&opcode.mode);
                Instruction::ADC(addr)
            },
            ops::OP::SBC => {
                let addr = self.get_operand_address(&opcode.mode);
                Instruction::SBC(addr)
            }
            ops::OP::AND => {
                let addr = self.get_operand_address(&opcode.mode);
                Instruction::AND(addr)
            }
            ops::OP::BRK => Instruction::BRK,
            ops::OP::LDA => {
                let addr = self.get_operand_address(&opcode.mode);
                Instruction::LDA(addr)
            },
            ops::OP::INX => Instruction::INX,
            ops::OP::NOP => todo!(),
            ops::OP::STA => {
                let addr = self.get_operand_address(&opcode.mode);
                Instruction::STA(addr)
            },
            ops::OP::TAX => Instruction::TAX,
        };
        self.program_counter += (opcode.len - 1) as u16;
        instruction
    }

    fn run(&mut self) {
        loop {
            let instruction = self.load_instruction();
            match instruction {
                Instruction::BRK => return,
                Instruction::LDA(param) => self.lda(param),
                Instruction::TAX => self.tax(),
                Instruction::INX => self.inx(),
                Instruction::ADC(addr) => self.adc(addr),
                Instruction::SBC(addr) => todo!(),
                Instruction::AND(addr) => self.and(addr),
                Instruction::STA(addr) => self.sta(addr),
            }
        }
    }

    fn set_register_a(&mut self, byte: u8) {
        self.register_a = byte;
        self.update_zero_and_negative_flags(self.register_a);
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

    fn and(&mut self, addr: u16) {
        let data = self.mem_read(addr);
        self.set_register_a(self.register_a & data);
    }

    fn lda(&mut self, addr: u16) {
        let byte = self.mem_read(addr);
        self.register_a = byte;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn inx(&mut self) {
        if self.register_x == 0b1111_1111 {
            self.register_x = 0 // overflow to 0
        } else {
            self.register_x += 1;
        }

        self.update_zero_and_negative_flags(self.register_x)
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