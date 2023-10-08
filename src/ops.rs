use std::collections::HashMap;

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

pub enum OP {
    BRK, // Force Interrupt
    NOP,

    // Arithmetic
    ADC, // Add with Carry
    SBC, // Subtract with Carry
    AND, // Logical AND

    LDA, // Load Accumulator
    INX, // Increment X Register

    STA, // Store Accumulator
    TAX, // Transfer accumulator to x,

}

pub struct OpCode {
    pub code: u8,
    pub op: OP,
    pub len: u8,
    pub cycles: u8,
    pub mode: AddressingMode,
}

impl OpCode {
    fn new(code: u8, op: OP, len: u8, cycles: u8, mode: AddressingMode) -> Self {
        Self { code, op, len, cycles, mode }
    }
}

lazy_static! {
    pub static ref CPU_OPS_CODES: Vec<OpCode> = vec![
        OpCode::new(0x00, OP::BRK, 1, 7, AddressingMode::NoneAddressing),
        OpCode::new(0xea, OP::NOP, 1, 2, AddressingMode::NoneAddressing),

        /* Arithmetic */
        OpCode::new(0x69, OP::ADC, 2, 2, AddressingMode::Immediate),
        OpCode::new(0x65, OP::ADC, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x75, OP::ADC, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x6d, OP::ADC, 3, 4, AddressingMode::Absolute),
        OpCode::new(0x7d, OP::ADC, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0x79, OP::ADC, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0x61, OP::ADC, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x71, OP::ADC, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        OpCode::new(0xe9, OP::SBC, 2, 2, AddressingMode::Immediate),
        OpCode::new(0xe5, OP::SBC, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xf5, OP::SBC, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xed, OP::SBC, 3, 4, AddressingMode::Absolute),
        OpCode::new(0xfd, OP::SBC, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0xf9, OP::SBC, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0xe1, OP::SBC, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xf1, OP::SBC, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        OpCode::new(0x29, OP::AND, 2, 2, AddressingMode::Immediate),
        OpCode::new(0x25, OP::AND, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x35, OP::AND, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x2d, OP::AND, 3, 4, AddressingMode::Absolute),
        OpCode::new(0x3d, OP::AND, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0x39, OP::AND, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0x21, OP::AND, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x31, OP::AND, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        OpCode::new(0xaa, OP::TAX, 1, 2, AddressingMode::NoneAddressing),
        OpCode::new(0xe8, OP::INX, 1, 2, AddressingMode::NoneAddressing),

        OpCode::new(0xa9, OP::LDA, 2, 2, AddressingMode::Immediate),
        OpCode::new(0xa5, OP::LDA, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xb5, OP::LDA, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xad, OP::LDA, 3, 4, AddressingMode::Absolute),
        OpCode::new(0xbd, OP::LDA, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0xb9, OP::LDA, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0xa1, OP::LDA, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xb1, OP::LDA, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        OpCode::new(0x85, OP::STA, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x95, OP::STA, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x8d, OP::STA, 3, 4, AddressingMode::Absolute),
        OpCode::new(0x9d, OP::STA, 3, 5, AddressingMode::Absolute_X),
        OpCode::new(0x99, OP::STA, 3, 5, AddressingMode::Absolute_Y),
        OpCode::new(0x81, OP::STA, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x91, OP::STA, 2, 6, AddressingMode::Indirect_Y),

    ];


    pub static ref OPCODES_MAP: HashMap<u8, &'static OpCode> = {
        let mut map = HashMap::new();
        for cpuop in &*CPU_OPS_CODES {
            map.insert(cpuop.code, cpuop);
        }
        map
    };
}