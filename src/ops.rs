use std::collections::HashMap;

#[derive(Debug, PartialEq)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Accumulator,
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect, // Only used by jmp
    Indirect_X,
    Indirect_Y,
    Implicit,
    Relative,
    // NoneAddressing,
}

pub enum OP {
    BRK, // Force Interrupt
    NOP,

    // Arithmetic
    ADC, // Add with Carry
    SBC, // Subtract with Carry
    INC, // Increment Memory
    INX, // Increment Register X
    INY, // Increment Register Y
    DEC, // Decrement Memory
    DEX, // Decement Register X
    DEY, // Decrement Register Y
    CMP, // Compare with Accumulator
    CPX, // Compare with Register X
    CPY, // Compare with Register Y

    // Logical
    AND, // Logical AND
    EOR, // Logical Exclusive OR
    ORA, // Logical Inclusive OR

    // Shifts
    ASL, // Arithmetic Shift Left
    LSR, // Logical Shift Right
    ROL, // Rotate Left
    ROR, // Rotate Right

    // Jumps + Branching
    JMP, // Jump
    JSR, // Jump to Subroutine
    RTS, // Return from Subroutine
    RTI, // return from Interrupt
    BNE, // Branch if Not Equal

    LDA, // Load Accumulator

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

    // https://www.nesdev.org/obelisk-6502-guide/reference.html
    pub static ref CPU_OPS_CODES: Vec<OpCode> = vec![
        OpCode::new(0x00, OP::BRK, 1, 7, AddressingMode::Implicit),
        OpCode::new(0xea, OP::NOP, 1, 2, AddressingMode::Implicit),

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

        OpCode::new(0xe6, OP::INC, 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0xf6, OP::INC, 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0xee, OP::INC, 3, 6, AddressingMode::Absolute),
        OpCode::new(0xfe, OP::INC, 3, 7, AddressingMode::Absolute_X),

        OpCode::new(0xe8, OP::INX, 1, 2, AddressingMode::Implicit),
        OpCode::new(0xc8, OP::INY, 1, 2, AddressingMode::Implicit),

        OpCode::new(0xc6, OP::DEC, 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0xd6, OP::DEC, 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0xce, OP::DEC, 3, 6, AddressingMode::Absolute),
        OpCode::new(0xde, OP::DEC, 3, 7, AddressingMode::Absolute_X),

        OpCode::new(0xca, OP::DEX, 1, 2, AddressingMode::Implicit),
        OpCode::new(0x88, OP::DEY, 1, 2, AddressingMode::Implicit),

        OpCode::new(0xc9, OP::CMP, 2, 2, AddressingMode::Immediate),
        OpCode::new(0xc5, OP::CMP, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xd5, OP::CMP, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0xcd, OP::CMP, 3, 4, AddressingMode::Absolute),
        OpCode::new(0xdd, OP::CMP, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0xd9, OP::CMP, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0xc1, OP::CMP, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0xd1, OP::CMP, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        OpCode::new(0xe0, OP::CPX, 2, 2, AddressingMode::Immediate),
        OpCode::new(0xe4, OP::CPX, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xec, OP::CPX, 3, 4, AddressingMode::Absolute),

        OpCode::new(0xc0, OP::CPY, 2, 2, AddressingMode::Immediate),
        OpCode::new(0xc4, OP::CPY, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0xcc, OP::CPY, 3, 4, AddressingMode::Absolute),


        /* Logical */
        OpCode::new(0x29, OP::AND, 2, 2, AddressingMode::Immediate),
        OpCode::new(0x25, OP::AND, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x35, OP::AND, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x2d, OP::AND, 3, 4, AddressingMode::Absolute),
        OpCode::new(0x3d, OP::AND, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0x39, OP::AND, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0x21, OP::AND, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x31, OP::AND, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        OpCode::new(0x49, OP::EOR, 2, 2, AddressingMode::Immediate),
        OpCode::new(0x45, OP::EOR, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x55, OP::EOR, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x4d, OP::EOR, 3, 4, AddressingMode::Absolute),
        OpCode::new(0x5d, OP::EOR, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0x59, OP::EOR, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0x41, OP::EOR, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x51, OP::EOR, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),

        OpCode::new(0x09, OP::ORA, 2, 2, AddressingMode::Immediate),
        OpCode::new(0x05, OP::ORA, 2, 3, AddressingMode::ZeroPage),
        OpCode::new(0x15, OP::ORA, 2, 4, AddressingMode::ZeroPage_X),
        OpCode::new(0x0d, OP::ORA, 3, 4, AddressingMode::Absolute),
        OpCode::new(0x1d, OP::ORA, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_X),
        OpCode::new(0x19, OP::ORA, 3, 4/*+1 if page crossed*/, AddressingMode::Absolute_Y),
        OpCode::new(0x01, OP::ORA, 2, 6, AddressingMode::Indirect_X),
        OpCode::new(0x11, OP::ORA, 2, 5/*+1 if page crossed*/, AddressingMode::Indirect_Y),


        /* Shifts */
        OpCode::new(0x0a, OP::ASL, 1, 2, AddressingMode::Accumulator),
        OpCode::new(0x06, OP::ASL, 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0x16, OP::ASL, 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0x0e, OP::ASL, 3, 6, AddressingMode::Absolute),
        OpCode::new(0x1e, OP::ASL, 3, 7, AddressingMode::Absolute_X),

        OpCode::new(0x4a, OP::LSR, 1, 2, AddressingMode::Accumulator),
        OpCode::new(0x46, OP::LSR, 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0x56, OP::LSR, 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0x4e, OP::LSR, 3, 6, AddressingMode::Absolute),
        OpCode::new(0x5e, OP::LSR, 3, 7, AddressingMode::Absolute_X),

        OpCode::new(0x2a, OP::ROL, 1, 2, AddressingMode::Accumulator),
        OpCode::new(0x26, OP::ROL, 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0x36, OP::ROL, 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0x2e, OP::ROL, 3, 6, AddressingMode::Absolute),
        OpCode::new(0x3e, OP::ROL, 3, 7, AddressingMode::Absolute_X),

        OpCode::new(0x6a, OP::ROR, 1, 2, AddressingMode::Accumulator),
        OpCode::new(0x66, OP::ROR, 2, 5, AddressingMode::ZeroPage),
        OpCode::new(0x76, OP::ROR, 2, 6, AddressingMode::ZeroPage_X),
        OpCode::new(0x6e, OP::ROR, 3, 6, AddressingMode::Absolute),
        OpCode::new(0x7e, OP::ROR, 3, 7, AddressingMode::Absolute_X),

        /* Jumps + Branching */
        OpCode::new(0x4c, OP::JMP, 3, 3, AddressingMode::Absolute),
        OpCode::new(0x6c, OP::JMP, 3, 5, AddressingMode::Indirect),

        OpCode::new(0x20, OP::JSR, 3, 6, AddressingMode::Absolute),
        OpCode::new(0x60, OP::RTS, 1, 6, AddressingMode::Implicit),

        OpCode::new(0x40, OP::RTI, 1, 6, AddressingMode::Implicit),

        OpCode::new(0xd0, OP::BNE, 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::Relative),
        // OpCode::new(0x70, "BVS", 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::NoneAddressing),
        // OpCode::new(0x50, "BVC", 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::NoneAddressing),
        // OpCode::new(0x30, "BMI", 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::NoneAddressing),
        // OpCode::new(0xf0, "BEQ", 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::NoneAddressing),
        // OpCode::new(0xb0, "BCS", 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::NoneAddressing),
        // OpCode::new(0x90, "BCC", 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::NoneAddressing),
        // OpCode::new(0x10, "BPL", 2, 2 /*(+1 if branch succeeds +2 if to a new page)*/, AddressingMode::NoneAddressing),

        OpCode::new(0xaa, OP::TAX, 1, 2, AddressingMode::Implicit),

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