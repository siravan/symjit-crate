#![allow(uncommon_codepoints)]

//! Symjit (<https://github.com/siravan/symjit>) is a lightweight just-in-time (JIT)
//! optimizer compiler for mathematical expressions written in Rust. It was originally
//! designed to compile SymPy (Python’s symbolic algebra package) expressions
//! into machine code and to serve as a bridge between SymPy and numerical routines
//! provided by NumPy and SciPy libraries.
//!
//! Symjit crate is the core compiler coupled to a Rust interface to expose the
//! JIT functionality to the Rust ecosystem and allow Rust applications to
//! generate code dynamically. Considering its origin, symjit is geared toward
//! compiling mathematical expressions instead of being a general-purpose JIT
//! compiler. Therefore, the only supported types for variables are `f64`,
//! (SIMD f64x4 and f64x2), and implicitly, `bool` and `i32`.
//!
//! Symjit emits AMD64 (x86-64), ARM64 (aarch64), and 64-bit RISC-V (riscv64) machine
//! codes on Linux, Windows, and macOS platforms. SIMD is supported on x86-64
//! and ARM64.
//!
//! Symjit is the default code generator backend of Symbolica (<https://symbolica.io/>), which is
//! a fast Rust-based Computer Algebra System. The former interface through `Compiler` object is
//! obsolete and should not be used.
//!

mod symjit;

pub use num_complex::{Complex, ComplexFloat};

pub use symjit::{
    Applet, Application, BuiltinSymbol, Compiled, CompiledPlaneFunc, Compiler, CompilerType,
    Composer, Config, Defuns, ElemType, Element, Expr, FastFunc, Instruction, Matrix, MirWriter,
    PlaneDescriptor, Slot, Storage, SymbolicaModel, Translator,
};

pub fn var(name: &str) -> Expr {
    Expr::var(name)
}

pub fn double(val: f64) -> Expr {
    Expr::from(val)
}

pub fn int(val: i32) -> Expr {
    Expr::from(val)
}

fn bool_to_f64(b: bool) -> f64 {
    const T: f64 = f64::from_bits(!0);
    const F: f64 = f64::from_bits(0);
    if b {
        T
    } else {
        F
    }
}

pub fn boolean(val: bool) -> Expr {
    Expr::from(bool_to_f64(val))
}
