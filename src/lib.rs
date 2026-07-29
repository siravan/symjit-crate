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
//! In Rust, there are two ways to contruct expressions to pass to Symjit: using
//! Symbolica or using Symjit standalone expression builder.
//!
//! # Symbolica
//!
//! Symbolica (<https://symbolica.io/>) is a fast Rust-based Computer Algebra System.
//! As of version 1.5 of Symbolica, Symjit is an optional backend for Symbolica. Therefore,
//! the previous interface through `Compiler` object is considered obsolete and should not
//! be used for new projects.
//!
//! # Standalone Expression Builder
//!
//! A second way to use Symjit is by using its standalone expression builder. Compared to
//! Symbolica, the expression builder is limited but is useful in situations that the goal
//! is to compile an expression without extensive symbolic manipulations.
//!
//! The workflow to create, compile, and run expressions is:
//!
//! 1. Create terminals (variables and constants) and compose expressions using `Expr` methods:
//!    * Constructors: `var`, `from`, `unary`, `binary`, ...
//!    * Standard algebraic operations: `add`, `mul`, ...
//!    * Standard operators `+`, `-`, `*`, `/`, `%`, `&`, `|`, `^`, `!`.
//!    * Unary functions such as `sin`, `exp`, and other standard mathematical functions.
//!    * Binary functions such as `pow`, `min`, ...
//!    * IfElse operation `ifelse(cond, true_val, false_val)`.
//!    * Heaviside function: `heaviside(x)`, which returns 1 if `x >= 0`; otherwise 0.
//!    * Comparison methods `eq`, `ne`, `lt`, `le`, `gt`, and `ge`.
//!    * Looping constructs `sum` and `prod`.
//! 2. Create a new `Compiler` object (say, `comp`) using one of its constructors.
//! 3. Define user-defined functions by calling `comp.def_unary` and `comp.def_binary`
//!    (optional).
//! 4. Compile by calling `comp.compile` or `comp.compile_params`. The result is of
//!    type `Application` (say, `app`).
//! 5. Execute the compiled code using one of the `app`'s `call` functions:
//!    * `call(&[f64])`: scalar call.
//!    * `call_params(&[f64], &[f64])`: scalar call with parameters.
//!    * `call_simd(&[__m256d])`: simd call.
//!    * `call_simd_params(&[__m256d], &[f64])`: simd call with parameters.
//! 6. Optionally, generate a standalone fast function to execute.
//!
//! Note that you can use the helper functions `var(&str) -> Expr`, `int(i32) -> Expr`,
//! `double(f64) -> Expr`, and `boolean(bool) -> f64` to reduce clutter.
//!
//! # Examples
//!
//! ```rust
//! use anyhow::Result;
//! use symjit::{Compiler, Expr};
//!
//! pub fn test_scalar() -> Result<()> {
//!     let x = Expr::var("x");
//!     let y = Expr::var("y");
//!     let u = &x + &y;
//!     let v = &x * &y;
//!
//!     let mut comp = Compiler::new();
//!     let mut app = comp.compile(&[x, y], &[u, v])?;
//!     let res = app.call(&[3.0, 5.0]);
//!     println!("{:?}", &res);   // prints [8.0, 15.0]
//!
//!     Ok(())
//! }
//! ```
//!
//! `test_scalar` is similar to the following basic example in Python/SymPy:
//!
//! ```python
//! from symjit import compile_func
//! from sympy import symbols
//!
//! x, y = symbols('x y')
//! f = compile_func([x, y], [x+y, x*y])
//! print(f(3.0, 5.0))  # prints [8.0, 15.0]
//! ```
//!
//! A more elaborate example, showcasing having a parameter, changing the
//! optimization level, and using SIMD:
//!
//! ```rust
//! use anyhow::Result;
//! use symjit::{var, Compiler, Expr};
//!
//! pub fn test_simd() -> Result<()> {
//!     use std::arch::x86_64::_mm256_loadu_pd;
//!
//!     let x = var("x");   // note var instead of Expr::var
//!     let p = var("p");   // the parameter
//!
//!     let u = &x.square() * &p;    // x^2 * p
//!     let mut comp = Compiler::new();
//!     comp.opt_level(2);  // optional (opt_level 0 to 2; default 1)
//!     let mut app = comp.compile_params(&[x], &[u], &[p])?;
//!
//!     let a = &[1.0, 2.0, 3.0, 4.0];
//!     let a = unsafe { _mm256_loadu_pd(a.as_ptr()) };
//!     let res = app.call_simd_params(&[a], &[5.0])?;
//!     println!("{:?}", &res);   // prints [__m256d(5.0, 20.0, 45.0, 80.0)]
//!     Ok(())
//! }
//! ```
//!
//! # Conditional Expression and Loops
//!
//! Many mathematical formulas need conditional expressions (`ifelse`) and loops.
//! Following SymPy, Symjit uses reduction loops such as `sum` and `prod`. The following
//! example returns the exponential functions:
//!
//! ```rust
//! use symjit::{int, var, Compiler};
//!
//! fn test_exp() -> Result<()> {
//!     let x = var("x");
//!     let i = var("i");   // loop variable
//!     let j = var("j");   // loop variable
//!
//!     // u = x^j / factorial(j) for j in j in 0..=50
//!     let u = x
//!         .pow(&j)
//!         .div(&i.prod(&i, &int(1), &j))
//!         .sum(&j, &int(0), &int(50));
//!
//!     let mut app = Compiler::new().compile(&[x], &[u])?;
//!     println!("{:?}", app(&[2.0])[0]); // returns exp(2.0) = 7.38905...
//!     Ok(())
//! }
//! ```
//!
//! An example showing how to calculate pi using the Leibniz formula:
//!
//! ```rust
//! use symjit::{int, var, Compiler};
//!
//! fn test_pi() -> Result<()> {
//!     let n = var("n");
//!     let i = var("i");   // loop variable
//!     let j = var("j");   // loop variable
//!
//!     // numer = if j % 2 == 0 { 4 } else { -4 }
//!     let numer = j.rem(&int(2)).eq(&int(0)).ifelse(&int(4), &int(-4));
//!     // denom = j * 2 + 1
//!     let denom = j.mul(&int(2)).add(&int(1));
//!     // v = numer / denom for j in 0..=n
//!     let v = (&numer / &denom).sum(&j, &int(0), &int(&n));
//!
//!     let mut app = Compiler::new().compile(&[x], &[v])?;
//!     println!("{:?}", app(&[100000000])[0]); // returns pi
//!     Ok(())
//! }
//! ```
//!
//! Note that here we are using explicit functions (`add`, `mul`, ...) instead of
//! the overloaded operators for clarity.
//!
//! # Fast Functions
//!
//! `Application`'s call functions need to copy the input slice into the function
//! memory area and then copy the output to a `Vec`. This process is acceptable
//! for large and complex functions but incurs a penalty for small ones.
//! Therefore, for a certain subset of applications, Symjit can compile to a
//! *fast function* and return a function pointer. Examples:
//!
//! ```rust
//! use anyhow::Result;
//! use symjit::{int, var, Compiler, FastFunc};
//!
//! fn test_fast() -> Result<()> {
//!     let x = var("x");
//!     let y = var("y");
//!     let z = var("z");
//!     let u = &x * &(&y - &z).pow(&int(2));    // x * (y - z)^2
//!
//!     let mut comp = Compiler::new();
//!     let mut app = comp.compile(&[x, y, z], &[u])?;
//!     let f = app.fast_func()?;
//!
//!     if let FastFunc::F3(f, _) = f {
//!         // f is of type extern "C" fn(f64, f64, f64) -> f64
//!         let res = f(3.0, 5.0, 9.0);
//!         println!("fast\t{:?}", &res);
//!     }
//!
//!     Ok(())
//! }
//! ```
//!
//! The conditions for a fast function are:
//!
//! * A fast function can have 1 to 8 arguments.
//! * No SIMD and no parameters.
//! * It returns only a single value.
//!
//! If these conditions are met, you can generate a fast function by calling
//! `app.fast_func()`, which returns a `Result<FastFunc>`. `FastFunc` is an
//! enum with eight variants `F1`, `F2`, ..., `F8`, corresponding to functions
//! with 1 to 8 arguments.
//!
//! # User-Defined Functions
//!
//! Symjit functions can call into user-defined Rust functions. Currently,
//! only the following function signatures are accepted:
//!
//! ```rust
//! pub type UnaryFunc = extern "C" fn(f64) -> f64;
//! pub type BinaryFunc = extern "C" fn(f64, f64) -> f64;
//! ```
//!
//! For example:
//!
//! ```rust
//! extern "C" fn f(x: f64) -> f64 {
//!     x.exp()
//! }
//!
//! extern "C" fn g(x: f64, y: f64) -> f64 {
//!     x.ln() * y
//! }
//!
//! fn test_external() -> Result<()> {
//!     let x = Expr::var("x");
//!     let u = Expr::unary("f_", &x);
//!     let v = &x * &Expr::binary("g_", &u, &x);
//!
//!     // v(x) = x * (ln(exp(x)) * x) = x ^ 3
//!
//!     let mut comp = Compiler::new();
//!     comp.def_unary("f_", f);
//!     comp.def_binary("g_", g);
//!     let mut app = comp.compile(&[x], &[v])?;
//!     println!("{:?}", app.call(&[5.0])[0]);
//!
//!     Ok(())
//! }
//! ```
//!
//! # Dynamic Expressions
//!
//! All the examples up to this point use static expressions. Of course, it
//! would have been easier just to use Rust expressions for these examples!
//! The main utility of Symjit for Rust is for dynamic code generation. Here,
//! we provide a simple example to calculate pi using Viete's formula
//! (<https://en.wikipedia.org/wiki/Vi%C3%A8te%27s_formula>):
//!
//! ```rust
//! fn test_pi_viete(silent: bool) -> Result<()> {
//!     let x = var("x");
//!     let mut u = int(1);
//!
//!     for i in 0..50 {
//!         let mut t = x.clone();
//!
//!         for _ in 0..i {
//!             t = &x + &(&x * &t.sqrt());
//!         }
//!
//!         u = &u * &t.sqrt();
//!     }
//!
//!     // u has 1275 = 50 * 51 / 2 sqrt operations
//!     let mut app = Compiler::new().compile(&[x], &[&int(2) / &u])?;
//!     println!("pi = \t{:?}", app.call(&[0.5])[0]);
//!     Ok(())
//! }
//! ```
//!
//! # C-Interface
//!
//! In addition to `Compiler`, this crate provides a C-style interface
//! used by the Python (<https://github.com/siravan/symjit>) and Julia
//! (<https://github.com/siravan/Symjit.jl>) packages. This interface
//! is composed of crate functions like `compile`, `execute`, and
//! `ptr_states`,..., and is not needed by the Rust interface but can be
//! used to link symjit to other programming languages.
//!

mod symjit;

pub use num_complex::{Complex, ComplexFloat};

pub use symjit::{
    double, int, var, Applet, Application, BuiltinSymbol, Compiled, Compiler, CompilerType,
    Composer, Config, Defuns, ElemType, Element, Expr, FastFunc, Instruction, MirWriter, Slot,
    Storage, SymbolicaModel, Translator,
};
