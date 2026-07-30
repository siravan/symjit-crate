use anyhow::Result;
pub use num_complex::{Complex, ComplexFloat};
use symjit::{Compiler, Config};
use wide::{f64x2, f64x4};

const MODEL: &str = "
([('fun', ('temp', 0), 'square', [], [('param', 0)], False),
  ('add', ('temp', 1), [('temp', 0), ('param', 1)], 0),
  ('assign', ('out', 0), ('temp', 1))],
 2,
 [])
";

fn pass(what: &str) {
    println!("**** test {:?} passed. ****", what);
}

pub fn test_instructions() -> Result<()> {
    let mut compiler = Compiler::new();
    let app = compiler.translate(MODEL.into(), 0)?;

    let args = vec![3.0, 5.0];
    let mut outs = vec![0.0];

    app.evaluate(&args, &mut outs);
    assert!(outs[0] == 14.0);
    Ok(())
}

fn kernel_p1_real() -> Result<()> {
    let mut config = Config::default();
    config.set_direct_arena(true);
    let mut compiler = Compiler::with_config(config);

    let app = compiler.translate(MODEL.into(), 0)?.seal()?;
    let mut mem = vec![3.0, 5.0, 0.0];
    let params: Vec<f64> = Vec::new();

    let f = app.scalar_kernel().unwrap();
    let _ = f(mem.as_mut_ptr(), std::ptr::null(), 0, params.as_ptr());
    assert!(mem[2] == 14.0);
    Ok(())
}

fn kernel_p1_complex() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(true);
    config.set_direct_arena(true);
    let mut compiler = Compiler::with_config(config);

    let app = compiler.translate(MODEL.into(), 0)?.seal()?;
    let x = Complex::new(1.0, 2.0);
    let y = Complex::new(3.0, 4.0);
    let mut mem = vec![x.re, x.im, y.re, y.im, 0.0, 0.0];
    let params: Vec<f64> = Vec::new();

    let f = app.scalar_kernel().unwrap();
    let _ = f(mem.as_mut_ptr(), std::ptr::null(), 0, params.as_ptr());
    let z = Complex::new(mem[4], mem[5]);
    assert!(z == Complex::new(0.0, 8.0));
    Ok(())
}

fn kernel_p2_scalar_real() -> Result<()> {
    let mut config = Config::default();
    config.set_direct_arena(true);
    let mut compiler = Compiler::with_config(config);
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let mut x = [2.0, 3.0, 4.0, 5.0, 6.0];
    let mut y = [1.0, 2.0, 3.0, 4.0, 5.0];
    let mut z = [0.0, 0.0, 0.0, 0.0, 0.0];

    let states: Vec<&mut [f64]> = vec![&mut x[..], &mut y[..], &mut z[..]];
    let params: Vec<f64> = Vec::new();

    let f = app.scalar_kernel().unwrap();
    let _ = f(std::ptr::null(), states.as_ptr(), 2, params.as_ptr());
    assert!(z[2] == 19.0);
    Ok(())
}

fn kernel_p2_scalar_complex() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(true);
    config.set_direct_arena(true);
    let mut compiler = Compiler::with_config(config);
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let mut x = Complex::new([1.0, 2.0, 3.0], [2.0, 3.0, 4.0]);
    let mut y = Complex::new([1.0, 2.0, 3.0], [2.0, 3.0, 4.0]);
    let mut z = Complex::new([0.0, 0.0, 0.0], [0.0, 0.0, 0.0]);

    let states: Vec<&mut [f64]> = vec![
        &mut x.re[..],
        &mut x.im[..],
        &mut y.re[..],
        &mut y.im[..],
        &mut z.re[..],
        &mut z.im[..],
    ];
    let params: Vec<f64> = Vec::new();

    let f = app.scalar_kernel().unwrap();
    let _ = f(std::ptr::null(), states.as_ptr(), 2, params.as_ptr());
    assert!(z.re[2] == -4.0 && z.im[2] == 28.0);
    Ok(())
}

fn kernel_p2_simd_real() -> Result<()> {
    let mut config = Config::default();
    config.set_direct_arena(true);
    let mut compiler = Compiler::with_config(config);
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let mut x = [2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0];
    let mut y = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
    let mut z = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];

    let states: Vec<&mut [f64]> = vec![&mut x[..], &mut y[..], &mut z[..]];
    let params: Vec<f64> = Vec::new();

    let f = app.simd_kernel().unwrap();
    let _ = f(std::ptr::null(), states.as_ptr(), 0, params.as_ptr());
    let _ = f(std::ptr::null(), states.as_ptr(), 1, params.as_ptr());
    assert!(z[2] == 19.0);
    Ok(())
}

fn kernel_p2_simd_complex() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(true);
    config.set_direct_arena(true);
    let mut compiler = Compiler::with_config(config);
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let mut x = Complex::new([1.0, 2.0, 3.0, 4.0], [1.0, 2.0, 3.0, 4.0]);
    let mut y = Complex::new([1.0, 2.0, 3.0, 4.0], [1.0, 2.0, 3.0, 4.0]);
    let mut z = Complex::new([0.0, 0.0, 0.0, 0.0], [0.0, 0.0, 0.0, 0.0]);

    let states: Vec<&mut [f64]> = vec![
        &mut x.re[..],
        &mut x.im[..],
        &mut y.re[..],
        &mut y.im[..],
        &mut z.re[..],
        &mut z.im[..],
    ];
    let params: Vec<f64> = Vec::new();

    let f = app.simd_kernel().unwrap();
    let _ = f(std::ptr::null(), states.as_ptr(), 0, params.as_ptr());

    #[cfg(target_arch = "aarch64")]
    let _ = f(std::ptr::null(), states.as_ptr(), 1, params.as_ptr());

    assert!(z.re[3] == 4.0 && z.im[3] == 36.0);
    Ok(())
}

fn kernel_b1_scalar_real() -> Result<()> {
    let mut compiler = Compiler::new();
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let args = vec![3.0, 5.0];
    let mut outs = vec![0.0];

    let f = app.scalar_kernel().unwrap();
    let _ = f(outs.as_mut_ptr(), std::ptr::null(), 0, args.as_ptr());
    assert!(outs[0] == 14.0);

    Ok(())
}

fn kernel_b1_scalar_complex() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(true);
    let mut compiler = Compiler::with_config(config);
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let args = vec![Complex::new(1.0, 2.0), Complex::new(3.0, 4.0)];
    let mut outs = vec![Complex::new(0.0, 0.0)];

    let f = app.scalar_kernel().unwrap();
    let _ = f(
        outs.as_mut_ptr() as *const f64,
        std::ptr::null(),
        0,
        args.as_ptr() as *const f64,
    );

    assert!(outs[0] == Complex::new(0.0, 8.0));
    Ok(())
}

#[cfg(target_arch = "x86_64")]
fn kernel_b1_simd_real() -> Result<()> {
    let mut config = Config::default();
    config.enable_simd512(false);
    let mut compiler = Compiler::with_config(config);
    let mut app = compiler.translate(MODEL.into(), 0)?;
    app.dump("test.bin", "simd");
    let app = app.seal()?;

    let args = [
        f64x4::new([1.0, 2.0, 3.0, 4.0]),
        f64x4::new([1.0, 2.0, 3.0, 4.0]),
    ];
    let mut outs = [f64x4::new([0.0, 0.0, 0.0, 0.0])];

    let f = app.simd_kernel().unwrap();

    let _ = f(
        outs.as_mut_ptr() as *mut f64,
        std::ptr::null(),
        0,
        args.as_ptr() as *const f64,
    );

    assert!(outs[0] == f64x4::new([2.0, 6.0, 12.0, 20.0]));
    Ok(())
}

#[cfg(target_arch = "aarch64")]
fn kernel_b1_simd_real() -> Result<()> {
    let mut config = Config::default();
    config.enable_simd512(false);
    let mut compiler = Compiler::with_config(config);
    let mut app = compiler.translate(MODEL.into(), 0)?;
    app.dump("test.bin", "simd");
    let app = app.seal()?;

    let args = [f64x2::new([1.0, 2.0]), f64x2::new([1.0, 2.0])];
    let mut outs = [f64x2::new([0.0, 0.0])];

    let f = app.simd_kernel().unwrap();

    let _ = f(
        outs.as_mut_ptr() as *mut f64,
        std::ptr::null(),
        0,
        args.as_ptr() as *const f64,
    );

    assert!(outs[0] == f64x2::new([2.0, 6.0]));
    Ok(())
}

#[cfg(target_arch = "x86_64")]
fn kernel_b1_simd_complex() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(true);
    config.enable_simd512(false);
    let mut compiler = Compiler::with_config(config);
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let args = [
        Complex::new(
            f64x4::new([1.0, 2.0, 3.0, 4.0]),
            f64x4::new([1.0, 2.0, 3.0, 4.0]),
        ),
        Complex::new(
            f64x4::new([1.0, 2.0, 3.0, 4.0]),
            f64x4::new([1.0, 2.0, 3.0, 4.0]),
        ),
    ];
    let mut outs = [Complex::new(
        f64x4::new([0.0, 0.0, 0.0, 0.0]),
        f64x4::new([0.0, 0.0, 0.0, 0.0]),
    )];

    let f = app.simd_kernel().unwrap();

    let _ = f(
        outs.as_mut_ptr() as *mut f64,
        std::ptr::null(),
        0,
        args.as_ptr() as *const f64,
    );

    assert!(
        outs[0]
            == Complex::new(
                f64x4::new([1.0, 2.0, 3.0, 4.0]),
                f64x4::new([3.0, 10.0, 21.0, 36.0])
            )
    );
    Ok(())
}

#[cfg(target_arch = "aarch64")]
fn kernel_b1_simd_complex() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(true);
    let mut compiler = Compiler::with_config(config);
    let app = compiler.translate(MODEL.into(), 0)?.seal()?;

    let args = [
        Complex::new(f64x2::new([1.0, 2.0]), f64x2::new([1.0, 2.0])),
        Complex::new(f64x2::new([1.0, 2.0]), f64x2::new([1.0, 2.0])),
    ];
    let mut outs = [Complex::new(f64x2::new([0.0, 0.0]), f64x2::new([0.0, 0.0]))];

    let f = app.simd_kernel().unwrap();

    let _ = f(
        outs.as_mut_ptr() as *mut f64,
        std::ptr::null(),
        0,
        args.as_ptr() as *const f64,
    );

    assert!(outs[0] == Complex::new(f64x2::new([1.0, 2.0]), f64x2::new([3.0, 10.0])));
    Ok(())
}

fn kernel_b2_simd_real() -> Result<()> {
    let mut config = Config::default();
    config.enable_simd512(false);
    let mut compiler = Compiler::with_config(config);
    let mut app = compiler.translate(MODEL.into(), 0)?;
    app.dump("test.bin", "simd");
    let app = app.seal()?;

    let args = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
    let mut outs = [0.0, 0.0, 0.0, 0.0];

    let f = app.simd_kernel().unwrap();

    let _ = f(
        outs.as_mut_ptr() as *mut f64,
        std::ptr::null(),
        1,
        args.as_ptr() as *const f64,
    );

    assert!(outs[1] == 13.0); // 13 = 3^2 + 4
    Ok(())
}

fn kernel_b2_simd_complex() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(true);
    config.enable_simd512(false);
    let mut compiler = Compiler::with_config(config);
    let mut app = compiler.translate(MODEL.into(), 0)?;
    app.dump("test.bin", "simd");
    let app = app.seal()?;

    let args = [
        Complex::new(1.0, 2.0),
        Complex::new(2.0, 2.0),
        Complex::new(3.0, 2.0),
        Complex::new(4.0, 2.0),
        Complex::new(5.0, 2.0),
        Complex::new(6.0, 2.0),
        Complex::new(7.0, 2.0),
        Complex::new(8.0, 2.0),
    ];
    let mut outs = [
        Complex::new(0.0, 0.0),
        Complex::new(0.0, 0.0),
        Complex::new(0.0, 0.0),
        Complex::new(0.0, 0.0),
    ];

    let f = app.simd_kernel().unwrap();

    let _ = f(
        outs.as_mut_ptr() as *mut f64,
        std::ptr::null(),
        1,
        args.as_ptr() as *const f64,
    );

    assert!(outs[1] == Complex::new(9.0, 14.0)); // 9+14j = (3+2j)^2 + (4+2j)
    Ok(())
}

pub fn main() -> Result<()> {
    test_instructions()?;
    pass("instructions");

    kernel_p1_real()?;
    pass("Kernel P1 real");

    kernel_p1_complex()?;
    pass("Kernel P1 complex");

    kernel_p2_scalar_real()?;
    pass("Kernel P2 scalar real");

    kernel_p2_scalar_complex()?;
    pass("Kernel P2 scalar complex");

    kernel_p2_simd_real()?;
    pass("Kernel P2 simd real");

    kernel_p2_simd_complex()?;
    pass("Kernel P2 simd complex");

    kernel_b1_scalar_real()?;
    pass("Kernel B1 real");

    kernel_b1_scalar_complex()?;
    pass("Kernel B1 complex");

    kernel_b1_simd_real()?;
    pass("Kernel B1 simd real");

    kernel_b1_simd_complex()?;
    pass("Kernel B1 simd complex");

    kernel_b2_simd_real()?;
    pass("Kernel B2 simd real");

    kernel_b2_simd_complex()?;
    pass("Kernel B2 simd complex");

    Ok(())
}
