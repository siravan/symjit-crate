use anyhow::Result;
use num_complex::Complex;
use symjit::{
    int, var, Compiled, Compiler, CompilerType, Composer, Config, Defuns, Expr, FastFunc,
    PlaneDescriptor, Slot, Translator,
};

fn test_simple() -> Result<()> {
    let x = Expr::var("x");
    let y = Expr::var("y");
    let p = &x + &y;
    let q = &x * &y;

    let mut config = Config::default();
    config.set_opt_level(2); // optional
    let mut comp = Compiler::with_config(config);

    let mut app = comp.compile(&[x, y], &[p, q])?;
    let v = app.call(&[3.0, 5.0]);
    println!("simple\t{:?}", &v);

    Ok(())
}

fn test_pi_viete(silent: bool) -> Result<()> {
    let x = var("x");
    let mut u = int(1);

    for i in 0..50 {
        let mut t = x.clone();

        for _ in 0..i {
            t = &x + &(&x * &t.sqrt());
        }

        u = &u * &t.sqrt();
    }

    let mut app = Compiler::new().compile(&[x], &[&int(2) / &u])?;
    let res = app.call(&[0.5]);

    if !silent {
        // println!("{:?}", &u);
        println!("pi = \t{:?}", res[0]);
    }

    Ok(())
}

fn test_loops() -> Result<()> {
    let x = var("x");
    let n = var("n");
    let i = var("i");
    let j = var("j");

    // u = x^j / factorial(j) for j in j in 0..=50
    let u = x
        .pow(&j)
        .div(&i.prod(&i, &int(1), &j))
        .sum(&j, &int(0), &int(50));

    // numer = if j % 2 == 0 { 4 } else { -4 }
    let numer = j.rem(&int(2)).eq(&int(0)).ifelse(&int(4), &int(-4));
    // denom = j * 2 + 1
    let denom = j.mul(&int(2)).add(&int(1));
    // v = numer / denom for j in 0..=100000000
    let v = (&numer / &denom).sum(&j, &int(0), &n);

    let mut app = Compiler::new().compile(&[x, n], &[u, v])?;
    let res = app.call(&[2.0, 100000000.0]);

    println!("e^2 = \t{:?}", res[0]);
    println!("pi = \t{:?}", res[1]);

    Ok(())
}

fn test_fast() -> Result<()> {
    let x = Expr::var("x");
    let y = Expr::var("y");
    let z = Expr::var("z");
    let p = &x * &(&y - &z).pow(&Expr::from(2));

    let mut comp = Compiler::new();
    let mut app = comp.compile(&[x, y, z], &[p])?;
    let f = app.fast_func()?;

    if let FastFunc::F3(f, _) = f {
        let v = f(3.0, 5.0, 9.0);
        println!("fast\t{:?}", &v);
    }

    Ok(())
}

fn test_fact() -> Result<()> {
    let x = Expr::var("x");
    let i = Expr::var("i");
    let p = i.prod(&i, &Expr::from(1), &x);

    let mut comp = Compiler::new();
    let mut app = comp.compile(&[x], &[p])?;
    let f = app.fast_func()?;

    if let FastFunc::F1(f, _) = f {
        let v = f(6.0);
        println!("fact\t6! = {:?}", &v);
    }

    Ok(())
}

extern "C" fn f(x: f64) -> f64 {
    x.exp()
}

extern "C" fn g(x: f64, y: f64) -> f64 {
    x.ln() * y
}

fn test_external(p: i32) -> Result<()> {
    let x = Expr::var("x");
    let u = Expr::unary("f_", &x);
    let v = &x * &Expr::binary("g_", &u, &x);

    let mut df = Defuns::new();
    df.add_unary("f_", f);
    df.add_binary("g_", g);
    let mut config = Config::from_defuns(df)?;
    config.set_option("use_simd", "true")?;
    let mut comp = Compiler::with_config(config);

    let mut app = comp.compile(&[x], &[v])?;
    let res = app.call(&[p as f64]);
    let expected = (p * p * p) as f64;
    assert_eq!(res[0], expected);

    Ok(())
}

fn test_memory(n: usize) -> Result<()> {
    for _ in 0..n {
        test_pi_viete(true)?;
    }
    Ok(())
}

fn compile_external_evaluators(direct: bool) -> Result<symjit::Application> {
    let f: Box<dyn Fn(&[f64]) -> f64 + Send + Sync> = Box::new(|args| {
        let y = args[0];
        3.0 + y * y + y
    });

    let g: Box<dyn Fn(&[f64]) -> f64 + Send + Sync> = Box::new(|args| {
        let y = args[0];
        3.0 + y * y + y
    });

    let mut defuns = Defuns::new();
    defuns.add_sliced_func("f", f)?;
    defuns.add_sliced_func("g", g)?;

    let mut config = Config::default();
    config.set_complex(false);
    config.set_direct(direct);
    config.set_defuns(defuns);

    // Compile f(y) + f(x). The call order makes the incorrect result match the original report.
    let mut translator = Translator::new(config);
    translator.set_num_params(2);
    translator.append_fun(&Slot::Temp(0), "f", &[Slot::Param(1)], true)?;
    translator.append_fun(&Slot::Temp(1), "f", &[Slot::Param(0)], true)?;
    translator.append_add(&Slot::Out(0), &[Slot::Temp(0), Slot::Temp(1)], 2)?;

    Ok(translator.compile()?)
}

// excternal call bug fixed in v2.22.1
fn test_external_evaluators() -> Result<()> {
    let args = [5.0, 2.0];
    let expected = 42.0;
    let optimized = compile_external_evaluators(false)?.evaluate_single(&args);
    let direct = compile_external_evaluators(true)?.evaluate_single(&args);

    eprintln!("expected:             {expected}");
    eprintln!("optimized translator: {optimized}");
    eprintln!("direct translator:    {direct}");

    assert_eq!(optimized, expected, "optimized translation is incorrect");
    assert_eq!(direct, expected);
    Ok(())
}

fn test_multiple() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(false);

    // Compile f(y) + f(x). The call order makes the incorrect result match the original report.
    let mut translator = Translator::new(config);
    translator.set_num_params(2);
    translator.append_add(&Slot::Out(0), &[Slot::Param(0), Slot::Param(1)], 0)?;
    translator.append_mul(&Slot::Out(1), &[Slot::Param(0), Slot::Out(0)], 0)?;

    let app = translator.compile()?.seal()?;

    let args = [5.0, 2.0];
    let mut outs = vec![0.0; 2];

    app.evaluate(&args, &mut outs);

    assert_eq!(outs[0], args[0] + args[1]);
    assert_eq!(outs[1], (args[0] + args[1]) * args[0]);

    Ok(())
}

fn test_output_reuse() -> Result<()> {
    let mut config = Config::default();
    config.set_complex(false);

    // Compile f(y) + f(x). The call order makes the incorrect result match the original report.
    let mut translator = Translator::new(config);
    translator.set_num_params(1);
    translator.append_assign(&Slot::Out(0), &Slot::Param(0))?;
    translator.append_assign(&Slot::Out(1), &Slot::Out(0))?;

    let mut app = translator.compile()?;

    app.dump("output_reuse.bytecode.txt", "bytecode");

    let args = [5.0, 2.0];
    let mut outs = vec![0.0; 2];

    app.evaluate(&args, &mut outs);

    assert_eq!(outs[0], args[0]);
    assert_eq!(outs[1], args[0]);

    Ok(())
}

// AI-generated test unused-trailing-inputs bug
fn declared_unused_inputs_do_not_shift_outputs() -> Result<()> {
    for complex in [false, true] {
        for opt in [0, 2] {
            for all_unused in [false, true] {
                let mut config = Config::new(CompilerType::Native, 0)?;
                config.set_symbolica(true);
                config.set_opt_level(opt);
                config.set_complex(complex);
                config.set_simd(true);
                config.set_direct_arena(true);
                config.set_direct_arena_identity_output(true);
                let mut translator = Translator::new(config);
                translator.set_num_params(2);
                let source = if all_unused {
                    Slot::Const(
                        translator
                            .append_constant(Complex::new(7.0, if complex { 9.0 } else { 0.0 }))?,
                    )
                } else {
                    Slot::Param(0)
                };
                if all_unused {
                    translator.append_assign(&Slot::Out(0), &source)?;
                } else {
                    translator.append_add(
                        &Slot::Out(0),
                        &[source, source],
                        if complex { 0 } else { 2 },
                    )?;
                }
                let mut application = translator.compile()?;
                application.prepare_simd();
                let app = application.seal()?;
                let lanes = app.compiled_simd.as_ref().map_or(1, |v| v.count_lanes());
                let width = if complex { 2 } else { 1 };
                // All input/output planes are disjoint. The unused input is a sentinel.
                let mut planes: Vec<Vec<f64>> = (0..3 * width)
                    .map(|i| {
                        vec![
                            if i < width {
                                3.0 + i as f64
                            } else if i < 2 * width {
                                17.0 + i as f64
                            } else {
                                f64::NAN
                            };
                            lanes
                        ]
                    })
                    .collect();
                let table: Vec<_> = planes
                    .iter_mut()
                    .map(|plane| unsafe {
                        PlaneDescriptor::from_raw_parts(plane.as_mut_ptr(), lanes)
                    })
                    .collect();
                for (mode, kernel) in [
                    ("scalar", app.scalar_plane_kernel()),
                    ("SIMD", app.simd_plane_kernel()),
                ] {
                    let kernel = kernel.expect("this reproducer requires scalar and SIMD kernels");
                    for i in 0..width {
                        planes[i].fill(3.0 + i as f64);
                    }
                    for i in width..2 * width {
                        planes[i].fill(17.0 + i as f64);
                    }
                    for plane in &mut planes[2 * width..] {
                        plane.fill(f64::NAN);
                    }
                    let status =
                        unsafe { kernel(std::ptr::null(), table.as_ptr(), 0, app.params.as_ptr()) };
                    assert_eq!(status, 0);
                    let overwritten = (0..2 * width).any(|i| {
                        planes[i].iter().any(|value| {
                            *value
                                != if i < width {
                                    3.0 + i as f64
                                } else {
                                    17.0 + i as f64
                                }
                        })
                    });
                    assert!(
                        !overwritten,
                        "input modified: complex={complex}, O{opt}, {mode}, constant={all_unused}"
                    );
                    for i in 0..width {
                        let expected = if all_unused {
                            7.0 + 2.0 * i as f64
                        } else {
                            6.0 + 2.0 * i as f64
                        };
                        for lane in 0..if mode == "scalar" { 1 } else { lanes } {
                            assert_eq!(planes[2 * width + i][lane], expected,
                                       "output: complex={complex}, O{opt}, {mode}, constant={all_unused}, lane={lane}");
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

fn pass(what: &str) {
    println!("**** test {:?} passed. ****", what);
}

pub fn main() -> Result<()> {
    println!("starting...");

    test_simple()?;
    pass("simple");

    test_pi_viete(false)?;
    pass("pi_viete");

    test_loops()?;
    pass("loops");

    test_fast()?;
    pass("fast");

    test_fact()?;
    pass("fact");

    test_memory(100)?;
    pass("memory");

    for p in 0..50 {
        test_external(p)?;
    }
    pass("external");

    test_external_evaluators()?;
    pass("external evaluator");

    test_multiple()?;
    pass("multiple");

    test_output_reuse()?;
    pass("output reuse");

    declared_unused_inputs_do_not_shift_outputs()?;
    pass("unused inputs");

    Ok(())
}
