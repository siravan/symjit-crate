use anyhow::Result;
pub use num_complex::{Complex, ComplexFloat};
use symjit::{Composer, Config, Defuns, Slot, Translator};

fn compile_external_evaluators(direct: bool, complex: bool) -> Result<symjit::Application> {
    let mut config = Config::default();
    config.set_complex(complex);
    config.set_direct(direct);
    config.set_debug_scalar(false);

    let mut inner = Translator::new(config);
    inner.set_num_params(2);
    inner.append_mul(&Slot::Out(0), &[Slot::Param(0), Slot::Param(1)], 0)?;
    let f = inner.compile()?.seal()?;

    let mut defuns = Defuns::new();
    defuns.add_applet("f", f);

    let mut config = Config::default();
    config.set_complex(complex);
    config.set_direct(direct);
    config.set_debug_scalar(false);
    config.set_defuns(defuns);
    // config.set_debug_bytecode(!complex && !direct);

    let mut outer = Translator::new(config);
    outer.set_num_params(2);
    outer.append_constant(Complex::new(7.0, -2.0))?;

    outer.append_fun(
        &Slot::Temp(0),
        "f",
        &[Slot::Param(0), Slot::Const(0)],
        false,
    )?;

    outer.append_add(&Slot::Out(0), &[Slot::Temp(0), Slot::Param(1)], 0)?;
    Ok(outer.compile()?)
}

fn test_external_evaluators_real() -> Result<()> {
    let args = [5.0, 2.0];
    let expected = 37.0;
    let optimized = compile_external_evaluators(false, false)?.evaluate_single(&args);
    let direct = compile_external_evaluators(true, false)?.evaluate_single(&args);

    eprintln!("expected:             {expected}");
    eprintln!("optimized translator: {optimized}");
    eprintln!("direct translator:    {direct}");

    assert_eq!(optimized, expected, "optimized translation is incorrect");
    assert_eq!(direct, expected);
    Ok(())
}

fn test_external_evaluators_complex() -> Result<()> {
    let args = [Complex::new(5.0, -2.0), Complex::new(2.0, 3.0)];
    let expected = Complex::new(33.0, -21.0);
    let optimized = compile_external_evaluators(false, true)?.evaluate_single(&args);
    let direct = compile_external_evaluators(true, true)?.evaluate_single(&args);

    eprintln!("expected:             {expected}");
    eprintln!("optimized translator: {optimized}");
    eprintln!("direct translator:    {direct}");

    assert_eq!(optimized, expected, "optimized translation is incorrect");
    assert_eq!(direct, expected);
    Ok(())
}

fn test_external_evaluators_real_simd() -> Result<()> {
    let args: Vec<f64> = (0..100).map(|x| f64::from(x)).collect();
    let expected: Vec<f64> = (0..100)
        .step_by(2)
        .map(|x| f64::from(7 * x + x + 1))
        .collect();

    let mut optimized = vec![0.0; 50];
    let mut direct = vec![0.0; 50];

    compile_external_evaluators(false, false)?.evaluate_matrix(&args, &mut optimized, 50);
    compile_external_evaluators(true, false)?.evaluate_matrix(&args, &mut direct, 50);

    eprintln!("expected:             {:?}", expected[10]);
    eprintln!("optimized translator: {:?}", optimized[10]);
    eprintln!("direct translator:    {:?}", direct[10]);

    assert_eq!(
        optimized[10], expected[10],
        "optimized translation is incorrect"
    );
    assert_eq!(direct[10], expected[10]);
    Ok(())
}

fn test_external_evaluators_complex_simd() -> Result<()> {
    let args: Vec<Complex<f64>> = (0..100).map(|x| Complex::new(x as f64, x as f64)).collect();
    let mut expected = vec![Complex::new(0.0, 0.0); 50];
    let mut optimized = vec![Complex::new(0.0, 0.0); 50];
    let mut direct = vec![Complex::new(0.0, 0.0); 50];

    for i in 0..50 {
        expected[i] = Complex::new(7.0, -2.0) * args[2 * i] + args[2 * i + 1];
    }

    compile_external_evaluators(false, true)?.evaluate_matrix(&args, &mut optimized, 50);
    compile_external_evaluators(true, true)?.evaluate_matrix(&args, &mut direct, 50);

    eprintln!("expected:             {:?}", expected[10]);
    eprintln!("optimized translator: {:?}", optimized[10]);
    eprintln!("direct translator:    {:?}", direct[10]);

    assert_eq!(
        optimized[10], expected[10],
        "optimized translation is incorrect"
    );
    assert_eq!(direct[10], expected[10]);
    Ok(())
}

fn pass(what: &str) {
    println!("**** test {:?} passed. ****", what);
}

pub fn main() -> Result<()> {
    test_external_evaluators_real()?;
    pass("external real evaluator");

    test_external_evaluators_complex()?;
    pass("external complex evaluator");

    test_external_evaluators_real_simd()?;
    pass("external real simd evaluator");

    test_external_evaluators_complex_simd()?;
    pass("external complex simd evaluator");

    Ok(())
}
