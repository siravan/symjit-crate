use anyhow::Result;
pub use num_complex::{Complex, ComplexFloat};
use symjit::{Composer, Config, Defuns, Slot, Translator};

fn compile_external_evaluators(direct: bool, complex: bool) -> Result<symjit::Application> {
    let mut config = Config::default();
    config.set_complex(complex);
    config.set_direct(direct);
    config.set_debug_scalar(false);

    let mut translator = Translator::new(config.clone());
    translator.set_num_params(2);
    translator.append_mul(&Slot::Out(0), &[Slot::Param(0), Slot::Param(1)], 0)?;
    let f = translator.compile()?.seal()?;

    let mut defuns = Defuns::new();
    defuns.add_applet("f", f);
    config.set_defuns(defuns);
    config.set_debug_scalar(complex && !direct);

    // Compile f(y) + f(x). The call order makes the incorrect result match the original report.
    let mut translator = Translator::new(config);
    translator.set_num_params(2);
    translator.append_constant(Complex::new(7.0, -2.0))?;

    translator.append_fun(
        &Slot::Temp(0),
        "f",
        &[Slot::Param(0), Slot::Const(0)],
        false,
    )?;

    // translator.append_mul(&Slot::Temp(0), &[Slot::Param(0), Slot::Param(1)], 0)?;
    translator.append_add(&Slot::Out(0), &[Slot::Temp(0), Slot::Param(1)], 0)?;
    Ok(translator.compile()?)
}

// external call bug fixed in v2.22.1
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

// external call bug fixed in v2.22.1
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

fn pass(what: &str) {
    println!("**** test {:?} passed. ****", what);
}

pub fn main() -> Result<()> {
    test_external_evaluators_real()?;
    pass("external real evaluator");

    test_external_evaluators_complex()?;
    pass("external complex evaluator");

    Ok(())
}
