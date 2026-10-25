# Free-scale first-root carrier

The endpoint has 15 unrestricted integer variables, exact total degree 44, and 111 live binary arithmetic gates (63 multiplications, 26 additions, 22 subtractions). Its no-integer-zero assertion is equivalent in ordinary ZFC to syntactic Con(ZFC), through the explicitly retained source34 native/compiler/refutation theorem.

The new mechanism is a free scale Y, a strengthened positive budget, and an amplified whole-product projection. Magnitude and parity are recovered before the signed Pell bootstrap; the exact scale divisibility is recovered afterward by integer cancellation. No unjustified coprime CRT assumption is made.

This is a lower-degree tradeoff, not Pareto domination: the retained predecessor is 15 variables, degree 48, 108 gates. Applying the same elementary Klo factorization to that old evaluator gives 107 gates. The new degree reduction therefore costs four gates under matched local scheduling.

## Files

- `PROOF.md`: complete ordinary proof, exact dependencies, soundness map, canonical completeness map, exact degree and scope.
- `section.tex`, `standalone.tex`, `standalone.pdf`: mathematical presentation.
- `equation.json`: the literal division-free DAG, with every coefficient bound to complete binary payloads.
- `specification.json`: ordered polynomial abbreviations.
- `build.py`, `circuit.py`: deterministic standard-library builder.
- `review/audit.py`: independently written exact cut-register checker, source-payload authentication, degree attainment, all-gate mutation rejection and finite arithmetic diagnostics.
- `source/`, `SOURCE_PINS.json`: copied immediate mathematical sources and their hashes. The archive must retain the round-15 dependency closure for the upstream compiler theorem and licensing.
- `coefficients/`: all six authentic integer payloads, their binding and recipe.

## Reproduce

Python 3 and SymPy are required for the audit; the builder uses only the standard library.

    python build.py
    python review/audit.py
    python -O review/audit.py

Both audit modes must report pass, 15 variables, degree 44, 111 gates, and 111 rejected gate mutations. The audits do not execute downloaded code or proof search and do not prove the inherited unbounded compiler theorem.

Compile `standalone.tex` with pdfLaTeX twice to regenerate the four-page PDF. It uses standard article, AMS, geometry and hyperref packages.
