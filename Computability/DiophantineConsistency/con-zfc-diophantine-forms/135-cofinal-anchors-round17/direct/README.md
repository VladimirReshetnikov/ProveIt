# Direct integer equations in round 17

The final three endpoints are strict_dimension_centered (282 variables, 192 rows, 5491 monomials), strict_grouped_centered (287,197,4313), and strict_sparse_centered (309,219,3922). All are exact quartics of coefficient height 128446 over unrestricted integers. equation.json lists the quadratic residuals and expanded_polynomial.json lists the complete collected sum of squares.

Read PROOF.md for the complete proof map. The inherited round16 direct arithmetic proof is preserved under proofs/INHERITED_ROUND16_DIRECT_PROOF.md, rather than being overwritten by the new proof. The local runtime and two portable input files are self-contained. Ordinary logical-calibration and further inherited arithmetic source files are retained in the release's architecture/proofs closure as listed in CLOSURE.json.

From any working directory, run:

    python /path/to/direct/check_compiled_cap.py /path/to/direct/strict_dimension /path/to/direct/strict_grouped /path/to/direct/strict_sparse --centered /path/to/direct/strict_dimension_centered /path/to/direct/strict_grouped_centered /path/to/direct/strict_sparse_centered --adversarial

Run the same command with python -O. For deterministic reconstruction of the selected sources and centered polynomials, run:

    python /path/to/direct/reproduce.py

The checker does not import the producing compiler. It checks every finite source, guard, factoring, projection and translation identity and every collected quartic coefficient. Its checks are not substitutes for the unbounded mathematical proof.
