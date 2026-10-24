# Completed direct-Horn consistency equation

Recommended artifact: fixed_base/equation_integer.json, a fully materialized ordinary polynomial over27,916 unrestricted integers, exact degree4,758,275nonzero monomials. In ZFC, its lack of integer zeros is provably equivalent to Con(ZFC).

Natural companion: the sum of squared explicit residuals in fixed_base/residuals_affine.json uses16,036 nonnegative variables, exact degree4. Rebuilding emits the redundant collected equation_affine.json.

This is not a numerical record. It completes the previously unmaterialized direct-proof branch, independent of K215 execution and Jones' universal polynomial. The structural change removes the entire height-accumulator stream using M0=2^(2mN+1), with m an independent bound on proof labels. Only one beta stream remains, with29localwitnesses. The CRT coordinate bound U is deliberately separate. Affine gate elimination removes addition and scalar-multiplication wires. The integer conversion constrains only semantic inputs to be nonnegative.

The mathematical proof is in section.tex, including source calibration, all arithmetic representation interfaces, and both directions of equivalence. No new end-to-end Lean/Rocq certificate or global minimality claim is made.

## Exact file format

Each polynomial term [coefficient,[indices]] denotes coefficient times the product of variables with the listed zero-based indices. Repetitions are powers. No variable exponent, bounded quantifier, factorial, binomial coefficient, unspecified constant, or compiler choice remains in equation_integer.json.

The compact release omits redundant expanded intermediates. It retains the complete integer polynomial, natural residuals, arithmetic circuit, row polynomial, fixed Horn relation, builders, proof sources, and SHA-256 replay manifest. The affine map and nonnegativity residual list are regenerated before the independent audits and must match their frozen hashes exactly; they are not duplicated in the ZIP.

## Reproduction

From fixed_base/:
    python build_direct.py
    python check_direct.py
    python reduce_affine.py
    python verify_replay.py

The final command compares all regenerated outputs against hashes recorded before packaging, including the complete integer polynomial. Both normal Python and python -O execute the checks. Independent semantic and algebraic audits are in the sibling direct_audit packet.
