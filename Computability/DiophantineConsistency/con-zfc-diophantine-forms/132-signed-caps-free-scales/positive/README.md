# Polynomial radical centering

Two new exact polynomial DAGs in ten strictly positive integer unknowns:

| File | Live binary operations | Exact total degree |
|---|---:|---:|
| first.json | 102 | 253 |
| second.json | 104 | 252 |

Both have a positive zero exactly when the retained coherent source61/native/controller refutation predicate is true. Absence of a positive zero expresses Con(ZFC) at that calibration. These are ordinary unbounded reductions, not new Lean endpoints or proofs of consistency.

The new mechanism subtracts a polynomial approximation to DE/(2A) from the fused radical's sharp center ADE. An even strong-period coefficient removes all half-integer coefficients. Soundness is certified by an exact whole-polynomial map into the retained uncentered polynomial, positive on the entire positive domain. Completeness uses fresh even-period Pell witnesses and an explicit positive carrier, including native t=0.

This is a modest degree/cost tradeoff: degree 254 at 97 operations remains cheaper; the new points buy degrees253 and252 at102 and104 operations. No nine-variable or global-minimality claim is made.

PROOF.md contains the full formulas, both directions, highest homogeneous forms and exact gate accounting. The complete prior package, source theorem texts and authentic coefficient payload are retained in prior/. No coefficients from a different controller tuple are mixed in.

Replay with Python3 standard library:

    python -B build.py --check
    python -B check.py
    python -B -O build.py --check
    python -B -O check.py
