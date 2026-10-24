# Eleven unrestricted integers with short divisibility carriers

The three principal equations use the same six literal fixed coefficients.

| File | Domain | Variables | Exact degree | Live binary operations |
|---|---|---:|---:|---:|
| scalar11_original_direct.json | integers | 11 | 488 | 121 |
| scalar11_original_center.json | integers | 11 | 464 | 125 |
| scalar11_q4_center.json | integers | 11 | 440 | 126 |

The two `_reduced` files denote identically the centered polynomials and
expose their degree cancellations. They are audit companions, not smaller
operation-count claims. A naive syntactic degree bound of 488 in a short
centered graph does not override its proved exact degree of 464 or 440.

All definitions and the complete new arithmetic proof are in
`../report/norm_section.tex` and the compiled report. The independent
ordinary review is `../reviews/SYNTHESIS11_INDEPENDENT_REVIEW.md`.
`source/` retains the inherited centered, folding, interpolation,
powered-divisibility, intersective-polynomial, and native calibration
proofs with their notices. These ordinary proofs are separate from the
finite checks below. No new Lean/Rocq endpoint is asserted.

Rebuild and check offline, using Python 3 standard library:

    python3 -B build.py
    python3 -B check.py
    python3 -B -O check.py

The checker does not import the producer. It verifies every live register
in a free polynomial ring, all 35 universal norm coefficients, full graph
liveness, exact operation counts, authentic coefficient bytes and finite
reconstruction, the centered cancellation identity, and a nonzero actual
coefficient attaining each degree. The normal run reconstructs the inherited
coefficient recipe; the optimized run repeats all new checks and authenticates
the same literal bytes. The parent recipe's deliberate normal-mode restriction
is retained.

The primary degree-440 witness coefficient is
`[j^264 w^40 v^52 h^12 s^12 r^24 c^32 z^4] P = 2^476 3^306 beta^264`.
The fixed `beta` is `2^1064921-1`, so the coefficient is nonzero.

The input variables are unrestricted integers. None of the intermediate
names in a DAG is an additional quantified variable. The six coefficient
ports are fixed by `coefficients/BINDING.json`, the compressed literal
numerals, and the included finite constructor; they are not parameters.

The source is ProveIt at `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`, including
the incoming Coprime Projection and Powered Saturation / Factorial Carriers
Round 14 packets. New material is AI-assisted research; inherited material
retains its licenses. Independently reviewed means a separate research-agent
audit in this workflow, not an external human endorsement.
