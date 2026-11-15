# An explicit prime number theorem in iPRA

The complete human-readable argument is in `pnt_ipra.pdf`; its source is
`tex/pnt_ipra.tex` and the three included section files. The paper proves an
explicit arithmetic formulation of PNT with quantifier-free induction in
intuitionistic primitive recursive arithmetic, and explains the passage to
the conventional logarithmic statement.

For `k >= 1`, set `q = 8k`, `D = 2^20 q^3`, and
`N(k) = 2^(2^(D^2+2))`. The arithmetic conclusion, for `n >= N(k)`, is

    k * abs(pi(n)*A(n) - n*F(n)) <= n*F(n),

where `F(n) = (n^2)!` and `A(n) = sum(F(n)/j, j=n+1,...,n^2)`.
The modulus is intentionally enormous and should be handled symbolically.

## Contents

- `pnt_ipra.pdf`: the complete report.
- `tex/`: the full LaTeX source, with all proof sections and bibliography.
- `lean/RationalPNT.lean`: executable natural-number definitions, the exact
  target and explicit modulus, plus small generic helper proofs.
- `lean/ObjectTarget.lean`: the required deeply embedded iPRA endpoint and
  generic transport wrappers for ProveIt's ConciseIPRA calculus.
- `lean/STATUS.txt`: precise formalization status and remaining obligations.
- `code/arithmetic.py`: exact rational/natural-number implementations.
- `code/check_arithmetic.py`: finite exact checks, including the Selberg
  convolution identity as a polynomial identity in formal prime logarithms.
- `verification.json`: the recorded results of those finite checks.
- `sources.json`: source and repository provenance.

## Status

The mathematical argument is a human-readable proof, including the finite
arithmetic and induction bookkeeping. The Lean files are an **uncompiled
formalization outline**, not a completed formal proof. No Lean executable was
available in the preparation environment. The files do not introduce a PNT
axiom or present a conditional wrapper as the missing theorem.

Finite computation checks validate definitions and proof identities on their
stated bounded ranges. They do not prove the universal prime number theorem.

## Rebuilding

With a working TeX Live installation:

    cd tex
    latexmk -pdf -interaction=nonstopmode -halt-on-error pnt_ipra.tex

With Python 3 and no third-party dependencies:

    python3 code/check_arithmetic.py

For the Lean integration, use the `ConciseIPRA` Lake project in ProveIt at
commit `b03925cccc76d55b9dc2a00864a5e0544b64aa7f` or port the explicitly
identified interfaces to a newer audited revision. The article gives the
module milestones and the exact final certificate type.

Prepared November 14, 2026.
