# Linear Pell orientation: a 306-integer quartic

The finished equation is `integer306/equation.json`. All its coordinates
range independently over the integers. It is the sum of squares of every
listed quadratic residual, not the square of their sum.

| Equation | Variables | Residuals | Degree | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Pinned parent | 324 | 208 | 4 | 5,808 | 128,446 |
| New | **306** | **206** | **4** | 6,259 | 128,446 |

The new ordinary theorem proves existence of an integer zero equivalent to
that of the pinned parent. Composing with the parent's retained C222/ZF/ZFC
calibration, ZFC proves that the new equation has no integer solution if and
only if Con(ZFC). This does not prove consistency or global minimality and
does not supply a new end-to-end proof-assistant certificate.

The new idea is to add nine **linear** orientation terms `1-X_i` to the
existing bounded Pell-index error pool. Modulo `A-1`, these terms lie in
`{0,2}`. The small nonnegative residue sum must vanish, which orients nine
Pell pairs. Their signed power requests then give nonnegative encoded
indices. A raw divisibility argument makes the reciprocal index positive;
one eight-factor strict product makes the other eight positive. Nine
three-variable sign graphs disappear. The last product multiplication is
fused into the final positivity row.

`PROOF.md` gives the complete new ordinary argument, including negative and
zero indices, the noncircular bootstrap, both witness maps, and the private
quotient adjustment. `signed_section.tex` is the corresponding report input.
The exact parent equation, centering certificate and parent arithmetic proof
are retained under `parent/`. Their Git blob identities are checked.

Standard-library Python 3.10 or later suffices:

    python3 -B verify.py
    python3 -B -O verify.py

Reconstruction overwrites the generated mathematical files deterministically:

    python3 -B build.py

The verifier is independent of the producer and performs 929 exact checks,
including every coefficient. Four deliberately corrupted artifacts are
rejected even when their output hashes are refreshed. `VERIFICATION.json`
records the successful run. The separate `review/` directory records the
second-agent mathematical and literal review, with its own scope.

Every residual is also readable in `integer306/residuals.txt`; variable
names are mapped in `variables.tsv`. The sparse coefficient format is
`[coefficient,[indices]]`, with repeated indices indicating repeated factors
and an empty index list indicating a constant term.

The transformation preserves the native front and every retained parent
coordinate except the private pool quotient. The two maps adjust that
quotient by the exactly integral `sum(1-X_i)/(A-1)` and choose fresh ternary
guard witnesses. The witnesses need not be unique.

This is a new complete arithmetic reduction relative to the inspected
repository. It saves variables and rows while increasing expanded support
by 451 terms. Inherited proofs and the C222 calibration remain explicitly
identified dependencies; finite checks do not prove those unbounded facts
by testing finitely many candidate assignments.
