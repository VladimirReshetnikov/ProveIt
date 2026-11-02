# Positive-binding reductions of AQ22

The generated [candidate17.json](candidate17.json) is a 17-positive-variable,
degree-32 sum-of-squares circuit with 99 arithmetic rows and eight squared
residuals. It is obtained from the pinned 22-variable, degree-10 graph by
simultaneously eliminating five explicit binding variables. This is a finite
algebraic candidate and an ordinary integer witness argument. A
[guarded historical Lean author run](../../reviews/ipra-aq17-guarded-author/README.md)
compiled its transport and native and standard iPRA endpoints in one fresh
overlay. Its [independent artifact audit](../../reviews/ipra-aq17-guarded-author-independent-audit/README.md)
passed. A later [historical paired run](../../reviews/ipra-aq17-historical-pair-terminal/README.md)
matched all 44 additions and passed an [independent complete-result audit](../../reviews/ipra-aq17-historical-pair-independent-audit/README.md).
It has not been
identified with the equation in the project's current PDF. A separate
[base-10 candidate display](equation32-17.pdf) names all 17 positive unknowns
and includes the complete 99-operation circuit. An [independent audit](../../reviews/equation32-17-independent-audit/README.md)
checked the preceding PDF; a [separate review](../../reviews/equation32-17-wording-independent-audit/README.md)
passed for its author-run wording. A [later review](../../reviews/equation32-17-paired-wording-independent-audit/README.md)
passed for the paired-run wording.
Its fixed decoder and rank recipe
retain the project's documented manual-transcription boundary.

The maintained [14-variable degree-30 equation](../../equation30-direct.pdf)
uses 90 circuit operations, so it is smaller on all three of those stated
metrics. The AQ17 construction extends the freshly rebuilt AQ29-to-AQ22 proof
chain; its proof provenance and replay status are tracked separately.

All circuit subtraction is integer subtraction. Let

- `q = 1 + J * beta`, `qm = J * beta`, and `M = q^3 * qm`;
- `U = Y * q^2`, `E = X * Y`, `kY = Y * (eta + zeta)`, and `ell = E * kY`;
- `c = eta + kY`, `a = E + Y`, and `DeltaComputed = 3 + 4*a + a^2`.

Remove the binding variables `scaleVariable`, `mainScaleVariable`,
`ellVariable`, `cSquareVariable`, and `deltaVariable` and substitute,
respectively, `M`, `U`, `ell`, `c^2`, and `DeltaComputed`. Delete their five
binding residuals from the sum of squares. All five expressions depend only
on surviving witnesses and ports, so the substitutions are simultaneous.
When the surviving witnesses are positive and `beta > 0`, every expression is
positive: `qm` and `q` are positive; `U`, `E`, `kY`, `ell`, and `c` are
positive; and `DeltaComputed >= 3`. These facts hold for every positive child
assignment, in particular at a child zero.

An AQ22 zero projects to a candidate zero because each deleted binding
residual vanishes. Conversely, reconstructing the five positive coordinates
as above makes the deleted residuals zero and preserves each of the other
eight residuals. A sum of integer squares is zero exactly when all its
summands are zero. Thus the two positive-zero existence statements agree in
ordinary integer mathematics for `beta > 0`. This argument does not by itself
supply a Lean proof that the AQ17 equivalence is provable inside iPRA.

The survey considers all 31 nonempty subsets of these **five specified
bindings**, not all possible equation reductions. For each subset it checks
all 13 original residual identities by exact sparse integer-polynomial
substitution, counts the live circuit rows, and computes the maximal residual
degree. The best degrees at each resulting variable count are:

| Positive variables | Degree | Arithmetic rows | Removed bindings |
| --- | ---: | ---: | --- |
| 21 | 16 | 111 | `mainScaleVariable` or `deltaVariable` |
| 20 | 20 | 108 | Several pairs; see `results.json` |
| 19 | 20 | 105 | `ellVariable`, `cSquareVariable`, `deltaVariable`, or `scaleVariable`, `cSquareVariable`, `deltaVariable` |
| 18 | 28 | 102 | `mainScaleVariable`, `cSquareVariable`, `deltaVariable`, plus either `scaleVariable` or `ellVariable` |
| 17 | 32 | 99 | All five |

These are minima only within this finite family; the gate count is the number
of binary `+`, `-`, and `*` rows in the displayed circuit, including the
squares and their additions. The 20-variable point is dominated within this
family by a 19-variable point with the same degree and fewer rows. Other
bindings with signed right-hand sides need a separate positivity proof and are
not included.

For the 17-variable candidate, the maximum residual degree is 16. Its `A0`
residual contains the witness monomial `J^8 X^2 Y^4 eta^2` with coefficient
exactly `-beta^8`, independent of the other three ports. The coefficient is
nonzero for every positive `beta`, including the actual selected fixed ports:
`CurrentMasks2011.beta_pos_int` proves the required positivity and port 0 is
`beta`. Therefore the leading homogeneous sum of squares is nonzero, so the
full equation has degree **exactly 32** after fixing all four ports. Shifting
positive variables to nonnegative variables preserves the degree.

Reproduce the checks with:

```sh
python3 survey.py
python3 verify_candidate17.py
```

The survey pins the AQ22 graph and emits `results.json` and `candidate17.json`.
The separate checker reads both generated and parent circuits, checks all
original residual substitutions, verifies output square wiring and raw
reconstruction dependencies, checks the specialized leading coefficient, and
rejects arithmetic and output-sign mutations. Both programs reject optimized
Python because their assertions are part of the checks. These checks are not a
Lean replay or a proof of global minimality.
