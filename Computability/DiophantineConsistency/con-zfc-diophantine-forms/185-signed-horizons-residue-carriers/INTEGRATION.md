# Integration notes

## Suggested placement

Add this directory beneath
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`, using
the next available package number and a suffix such as
`signed-horizons-residue-ordinates`. The repository was inspected at
commit `02a78a08603cbae248c19c23a75907c6c6bd6443`; a later available
number should be chosen at integration time.

Keep the three component directories together: their relative paths are
used by the LaTeX sources and replay tools. The package runs outside a
checkout and requires no downloads. It is not an automated Git patch.

## Suggested catalogue entry

> **Signed horizons and residue-encoded Pell witnesses.** Completed
> ordinary ZFC-calibrated equations: a 214-integer-variable quartic with
> 153 quadratic residuals and exact height 655,360; a 212-variable quartic
> with larger coefficients; fourteen-positive-variable compact forms at
> 66 operations/degree 174 and 68 operations/degree 146; a fully explicit
> 36-integer-variable lift of degree 288 at 145 operations; and eight
> directly compiled pooled-power profiles down to 86 variables at degree
> 2,097,780. Includes proofs, fixed coefficients, literal equations,
> exact finite replay certificates, source pins, and editable article.
> Inherited C222/ZF/ZFC or native/P66 calibration remains identified;
> no new end-to-end proof-assistant certificate is claimed.

## Definition and trust boundary

- The final Q214 and Q212 equations are in `quartic/affine_horizons/`.
  Their JSON coefficient lists, not informal semantic exponent notation,
  define the ordinary quartics.
- The final compact equations are in `compact/equations/` and
  `compact/integer_equations/`. The `.bin` files in
  `compact/coefficients/` are part of their complete fixed definition;
  `rebuild_coefficients.py` regenerates and authenticates them.
- The eight final direct circuits are in `direct/equations/`. Their
  quantified inputs are listed explicitly. Circuit registers do not add
  quantified variables. The equation is the circuit's final polynomial
  output equal to zero, with domain unrestricted integers.
- Intermediate source equations and certificates under `sources/`,
  `inherited/`, and similar paths have their own documented role. They
  should not be counted as additional new endpoints.
- Preserve each complete native coefficient tuple. Mixing one port from
  another construction invalidates the inherited calibration even if
  several size inequalities survive.

The theorem is the formalizable equivalence with the existence of a
finite refutation from the specified `ZFCax_s` presentation. It is not
an external-standard-model-only assertion and does not assume ZFC's
consistency. The logical calibration includes semantic completeness
arguments; the entire chain is not newly implemented as a primitive
recursive proof translator.

## Verification and future edits

Run `python3 -B verify_all.py` and `python3 -O -B verify_all.py` before
integration. `SHA256SUMS` authenticates this frozen submission. After an
intentional code, documentation, or PDF edit, use `--skip-manifest` for
the mathematical replay and regenerate the manifest as part of a new
release. Do not remove verification checks to hide a changed equation.

The report can be rebuilt from `report/report.tex`; all included LaTeX
files are present. `report/emit_quartic_appendix.py --check` compares the
complete printed Q214 residual list with the verified JSON source.

If headline tables are updated, keep metrics in distinct columns:
domain, quantified variable count, exact degree, binary evaluation
operations, expanded coefficient height/bound, and coefficient bytes.
A maximum circuit literal of 256 is not an expanded height of 256.

The signed affine source change uses cofinality, not a pointwise inverse
to the old quadratic horizon. The subsequent affine projection and
unit-linear eliminations do have explicitly stated polynomial inverses.
This distinction should remain visible in future summaries.

## Known limits and next useful work

The supplied finite verifier does not kernel-check the inherited
unbounded Pell, native window, or C222/ZF/ZFC theorems. A formalization
effort should separately target the new sign bootstrap, residue-carrier
extraction, integer-domain relaxation, and protected-row commutation.

The direct balanced quartic improves variable count while increasing
support and height. The compact formulas improve selected evaluation and
degree metrics while retaining large fixed constants. No global
simplicity minimum, new integer-variable record, or worldwide-priority
claim is part of this submission.
