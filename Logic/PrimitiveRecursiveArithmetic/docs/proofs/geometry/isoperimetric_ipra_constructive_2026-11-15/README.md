# Constructive isoperimetry in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Read first

**isoperimetric_ipra.pdf** is the complete report. It includes the entire
22-page prior planar proof as an attributed appendix. The new report source
is **report/isoperimetric_ipra.tex** and the section sources beside it.

The human arguments are complete for the finite statements and explicitly
specified effective presentations in the coverage table. The Lean files are
**uncompiled formalization outlines**, not completed internal iPRA proofs.
The Python programs are exact reference implementations and finite diagnostics,
not a formal proof checker.

## Main results

- Sharp planar isoperimetry for specified effective boundaries, with a
  uniform rational-polygon core and constructive circle rigidity.
- Isoperimetric quotient/ratio, disk attainment, Dido's semicircle problem,
  and the regular-polygon quotient with monotonicity and an explicit rate.
- Wigner-caustic improvement, constant-width equality, and a quantitative
  width estimate for finite support polynomials and effective C² support
  presentations.
- Both triangle inequalities, radical-free polynomial targets, and
  equilateral equality for nondegenerate triangles.
- A wholly rational Brunn–Minkowski theorem for finite box unions:

  `q^n * vol(X) ≤ vol(Y)  ⇒  vol(X+Y) ≥ vol(X) * (1+q)^n`.

- The sharp higher-dimensional inequality
  `P^n ≥ n^n * omega_n * V^(n-1)` from explicit outer-volume data;
  all rational box unions and balls have verified examples of the data.
- Finite layered Sobolev and cubical BV inequalities, and an explicit
  sufficient norm/coarea contract for an analytic extension.
- Spherical cap equality, finite disjoint cap-union inequalities, radius
  scaling, and complement symmetry.
- Exact finite-graph profiles; the sharp hypercube edge bound with subcube
  equality classification; the complete Harper vertex theorem, including
  all cardinalities, binomial thresholds, and iterated neighborhoods.

The general spherical curve theorem, arbitrary Hadamard manifolds, unrestricted
measure-theoretic generalizations, all higher-dimensional equality sets, and
the full classical W¹,¹ class without effective data are **not** claimed.
The report explains the distinction at each relevant theorem.

## Foundation and repository provenance

The inspected ProveIt commit is:

`22afac4c9db7a0e060c081cc11db0dc96fe59e93`.

The report uses the actual embedded first-order calculus in
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`:
`PR`, `PTm`, `PRAAx`, `Prf`, and `PRA.qfInd`. Its specified toolchain is
Lean 4.32.0 with Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`.

`pra_iff_native` transfers an already constructed arithmetic derivation.
It does not convert external Mathlib truth into internal iPRA provability.
The supplied outlines retain this distinction throughout.

The existing planar package is copied under `reused/`, with original source
paths, a commit/blob manifest, and historical validation records. Its own
older foundation snapshot is preserved rather than silently rewritten.
`reused/SOURCE_BLOBS.json` identifies byte-exact upstream text copies.

## Files

| Path | Purpose |
|---|---|
| `isoperimetric_ipra.pdf` | Complete compiled report, including the planar appendix |
| `report/*.tex` | Main report and individual mathematical sections |
| `lean/Outline.lean` | Finite data, theorem propositions, and internal iPRA proof targets |
| `lean/AnalyticInterfaces.lean` | Effective geometric and analytic presentation interfaces |
| `lean/README.md` | Source audit and completion roadmap |
| `code/box_bm.py` | Exact matched-cut Brunn–Minkowski reference algorithm |
| `code/hypercube_verify.py` | Exact exhaustive small-cube and compression checks |
| `code/plane_checks.py` | Exact support-function and Wigner normalization checks |
| `code/triangle_checks.py` | Radical-free triangle and equality diagnostics |
| `code/run_checks.py` | Runs the new diagnostics into the requested output directory |
| `audit/` | Recorded validation results and PDF verification summary |
| `reused/` | Attributed upstream planar source, PDF, code, Lean outlines and provenance |
| `build.sh` | Standard pdfLaTeX/latexmk rebuild |
| `MANIFEST.sha256` | SHA-256 hashes of packaged files |

## Reproduce the finite diagnostics

Python 3.10 or later, standard library only:

```sh
python3 code/run_checks.py --output-dir audit_rerun
```

The recorded run includes all 65,814 cube families in dimensions 0–4,
104 Laurent-polynomial cases, 200 reciprocal-telescope checks, 29 rational
box cases, and 7,825 integer-side triangle cases (including degeneracies),
plus 2,197 substitution-identity cases. These counts concern finite tests,
not a substitute for the universal human proofs.

The reference box example verifies the lower-bound chain
`12 ≤ 25/2 ≤ 15`, with a matched rational cut at `2/3`.

Historical planar diagnostics in `reused/verification/` are preserved as
upstream artifacts. To rerun them without overwriting provenance files:

```sh
python3 reused/code/verify.py audit_rerun/planar_exact_checks.json
python3 reused/code/dyadic_spectral_check.py --output audit_rerun/planar_spectral_checks.json
```

## Rebuild the PDFs

The supplied PDF is ready to read. With a functioning TeX Live installation
containing the packages named in the source preambles:

```sh
sh build.sh
```

The script builds the reproduced planar appendix and then the complete
report. It prefers `latexmk`, falling back to repeated `pdflatex` runs.
Generated auxiliary files are confined to `build/`.

## Lean completion

The two new Lean files and the three preserved upstream files are explicitly
marked as outlines. They have not been elaborated in this session. Read
`lean/README.md` and the report's repository section for exact proof
obligations. The final target is an actual closed term of the appropriate
`Prf PRAAx [] ...` type, after verified compilation of the specified finite
algorithm to a fixed `PR` symbol. No complete such derivation is supplied.

