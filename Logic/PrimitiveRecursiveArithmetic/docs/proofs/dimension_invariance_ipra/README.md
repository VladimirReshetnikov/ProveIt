# Dimension invariance in intuitionistic primitive recursive arithmetic

**A finite proof using staggered rational grids**  
Prepared for Vladimir Reshetnikov, 15 November 2026.

The report gives a complete human-readable constructive argument for an explicit quantitative version of dimension invariance, together with its first-order arithmetic formulation and a detailed Lean completion plan. The central theorem concerns finite rational tables and requires no real-number equality test or compactness principle.

## Main result

Let `F : {0,...,N}^d -> Q^m`, where `d > 0`, `N >= 1`, and `h > 0` is rational. Use the sup norm. If every pair of points on opposite coordinate faces has image distance at least `h`, and every standard Kuhn simplex has image diameter strictly less than `h/d`, then **`d <= m`**.

The proof supplies a positive finite alternative when `d > m`: a primitive-recursive procedure returns either an opposite-face pair with image distance below `h`, or two vertices of one Kuhn simplex with image distance at least `h/d`. It uses a complete cubical Sperner parity argument, then shifts the target grid by `(i-1)/d` for source direction `i`. Different shifts have boundaries separated by at least `h/d` in one target coordinate, which forces the dimension inequality.

For a uniformly presented map on a cube, the finite result yields rational opposite-face points with images within any requested dyadic tolerance. Applying this to a homeomorphism and its inverse proves equality of dimensions **for presentations with the explicitly specified primitive-recursive rational evaluators and local uniform moduli**. First-order iPRA does not quantify over arbitrary real functions: the finite theorem is a numerical theorem, while the map formulation is a schema for fixed procedures. The report states the forward and one-scale inverse hypotheses arithmetically and explains the distinction.

## Contents and status

| Artifact | Purpose and status |
| --- | --- |
| `dimension_invariance.pdf` | Compiled mathematical report, including all finite proofs, quantitative sampling constants, the iPRA induction audit, and the Lean completion path. |
| `dimension_invariance.tex` | Complete editable LaTeX source. |
| `lean/Blueprint.lean` | **Unfinished documentation-only outline.** Proposed declarations are inside a comment; this file is not a completed formal proof and was not compiled. |
| `lean/README.md` | Verified integration interfaces and remaining formalization work. |
| `code/finite_dimension.py` | Exact-rational witness extractor and independent checker for individual finite witnesses. |
| `code/validate.py` | Reproducible finite implementation audits. |
| `code/validation.json` | Recorded successful audit results and deterministic random seed. |
| `code/example_input.json`, `code/example_certificate.json` | Worked two-dimensional source and one-dimensional target example. |
| `source_manifest.json` | Source provenance, pinned repository paths, and verification boundaries. |
| `verification_summary.json`, `SHA256SUMS` | Final build and review status, and hashes of the delivered files. |
| `build.sh` | Portable three-pass LaTeX build script. |

**Formal status:** the human-readable argument is complete. A complete Lean derivation remains to be constructed. The Python checker verifies the particular rational witness supplied to it; it does not check an iPRA derivation or prove the general theorem. No full upstream ProveIt build was run for this report.

## Reproduce the executable checks

The code uses Python 3.10 or later and only the standard library, including `fractions.Fraction`. It rejects floating-point coordinate inputs. Run from this directory:

```sh
python3 code/validate.py
python3 code/finite_dimension.py code/example_input.json
python3 code/finite_dimension.py code/example_input.json --check code/example_certificate.json
```

The last command returns `{"valid": true}` and exit status zero for the supplied example. The audit uses seed `20261115` and records:

| Check | Count |
| --- | ---: |
| Exhaustive admissible colorings | 5,223 |
| Further admissible colorings with independent facet-incidence reconstruction | 160 |
| Exhaustive rational tables | 625 |
| Further rational tables | 132 |
| Exact cell-boundary cases, including negative values | 756 |
| Staggered-grid separation cases | 4,116 |
| Zero-dimensional target cases | 8 |
| Rejected invalid or inapplicable inputs | 6 |
| Rejected invalid certificates | 7 |

These are finite implementation checks. The general parity and dimension arguments are proved in the article; the checks do not replace them.

Input rows follow lexicographic source-vertex order with the last coordinate varying fastest. Coordinates may be integers or exact rational strings such as `"-3/7"`. The JSON field `delta` denotes the article's rational separation scale `h`; it is distinct from the requested collision tolerance denoted by delta in the sampling section.

## Rebuild the PDF

Use a standard LaTeX installation providing `pdflatex` and the packages listed in the source, including `lmodern`, `microtype`, the AMS packages, `mathtools`, `geometry`, `enumitem`, `booktabs`, `longtable`, `tikz`, `listings`, `fancyhdr`, `needspace`, `xurl`, `hyperref`, and `bookmark`.

```sh
sh build.sh
```

The script runs `pdflatex` three times to resolve the table of contents and cross-references. It performs no environment-specific TeX configuration.

## Repository integration

The inspected ProveIt commit is **`daade0300022828cdba33a324d987997fee9fa08`**. The root configuration pins Lean and mathlib to **`v4.32.0`**.

The existing `ConciseIPRA` library provides the object-language syntax `PR` and `PTm`, intuitionistic derivability `Prf`, the axiom family `PRAAx`, and the induction rule `PRA.qfInd`. Its `NativeBiInterpretation` module supplies `pra_iff_native`, which transfers an actual iPRA derivation into the concise native calculus. The intended formal endpoint is `[] ⊢[PRAAx] finiteDimensionFormula`, followed by this existing bridge. An ordinary Lean theorem about real spaces would be a different result.

The substantial new formalization tasks are explicit Kuhn incidence pairing, cubical Sperner parity, rational cell arithmetic, and their object-language arithmetic derivations. The blueprint identifies a quantifier-free parity invariant by fixing the full input labeling and restricting it to nested lower faces. No universal primitive-recursive evaluator is assumed.

Relevant repository source contents and configuration were inspected; archived draft ZIPs were listed but their internal mathematical arguments were not imported. No suitable existing topological Sperner result was located in the inspected sources and searches. The source manifest distinguishes these observations from a full repository audit or build.

## References

- Eric W. Weisstein, [Dimension Invariance Theorem](https://mathworld.wolfram.com/DimensionInvarianceTheorem.html), MathWorld: the classical target statement.
- Michael Müger, [A remark on the invariance of dimension](https://arxiv.org/abs/1310.8090): the Kulpa–Müger cubical Sperner boundary convention and related dimension argument. The report gives the needed finite proof in full and makes no priority claim.
- Takayuki Kihara, [The Brouwer invariance theorems in reverse mathematics](https://doi.org/10.1017/fms.2020.52), *Forum of Mathematics, Sigma* 8 (2020), e51: scope and reverse-mathematical context. Its unrestricted embedding/injection result is distinguished from the homeomorphism-only question.
- [ProveIt ConciseIPRA at the inspected commit](https://github.com/VladimirReshetnikov/ProveIt/tree/daade0300022828cdba33a324d987997fee9fa08/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA): the formal arithmetic and interpretation infrastructure.
