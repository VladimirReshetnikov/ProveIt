# Constructive Stokes in intuitionistic primitive recursive arithmetic

Research package prepared for Vladimir Reshetnikov, November 21, 2026.

The report proves a quantitative constructive Stokes theorem for **supplied
effective data**: primitive-recursive rational approximation procedures,
uniform continuity moduli, and first-order remainder certificates. It
constructs the integrals from finite sums and proves their equality through
explicit rational estimates. The result extends to finite oriented chains
of certified `C²` parameterizations and ambient forms with certified `C¹`
coefficients.

The human-readable proof and its reduction to first-order iPRA are developed
in full. The accompanying Lean files are **uncompiled proof scripts and a
formalization outline**. This package does not claim a completed,
kernel-checked Lean formalization of the full analytic theorem.

## Main result

For each fixed collection of primitive-recursive coefficient procedures and
moduli satisfying the report's arithmetic certificates, iPRA proves

\[
\int_C d\omega=\int_{\partial C}\omega
\]

as equality of primitive-recursive regular Cauchy names. The statement is a
schema in fixed primitive-recursive definitions, with ordinary number
parameters allowed. It does not assume a total primitive-recursive evaluator
for arbitrary primitive-recursive program codes.

For a single `k`-cube, the key finite estimate is

\[
|V_{n,p}-B_{n,p}|
\le k2^{-t}+k(2N+1)2^{-p},\qquad N=2^n,
\]

provided the mesh meets the supplied first-order remainder modulus at
precision `t`. The discrete increment sum equals the outer-face sum exactly.
The displayed estimate accounts for every sampled derivative and endpoint
error before passing to names.

Write `ell(k)=ceil(log₂ k)` for `k≥1`, computed by bounded search, and replace
the supplied moduli by nondecreasing majorants. The common schedule is

\[
\begin{aligned}
t_r&=r+\ell(k)+4,\\
n_r&=\max\{r,\bar\mu_F(t_r),\bar\mu_G(t_r),\bar\tau(t_r)\},\\
p_r&=n_r+t_r+2,\\
V_r&=V_{n_r,p_r},\qquad B_r=B_{n_r,p_r}.
\end{aligned}
\]

The report proves the following rates:

| Estimate | Bound | Index condition |
| --- | --- | --- |
| Same-index Stokes defect | `abs(V_r-B_r) ≤ (7/64) 2^(-r)` | Every `r` |
| Volume-name refinement | `abs(V_r-V_s) ≤ (3/32) 2^(-r)` | `s≥r` |
| Boundary-name refinement | `abs(B_r-B_s) ≤ (3/16) 2^(-r)` | `s≥r` |
| Cross-index equality | `abs(V_a-B_b) ≤ (19/64) 2^(-r)` | `a,b≥r` |

For a chain with integer multiplicities `c_j`, shift each cell's requested
accuracy by `ceil(log₂(max(1,sum_j abs(c_j))))`. Interior faces cancel using
the supplied matching information and the explicit orientation conventions.

## Scope and assumptions

The construction includes ordinary three-dimensional Kelvin–Stokes as a
special case, together with finite cubical formulations of Green's theorem
and the divergence theorem. Curved cells, boundaries with corners, and finite
linear combinations of cells are included.

The input contains the parameterizations, finite chain, analytic bounds,
uniform moduli, and any matching of interior faces. The theorem does not
extract those data from an arbitrary qualitative assertion about a smooth
manifold, compact set, or continuous function. Its geometric integration is
defined on the supplied oriented parameterized chains.

All analytic shorthand is reduced to rational approximation programs and
first-order arithmetic formulas. The inductive arguments use finite
denominator-cleared identities or inequalities; their invariants are
quantifier-free. Uniform analytic contracts serve as hypotheses supplying
the finite instances used by those inductions.

## Contents

| Path | Contents |
| --- | --- |
| `report/report.pdf` | Compiled mathematical report. |
| `report/report.tex` and the other `.tex` files in `report/` | Complete editable LaTeX source, including the proofs, definitions, formalization plan, and references. |
| `report/figures/` | Vector figures and PNG previews used in the report. |
| `lean/FiniteCore.lean` | Written proof scripts for finite integer telescoping, error accumulation, row cancellation, and square-boundary cancellation; uncompiled. |
| `lean/RepositorySlice.lean` | Written adapters to ProveIt's object-level finite-FTC results and polynomial certificates; uncompiled. |
| `lean/StokesBlueprint.lean.txt` | Detailed definitions, intended theorem statements, invariants, and remaining implementation steps; a design document, not a build target. |
| `lean/README.md` | Lean status, replay instructions, and the distinction between ambient Lean theorems and iPRA object derivations. |
| `code/stokes_reference.py` | Standard-library exact rational implementation of the finite sums and polynomial examples. |
| `code/validate.py` | Reproducible validation runner. |
| `code/make_figures.py` | Figure-generation script; requires Matplotlib. |
| `validation/` | Exact JSON receipts, CSV tables, and any report build or review records. |
| `sources/source_manifest.json` | Pinned repository source URLs, blob hashes, imports, and relevant theorem names. |
| `sources/repository_audit.txt` | Repository reuse analysis and precise limitations of the inspected supporting results. |
| `build_report.sh` | Local LaTeX build command. |

## Worked curved example

The example uses

\[
\sigma(u,v)=(u,v,uv),\qquad
F(x,y,z)=(0,xz,x^2y),\qquad 0\le u,v\le1.
\]

The pullback one-form is

\[
P\,du+Q\,dv,
\qquad P=u^2v^2,\qquad Q=u^2v(1+u),
\]

and the curl flux density is `u*v*(u+2)`. The four oriented edge integrals are
`0`, `1`, `-1/3`, and `0`; both sides of Stokes therefore equal `2/3`.

For exact left-grid evaluations,

\[
V_N=\frac{(N-1)^2(8N-1)}{12N^3},\qquad
B_N=\frac{(N-1)(4N+1)}{6N^2},
\]

\[
B_N-V_N=\frac{(N-1)(11N-1)}{12N^3}.
\]

A common continuity modulus is `mu(t)=t+4`; a diagonal remainder modulus is
`tau(t)=t+2`. The general schedule specializes to
`t=r+5`, `n=r+9`, and `p=2r+16`. Large schedule grids are handled in the
validation by these independently checked formulas, not by enumerating
astronomically large grids.

## Reproduce the executable checks

From the package directory:

```sh
python3 code/validate.py
```

The runner uses only Python's standard library. Every mathematical comparison
uses exact `fractions.Fraction` arithmetic. The supplied receipt records:

- **36** arbitrary-table telescoping cases in dimensions 1 through 4;
- **5** double-boundary checks, in dimensions 2 through 6;
- **6** directly enumerated curved-example grids;
- **48** noisy-evaluation cases checking local and total error budgets;
- **19** large-schedule cases evaluated through the checked formulas.

It also compares polynomial coefficients exactly for the pullback/curl
identity, both Taylor remainders, the power-sum recurrences, and the closed
grid formulas. The JSON receipt records source hashes and the Python version.
These are executable checks supporting the proof, not substitutes for the
proof or an iPRA proof-checker certificate.

## Rebuild the report

The PDF and figures are already included. With a local TeX Live installation:

```sh
bash build_report.sh
```

The script runs `pdflatex` three times to resolve cross-references and uses
local TeX files. Its optional `STOKES_TEX_CACHE` variable selects the scratch
directory for generated format and build-log files.

To regenerate the figures with Python and Matplotlib:

```sh
python3 code/make_figures.py
bash build_report.sh
```

Lean replay commands are provided in `lean/README.md`. They are instructions
for future compilation, not a record of successful compilation in the
environment used to prepare this package.

## Relation to ProveIt

The repository inspection is pinned to commit
`a5688a1b37d62046c894691c3c41f7bdd53976ca` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
Especially useful existing object-level iPRA results are `FiniteFTC`, finite
`Fubini`, `RiemannSumRules`, `SumLemmas`, `SumSplit`, `DyadicNames`, and
`UniformCertificates`. The source audit distinguishes these from research
outlines and ambient Lean results. The package does not bundle or claim to
have rebuilt their complete transitive dependency closure.

A natural destination for later repository integration is
`Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/stokes_ipra/`.
No repository commit, push, or pull request is part of this delivery.
