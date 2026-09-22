# Surquaternions

## Algebra, Infinitesimal Geometry, and Support-Controlled Analysis

`article.pdf` (61 pages) and `article.tex` are one **merged** research report on Hamilton's
quaternion division algebra over the surreal numbers,

    H_No = No + No i + No j + No k,     i^2 = j^2 = k^2 = ijk = -1,

with central surreal coefficients. The algebra is **noncommutative**, and that is the whole
difficulty of the subject: conjugation, multiplicativity of the modulus, valuation and
leading coefficients, polynomial evaluation, matrix adjoints, exponential laws and every
chain rule all need separate treatment from the commutative surcomplex case. No commutative
argument is reused anywhere in the report; every commutative result quoted from a companion
report is cited for orientation and reproved over `H`.

Every `\label` in `article.tex` carries the prefix `squat:`.

## What this report is

A three-level development, with the levels never silently mixed:

1. **Finite algebra over an arbitrary real closed field `F`** — division, conjugation, the
   `F`-valued modulus, complex slices and centralizers, conjugacy spheres, explicit square
   roots, the algebraic spin/rotation description with two independent surjectivity proofs,
   two rational charts on the unit group, quaternionic Möbius maps, one-sided polynomials
   with a constructive fundamental theorem and a complete zero-class algorithm, and
   finite-dimensional Hermitian spectral theory with SVD and polar decomposition.
2. **Set-sized Hahn workspaces** `D_Gamma = H(R((t^Gamma)))` — quaternion-valued normal
   forms with a **noncommutative** residue algebra `H_R`, exact multiplicative valuation
   and leading coefficients, the all-lengths Neumann support lemma (proved via Higman's
   finite-word lemma), the exact geometric inverse with its truncation certificate, the
   infinitesimal Hahn exponential and logarithm, BCH at positive valuation, the filtered
   nonabelian rotation group with its graded bracket, a spectral-projector estimate at
   arbitrary surreal gap scale with a sharp two-scale example, support-controlled implicit
   lifting, and an exact square-root conditioning analysis.
3. **The full surreal class** — finite angles at arbitrary radius, the Ehrlich–Kaplan
   global phase normalization, the global radial exponential with its complete logarithm
   fibres and four-coordinate differential (rank-two critical spheres at radii in `pi*Oz`,
   including the infinite radius `omega`), the componentwise Berarducci–Mantova derivation
   with the no-oscillation theorem and the chain-rule corollary, and coefficientwise slice,
   Cauchy and Fueter analysis on explicitly named coefficient spaces.

### Section 2 is the ledger. Read it first.

Three exponentials and four derivative-like operators in this subject carry overlapping
names, and each satisfies a *different* law on a *different* domain. Section 2 fixes one
name and one symbol per object and tabulates, for each law, which object satisfies it:

| object | what it is | key law | key non-law |
|---|---|---|---|
| `Exp_m` | infinitesimal Hahn exponential on `m_H` | bijection onto `1 + m_H`; additive on commuting pairs | not additive otherwise (BCH); not a group isomorphism |
| `Exp_T` | finite-angle tube exponential on `{a+v : |v| finite}` | conjugation-equivariant, surjective, polar logarithms | domain excludes `omega*i`; not a Hahn sum of `q^n/n!`; not `exp(q_0)Exp_m(eps)` |
| `Exp_rad` | global radial exponential from the Ehrlich–Kaplan phase | on each slice a surjective homomorphism with kernel `2 pi Oz I` | **not** a homomorphism on noncommuting arguments; not an everywhere Hahn-summed series; its fibre over 1 is not a kernel |
| `d_H` | componentwise Berarducci–Mantova derivation | constants exactly `H_R`; surjective | no solution of `d_H y = cIy`; hence no commuting exponential chain rule |
| `delta_H`, `ad_w` | componentwise extension of any scalar derivation, plus inner part | every derivation is `delta_H + ad_w`, uniquely | `delta_H(q^n) = n q^{n-1} delta_H q` only under commutation |
| `d_sl` | coefficientwise slice (formal) derivative | preserves the common-support class | is not the full differential |
| `df_q` | fine (`No`-linear Fréchet) differential | computes `d Exp_rad` and its determinant | no Banach structure, no inverse function theorem |
| `D`, `Delta_4` | left Fueter operator and four-coordinate Laplacian | `D Delta_4 f = 0` for coherent slice-regular `f` | slice regularity does not give `D f = 0`: `D q = -2` |

Section 2.1 explains in full why the report's statement that `Exp_rad` is **not** an
additive-to-multiplicative homomorphism is consistent with the companion physics report's
correct claim that the **commutative** surcomplex Ehrlich–Kaplan exponential **is** a
homomorphism with kernel `2 pi i Oz`: the restriction of `Exp_rad` to any single slice is
exactly that commutative exponential, and the law holds there; it fails only across
*noncommuting* arguments, where no common slice exists. The exact witness is
`Exp_rad(omega i + pi j) = 1 + (pi^2/2 omega) i + O(omega^-2)` against
`Exp_rad(omega i) Exp_rad(pi j) = -1`. A merged sentence blurring the two would manufacture
a false contradiction across the collection.

## Which archives it came from, and what each contributed

The report is the **union** of two independently written manuscripts, both dated
21 September 2026. Neither is reproduced here; what each contributed is recorded below and
in the article's own provenance material.

* `10-noncommutative-hahn-obstructions.tex` (+ its README), delivered as a 34-page
  article with 27 numbered statements, from the archive `surquaternions_article(1).zip`;
* `11-radial-exponential-support-lifting.tex` (+ its README), delivered as a
  32-page article, from the archive `surquaternions_article.zip`.

Roughly two thirds of the mathematics is common to both — the algebra, norm, slice and
conjugacy-sphere material, the rotation description, the `M_2(F[i])` realization, the
one-sided fundamental theorem, the Hermitian spectral theorem with positive square roots
and the SVD, the Hahn normal form and residue algebra, the summability-versus-topology
section, infinitesimal exp/log, the Ehrlich–Kaplan radial exponential, admissible slice
series, and the computation/formalization discussion. Those are printed **once**.

**Only in 10 (`noncommutative-hahn-obstructions`).** The no-oscillation theorem
(`squat:thm:nooscillation`) and its chain-rule corollary (`squat:cor:nochain`), with the
`Exp_rad(omega i)` witness; the complete zero-class criterion with the two-coefficient
sphere remainder and conservation of class multiplicity (`2s + l <= d`); the
spectral-projector estimate at arbitrary surreal gap scale (`squat:thm:projector`) and the
two-scale example realizing its loss exactly (`squat:ex:spectral`); the intermediate tube
exponential `Exp_T` with its polar logarithms, `n`-th roots and two distinct Taylor failure
modes; the fine-topology counterexample of a locally-constant non-constant function; the
Cayley chart and the quaternionic Möbius maps with exact algebraic conformality; the
"no common domain" coefficient-pole counterexample; the Cauchy formula at arbitrary slice
direction with the classical slice kernel; the representation hierarchy; the five-layer
Lean proposal; the conventions-and-dependencies ledger and the appendix of worked exact
calculations.

**Only in 11 (`radial-exponential-support-lifting`).** The complete logarithm fibres of the
radial exponential (`squat:thm:logfibres`) and its exact four-coordinate differential and
determinant, with rank-two critical spheres at radii in `pi*Oz` including `omega`
(`squat:thm:exp-derivative`); the `omega i + pi j` example; the all-lengths Neumann lemma
proved via Higman's finite-word lemma; the lexicographic `Z x Z` warning that positive
valuation is a summability certificate and not cofinality; the adjoint series summable even
at infinite arguments; the graded rotation algebra `U_{>=gamma}/U_{>gamma} = (Im H, +)`;
support-controlled implicit lifting with `supp(h) ⊆ S* \ {0}` and `val(h) = val(P(x_0))`
(`squat:thm:lifting`); the exact Sylvester operator for squaring with its determinant,
inverse and singular values (`squat:prop:sylvester`); the quantified near-singular
square-root threshold (`squat:thm:conditioned`); the stereographic chart; the interspersed
no-root counterexample `q + i q i + 1 = 0`; the infinitesimal avoided-crossing example;
the classification of derivations with the angular-velocity identity; the six-layer Lean
proposal and the scalar-backend requirements.

**Kept as two proofs, marked as such.** Where the two manuscripts proved the same statement
by genuinely different routes, both routes are printed: surjectivity of
`Sp(1,F) -> SO(3,F)` (the `det(A-I) = -det(A-I)` fixed-vector argument, and the
odd-degree-characteristic-polynomial argument with its `-1`-eigenvalue refinement); the
sphere-remainder lemma (via the norm of the remainder, and via conjugating the remainder);
and the classification of derivations (via `u^2 = -N(u)`, and via the anticommutation
relations). Two different Cauchy formulas, two different formalizations of a common-domain
coefficient family, two rational charts on the unit group, two counterexamples to a root
theorem for interspersed coefficients and two proposed Lean layerings are likewise all kept.

## What is NOT claimed

Section 17 of the report, `Limitations and non-claims`, lists 29 numbered items (N1)–(N29);
every honest limitation from either source manuscript survives there verbatim in substance.
The headline ones:

* Not refereed, no priority claim, no claim to solve a named published open problem;
  literature inspection was targeted, not exhaustive. Much of the finite algebra is
  classical, the slice/Fueter framework has classical antecedents, and the scalar phase
  normalization is Ehrlich and Kaplan's, not introduced here.
* **No Lean implementation or formal verification** of this article. Both proposed layerings
  are *proposed modules only*; the report refuses to infer a theorem from a successful build
  reported elsewhere.
* The symbolic suites check **finite identities and truncated formal expansions only**. They
  do not construct the surreals, do not prove the Hahn support lemma, do not verify
  real-closed-field transfer or the Berarducci–Mantova construction, and establish no
  general analytic or spectral theorem.
* **No physics.** Neither source manuscript makes any claim about any empirical subject, and
  none is made here. "Spin" means the algebraic double cover; "rotation" means an element of
  `SO(3,F)` or `SO(4,F)`; the "avoided crossing" is 2x2 linear algebra; the
  "angular velocity" identity is a derivation identity, not a time evolution; "condition
  number" is an exact valuation statement, not a numerical heuristic.
* The `S^3(F) -> SO(3,F)` double cover is a statement about algebraic group points, **not** a
  covering-space theorem; neither rational chart claims `Sp(1,F)` is topologically a
  3-sphere; polar decomposition asserts no compactness.
* The root theorem covers **only** one-sided polynomials with a central indeterminate;
  interspersed-coefficient expressions can have no root at all.
* All spectral theory is finite-dimensional. The companion spectral-theory report's
  **determinantal singular-scale theorem and its positive Cauchy–Binet argument are
  determinant arguments and are not available over the quaternions**; nothing here reuses
  them. For matrices only `w(AB) >= w(A) + w(B)` holds.
* The cluster/block multiscale spectral calculus is a *direction*: one rank-one instance is
  proved, with no optimal block constant.
* `Exp_rad` depends on a **chosen** normalization, is not an everywhere Hahn-summed power
  series, is not a homomorphism on noncommuting arguments, and has no kernel and no
  preferred logarithm. `Exp_m` gives a bijection, not a group isomorphism.
* `squat:cor:nochain` forbids a commuting chain rule for `d_H` **only**; it says nothing
  about any exponential's multiplicative behaviour, does not conflict with the
  Liouville-closed results of Berarducci–Mantova, and does not contradict the commutative
  surcomplex homomorphism claim.
* A Hahn workspace need not be closed under Gonshor's exponential or under a chosen
  derivation; positive valuation is a summability certificate, not cofinality; fine
  differentiation gives no inverse function theorem; a zero fine differential does not imply
  constancy; coefficientwise integration is over *ordinary* contours and gives no uniqueness
  for arbitrary functions on `H_No`; admissible-series and coherent-function statements need
  a *common* support or a *common* ordinary domain.
* The `sigma > 2 kappa` square-root threshold is sufficient only, not optimal.
* Algorithms are effective *relative to* an exact scalar oracle; arbitrary surreal
  coefficients have no finite computable encoding.
* Octonions over `No` have no zero divisors but are only alternative, and the associativity-
  dependent proofs cannot be copied; this is an observation, not an octonionic theory.
* The first source archive's README lists a `SHA256SUMS.txt` that is **absent** from the
  delivered tree; no integrity claim rests on it.
* Each accompanying script **rewrites its own result file** beside itself by default, so an
  in-place re-run destroys the delivered record.

Six research directions are left explicitly open (Section 18).

## Code, data, and independent reproduction

`code/` and `data/` hold the two source suites and their recorded outputs, unchanged:

| file | contents |
|---|---|
| `code/10-noncommutative-hahn-obstructions-verify.py` | exact SymPy suite: Hamilton table, generic associativity/conjugation/norm, the `M_2(F[i])` representation, Rodrigues, the inner-derivation reconstruction, the `(X-i)*(X-j)` example, a Cayley unit, truncated exp/log/BCH, the two-scale Hermitian matrix through `t^9`, Fueter/Laplacian identities |
| `data/10-...-verification.json` | 69 of 69 check groups passed, 0 failed, 252 scalar identities |
| `data/10-...-build-and-validation.json` | 34 pages, 27 statements, 0 LaTeX errors/warnings/boxes, `formal_theorem_proof_verification: false` |
| `data/10-...-source-manifest.json` | repository snapshot; `repository_modified: false`, `repository_build_run: false` |
| `code/11-radial-exponential-support-lifting-verify.py` | exact SymPy suite: 31 named checks including generic associativity in twelve variables, the full square-map Jacobian, the parallel/perpendicular inverse of the square linearization, the interspersed no-root example, exp/log through degree six, BCH through degree four, the displaced square root through degree seven, the radial-exponential differential determinant, `D Delta_4 (q^n) = 0` for `n = 0..7` |
| `data/11-...-verification-results.json` | 31 of 31 passed, `all_passed: true` |
| `data/*-requirements.txt` | `sympy==1.14.0` (both) |

Both recorded runs used Python 3.13.5 with SymPy 1.14.0. Both suites were **re-run
independently on copies of the trees** under Python 3.14.4 with SymPy 1.14.0; both exited
zero, reporting 252 identities in 69 groups and 31 checks respectively. Running on copies
is not a formality — each script writes its result file beside itself, so an in-place re-run
overwrites the delivered evidence and a byte-identity check afterwards would compare two
equally modified copies and prove nothing. Nothing under `code/` or `data/` was
modified in producing this report.

To run them yourself, copy the tree first:

```sh
python -m pip install sympy==1.14.0
python code/10-noncommutative-hahn-obstructions-verify.py --output /tmp/rerun-10.json
python code/11-radial-exponential-support-lifting-verify.py   # overwrites its own JSON
```

## How to build

Standalone LaTeX: full preamble, bibliography embedded with `thebibliography`, no external
`.bib`, no graphics, no external fonts distributed. A standard TeX Live or MiKTeX
installation with `amsmath`/`amssymb`/`amsthm`/`mathtools`/`mathrsfs`, `geometry`,
`microtype`, `booktabs`, `longtable`, `array`, `enumitem`, `ragged2e`, `xcolor`,
`fancyhdr`, `hyperref`, `aliascnt` and `cleveref` suffices.

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex
```

Inspect `article.log` before running `latexmk -c article.tex`, which removes
auxiliary files. The recorded build is clean: **no errors, no LaTeX warnings, no
undefined references or citations, no multiply-defined labels, no duplicate PDF
destinations, and no overfull or underfull boxes**, giving a 61-page PDF. The front matter
uses roman page numbers with `pageanchor=false` across the title page, which is what keeps
the title page from producing a duplicate `page.1` destination; a single benign TeX note,
`Infinite glue shrinkage found in box being split`, remains where the notation longtable
breaks across a page.

## Directory contents

```
article.tex   the merged report (all labels prefixed squat:)
article.pdf   61 pages
README.md     this guide
code/         the two source verification suites, unchanged
data/         their recorded outputs and build metadata, unchanged
```

## Companion reports: inherited, not restated

Cited by title and repository path, at repository snapshot
`39f2be6667ade51bca2b45daa47e289d69c09764`:

* **`docs/surcomplex/spectral-theory/article.tex`** — *Surcomplex Spectral Theory: Singular
  Values, Infinitesimal Rank, and Multiscale Stability*. Supplies the complex/real-closed
  Hermitian and normal diagonalization, positive square roots, SVD, polar decomposition,
  variational principles, and the Hahn-workspace gap-sensitive projectors and subspace
  perturbation, with its Gram-squaring warning. The quaternionic case is kept separate here
  because the right-module structure, `A* = ` conjugate transpose and the reality of
  eigenvalues are genuinely different; its determinant arguments are explicitly not reused.
* **`docs/surcomplex/trigonometry/article.tex`** — *Trigonometry on the Surcomplex Plane:
  Canonical Phases, Arbitrary-Scale Geometry, and Infinitesimal Degeneration*. Supplies the
  scalar finite-angle theorem and the Ehrlich–Kaplan integer-part normalization with the
  omnific integers, presented there as one member of a character family and explicitly not
  claimed as new. Only the conjugation-equivariant *quaternionic* radial extension, its
  fibres, differential and critical points are printed here.
* **`docs/surcomplex/differential-equations/article.tex`** — *Differential Algebra and
  Differential Equations over the Surreal and Surcomplex Numbers*. Supplies "the missing
  oscillator", proved there three independent ways; `squat:thm:nooscillation` is stated as
  the componentwise quaternionic extension of it, not as an independent discovery. Its
  three-symbol phase convention — finite angle `theta`, infinitesimal residue `eta`,
  accumulated phase `B` — is reused unchanged, and Section 2's ledger is written as an
  extension of that table. No fourth sense of "phase" is introduced.
* **`docs/physics/surreal-scalars-and-spacetime/`** — cited only for its **commutative**
  surcomplex Ehrlich–Kaplan exponential with kernel `2 pi i Oz`; see Section 2.1 for why
  that claim and this report's non-homomorphism statement are both true.

## Status

An AI-assisted research draft with written proofs and finite symbolic checks, merged from
two such drafts. Not refereed and not machine-checked. Classical quaternion results,
surreal foundational inputs, and classical slice/Fueter theory are attributed; no
first-publication claim is made. The distinction between the fine topology of the full
surreal class and the intrinsic topology of a set-sized Hahn workspace is essential
throughout, all summations are Hahn sums unless an ordinary coefficient operation is named,
and the different exponentials and derivatives are deliberately never identified.
