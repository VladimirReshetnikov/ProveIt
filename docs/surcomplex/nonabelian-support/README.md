# Nonabelian Support Obstructions: A Matrix Cousin Criterion and the Surcomplex Riemann–Hilbert Problem

`article.tex` / `article.pdf` — one merged research article, 52 pages, 50 numbered
results, standalone LaTeX with an internal bibliography, no external `.bib`, no
graphics. Build with

```sh
latexmk -pdf -interaction=nonstopmode article.tex
```

The delivered build has no errors, no warnings, no overfull or underfull boxes,
no undefined references or citations, no multiply-defined labels and no
duplicate PDF destinations. Every `\label` carries the prefix `nab:`.

## What this report is

One coefficient category, studied from two sides. The objects are matrices
congruent to the identity modulo positive Hahn exponents, `I_r + Mat_r(J_Gamma)`,
over a **set-sized and possibly non-Archimedean** ordered value group `Gamma`,
with ordinary holomorphic coefficient functions on a **single fixed ordinary
complex domain**. When `Gamma` is an ordered subgroup of the surreals,
`t^gamma = omega^(-gamma)` gives the surcomplex reading.

* **Part I (sections 6–11)** solves the multiplicative gluing problem — a matrix
  Cousin problem on a puncture-and-disk cover of a connected open Riemann
  surface — and develops the resulting integral vector bundles and the Stein
  branch.
* **Part II (sections 13–18)** solves the inverse monodromy (Riemann–Hilbert)
  problem for near-identity representations of the fundamental group of a plane
  with a closed discrete puncture set.
* **Part III (sections 19–23)** collects effectivity, the verification record,
  the full list of what is not claimed, and the open questions.

### The one thing to read before generalizing anything

Both headline theorems read *"the criterion is that the union of the supports is
well ordered"*, and **they are not the same criterion**. Section 12 exists
solely to keep them apart, and section 1.2 states both in a box on page 2.

* **Criterion P** (Theorem 6.2, Part I): gluing is solvable iff the union over
  punctures of the supports of the **normalized polar factors**
  `Pol(G_a) - I_r` is well ordered, where each transition matrix is factored
  **independently and first** as `G_a = Pol(G_a) Reg(G_a)`. It is **false** with
  the raw transition support `union_a supp(G_a - I_r)` in place of it, in
  **both** directions.
* **Criterion M** (Theorem 14.2, Part II): a representation is realizable iff
  the union over punctures of the supports of `rho(ell_d) - I_r` is well
  ordered, for a compatible based-meridian basis — the **raw monodromy
  matrices**, with no factorization applied first. Here the raw support *is* the
  invariant, and it is basis- and basepoint-independent (Proposition 14.4).

The trap is printed where a reader would otherwise generalize. Section 8 gives a
rank-three family over `Gamma = Q` whose determinant is one, whose only raw
singular exponent is `{1}`, and whose abelianized cocycle **splits** — yet which
admits no splitting, because the polar factors are forced to carry the
descending set `{1 + 1/n}` (Theorem 8.2). Example 8.3 then **adds** a term that
introduces exactly that descending set among the raw poles and thereby
**removes** the obstruction. Proposition 8.4 shows that even the true matrix
logarithm is not a repair: its `(1,3)` coefficient is off by a factor of `1/2`
from the correct polar coefficient.

## Which archives it came from, and what each contributed

Two independently written manuscripts, both dated September 21, 2026, both
preserved unchanged under `sources/`, `code/` and `data/`.

### `surcomplex_nonabelian_support` → Part I (base)

`sources/08-polar-support-matrix-cousin.tex` (+ its README). It owns the
machinery the two parts share and contributes:

* the integral/positive/full common-domain Hahn sheaves `H_Gamma`, `I_Gamma`,
  `J_Gamma`, the reduction map, the positive matrix group, and the proof that
  these are sheaves on the *ordinary* base;
* the Neumann support calculus and the positive inversion/`exp`/`log` lemma
  (both members proved these independently; printed once);
* the fixed-disk Laurent splitting and the isolated-singular-parts input on the
  plane (self-contained, essential singularities allowed) and on open Riemann
  surfaces via Behnke–Stein and Cartan B;
* the normalized polar factorization `Pol`/`Reg` with right-gauge invariance
  (`Pol(GQ) = Pol(G)`; the left-hand analogue is false);
* **Criterion P** with its support certificate, the right-torsor description of
  all splittings, removal of arbitrarily supported regular data, coordinate
  independence, and absoluteness under ordered value-group extension;
* the rank-one **recovery** of the repository's scalar Cousin criterion;
* the closed Heisenberg factorization, the rank-three obstruction, its repair,
  and the logarithm diagnostic;
* the chain identity and the **depth hierarchy**: for every `r >= 3` a cocycle
  trivial modulo the last central subgroup `Z_r` but nonsplit in full positive
  rank `r`, and nonsplit after every ordered value-group extension;
* nontrivial determinant-one **integral vector bundles** with trivial ordinary
  reduction, trivial on every bounded plane domain, plus the explicit
  localization boundary;
* support-controlled **Stein splitting** and **deformation rigidity** (the
  latter with `End(V)` acyclicity, around a nontrivial ordinary bundle), and the
  cyclic-versus-noncyclic universal rigidity dichotomy with its
  determinant-one rank-two counterexample.

### `surcomplex_riemann_hilbert` → Part II

`sources/09-support-monodromy-realization.tex` (+ its README and
`BUILD_AND_PROVENANCE.json`). It contributes:

* strong summability and the finite-decomposition lemma inside a generated
  monoid; the free based-meridian lemma;
* the period map `P` into the full **product** `C^D` and a complex-linear
  section `sigma` (axiom of choice for infinite `D`);
* the fundamental-matrix theorem with a support certificate **uniform over all
  group elements** — which is where necessity comes from — and the triangular
  change-of-monodromy lemma;
* **Criterion M** as a three-way equivalence, including realizers that are
  coefficientwise logarithmic (at most simple poles in `D`, no other finite
  poles), and a unique `sigma`-normalized realizer;
* the intrinsic form of the condition, and its invariance under one fixed
  `GL_r(K)` conjugation and under value-group enlargement;
* framed gauge classification, entire extension of logarithmic comparison
  gauges, and a nonlogarithmic counterexample showing that extension is sharp;
* the positive **Frobenius form** at a puncture, in which no spectral resonance
  operator is inverted;
* the finite Fuchsian specialization and the `SL_r` (traceless) refinement;
* three calibrating examples: an `SL_2` representation with every finite
  subproblem realizable and no global realization; a `cot` connection showing
  point-finiteness across punctures is **not** necessary; and one showing
  admissible supports need not be locally finite below a bound;
* the explicit **mixed commutator correction** on `C \ {0,1}`, with the
  `Gamma = Q + Q*omega` specialization placing it at exponent `1 + omega`;
* finite exponent dependence, base change, and the proof that no **continuous**
  linear period right inverse exists for infinite `D`.

### How the merge was done

A merge here is a union, not a selection. Results every member proved are
printed once (the Neumann lemma; the positive inversion/`exp`/`log` lemma).
Results reached by genuinely different routes keep **both** routes, marked:
the ordinary Mittag–Leffler input appears twice (unbounded-order singular parts
in section 4.2; a linear period section in section 4.3, with the reason each
theorem needs its own at the end of section 4), and "enlarging the workspace
cannot repair the obstruction" is proved twice, for two different objects
(Corollary 7.3 and Proposition 14.5). The two local normal forms (Theorem 5.1
and Theorem 5.4) are two normalizations of two different objects and neither is
derived from the other. Section 2.3 is a name-comparison table; section 2.2
records the one place where the two members make **different standing
assumptions** and keeps both. Appendix C is the merge record.

## What is NOT claimed

Section 21 lists 22 numbered limitations, all inherited from the two sources and
none weakened. The load-bearing ones:

* Nothing is refereed or proof-assistant verified; both sources are
  self-described AI-assisted research drafts.
* **Nontriviality in Part I is proved only over the integral sheaf `I_Gamma`.**
  It is *not* claimed after all monomials are inverted (over `H_Gamma`): there
  positive monomials are units, no reduction homomorphism to `O` exists, and the
  framing argument cannot be repeated. Neither criterion is restated over a
  coefficient field admitting **negative-valuation** changes of frame.
* Part II works only with **positive** support and monodromy near the identity:
  no nontrivial exponent-zero monodromy, no arbitrary residues with resonances,
  no arbitrary algebraic groups.
* **Neither theorem is the unrestricted classical Cousin or Riemann–Hilbert
  theorem.** The base, universal cover and path category are *ordinary* complex
  by design — not provisional notation for a fine-topological construction.
* Criterion P is exact only on the puncture-and-disk (star) cover. For general
  covers only the *sufficient* Stein theorem is available, and its hypothesis is
  a condition on a **presentation**, not an invariant.
* Neither criterion is a decision algorithm for a black-box infinite family;
  Corollary 10.3 shows finite-puncture computation provably cannot detect the
  Part I examples. Finite cutoffs are justified only for finitely generated
  positive rational exponent monoids.
* No classification of isomorphism classes; only triviality is decided.
* The infinite-puncture period section uses the axiom of choice and is not
  continuous (proved impossible), not normed, not effective, not computable.
  For infinite `D` no growth condition at infinity is imposed.
* Part II assumes no sheaf property, uses no Hahn sheaf cohomology, and relies
  on no companion claim about Hahn Noetherianity or a Nullstellensatz.
* Open: monomial localization; arbitrary-cover normal forms; classification;
  deformations of a nontrivial ordinary **connection** (twisted period map, no
  right inverse supplied); higher-dimensional bases; formal verification. Also
  open, and explicitly *not* suggested to be true in its naive form: a common
  generalization of the two criteria.
* No physics, no empirical claim and no applied interpretation anywhere. The
  citation of Ebrahimi-Fard–Guo–Kreimer is to the *algebra* of recursive
  Birkhoff factorization only. "Positive" always means Hahn exponents — never
  Hermitian positivity — and the normalized polar factorization is **not** the
  Hilbert-space polar decomposition. Surcomplex "resonance" senses used
  elsewhere in this collection are not in force here (Remark 2.1).

## Relation to other reports in the collection

Inherited and cited, not restated:

* `docs/surcomplex/global-divisors/` — *Global Support Obstructions: Moving
  Divisors, Mittag–Leffler, and a Picard Dichotomy*. Its "Further precise
  directions" asks for exactly this work. Its exact Cousin criterion
  (**Theorem 13.1**, in terms of the singular support) is **cited as the rank-one
  case that Proposition 7.4 recovers**, not reproved; its Picard-group vanishing
  dichotomy is the rank-one shadow of Theorem 11.4 here.
* `docs/surcomplex/differential-equations/` — its theorem *"Monodromy valued in
  `GL_d(K_Gamma)`"* is the **forward** map; Theorem 14.2 here is the converse for
  near-identity representations. Its ordinary-paths wording is adopted verbatim
  rather than re-argued (section 2.5).
* The analysis, analytic-geometry and contours-and-Stokes packages are credited
  by Part II as antecedents, not as contributions claimed here.

Repository reviewed at commit
`39f2be6667ade51bca2b45daa47e289d69c09764`, inspected September 21, 2026.
Neither source manuscript audited every manuscript in the repository, and one
repository code-search response was marked incomplete; its empty result is not
evidence of absence.

## Code and data

`code/` and `data/` hold both delivered suites and their recorded outputs,
unchanged. Neither verifies a theorem; both audit finite identities and both
print their own scope disclaimer. Section 20 describes exactly what each checks.

```sh
python code/08-polar-support-matrix-cousin-verify.py   # exact symbolic, SymPy
python code/09-support-monodromy-realization-verify-examples.py  # + NumPy/SciPy
```

* Part I: 2,899 exact rational-arithmetic checks, no floating point in any
  checked identity. Recorded run Python 3.13.5 / SymPy 1.14.0; an independent
  rerun reproduced the same PASS lines and the identical count of 2,899 under
  Python 3.14.4 / SymPy 1.14.0, the version banner being the only differing
  line.
* Part II: eight exact algebraic checks plus four coefficient-ODE error checks;
  recorded maximum entrywise errors `1.17e-13` and `1.47e-13`, with assertions
  at a looser `2e-9`. No floating-point surrogate is substituted for the Hahn
  monomials `u`, `v`.

**Two operational cautions, verified directly rather than read from a README.**

1. The Part II script **writes its own evidence**: it emits
   `verification_results.json` beside itself via `Path(__file__).with_name`, so
   running it in place overwrites the delivered record. **Run it on a copy.** A
   byte-identity check performed after an in-place run compares two equally
   modified copies and proves nothing.
2. The Part II README as delivered lists `SHA256SUMS.txt`; that file is **not
   present** in the delivered directory and is not present here, so no checksum
   verification of the original archive is possible from what was shipped.

## Directory contents

```
article.tex   merged article, standalone LaTeX, all labels prefixed nab:
article.pdf   52 pages
README.md     this file
sources/      the two source manuscripts and their READMEs, unchanged
code/         both verification scripts and the Part I Makefile, unchanged
data/         recorded outputs, requirement pins, build metadata, unchanged
```
