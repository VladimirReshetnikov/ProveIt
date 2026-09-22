# Nonabelian Support Obstructions: A Matrix Cousin Criterion and the Surcomplex Riemann–Hilbert Problem

Merged research report from **three** independently written manuscripts: two
dated 21 September 2026 (Parts I and II) and one dated 22 September 2026
(Part III, "localization-resistant bundles"). AI-assisted research draft: not
refereed, not formalized in Lean.

```
article.tex   merged article, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 83 pages
README.md     this file
code/         08-polar-support-matrix-cousin-verify.py          (Part I source)
              08-polar-support-matrix-cousin-Makefile           (Part I source)
              09-support-monodromy-realization-verify-examples.py (Part II source)
              10-localization-bundles-verify.py                 (Part III source)
data/         08-polar-support-matrix-cousin-requirements.txt,
              08-polar-support-matrix-cousin-verification.txt   (Part I source)
              09-support-monodromy-realization-build-and-provenance.json,
              09-support-monodromy-realization-requirements-tested.txt,
              09-support-monodromy-realization-verification-results.json (Part II source)
              10-localization-bundles-PROVENANCE.json,
              10-localization-bundles-requirements.txt,
              10-localization-bundles-verification.json,
              10-localization-bundles-verification.txt,
              10-localization-bundles-build_qa.json             (Part III source)
```

Without `latexmk`, run `pdflatex -interaction=nonstopmode -halt-on-error
article.tex` three times to settle references and the contents.

The article has 98 numbered environments: 84 numbered results (24 theorems,
16 lemmas, 15 propositions, 19 corollaries, 10 examples; there were 50 before
Part III was added) plus 6 definitions and 8 remarks. The delivered build has
no errors, no LaTeX or package warnings, no overfull or underfull boxes, no
undefined references or citations, no multiply-defined labels and no duplicate
PDF destinations.

Every `\label` carries the prefix `nab:`. Material added with Part III carries
the sub-prefix `nab:loc:`. **No pre-existing label was renamed or removed**:
the article had 169 labels before Part III was added and has 257 after it (88
new, all `nab:loc:`), and all 169 original labels are still present.
`docs/FORMALIZATION.md` cites `nab:` labels by name with line numbers; the
names are unchanged, but every cited line number has moved (the preamble gained
15 macro lines, and Part III sits between Parts II and IV).

The September 22, 2026 review corrects the full-raw-support sufficiency claim
and distinguishes it from the failure of raw singular support in both
directions. It adds an explicit left-gauge counterexample, clarifies the
matrix exponential/logarithm domains and support-condition invariance, and
separates the Part I bundle question from the Part II framed classification.
That review covered Parts I and II before Part III was added. The merged
83-page PDF builds in three `pdflatex` passes without warnings or box errors;
Part III has not received this maintained mathematical review. Temporary-copy reruns passed all 2,899 Part I exact checks and
the eight exact plus four numerical Part II checks under Python 3.13.14,
SymPy 1.14.0, NumPy 2.3.5 and SciPy 1.17.0; the largest numerical error was
`1.472e-13`, below `2e-9`. Historical code and data remain unchanged.

## What this report is

One coefficient category, studied from two sides, and then pushed past its
integrality boundary. The objects of Parts I and II are matrices congruent to
the identity modulo positive Hahn exponents, `I_r + Mat_r(J_Gamma)`, over a
**set-sized and possibly non-Archimedean** ordered value group `Gamma`, with
ordinary holomorphic coefficient functions on a **single fixed ordinary
complex domain**. When `Gamma` is an ordered subgroup of the surreals,
`t^gamma = omega^(-gamma)` gives the surcomplex reading.

* **Part I (sections 6–12)** solves the multiplicative gluing problem — a matrix
  Cousin problem on a puncture-and-disk cover of a connected open Riemann
  surface — and develops the resulting integral vector bundles and the Stein
  branch. Section 12 keeps the two criteria apart.
* **Part II (sections 13–18)** solves the inverse monodromy (Riemann–Hilbert)
  problem for near-identity representations of the fundamental group of a plane
  with a closed discrete puncture set.
* **Part III (sections 19–27)**, new, leaves the integral category: it builds
  bundles that stay nontrivial after all Hahn monomials are inverted, and even
  over the coefficientwise meromorphic sheaf `Mer((t^Gamma))`, and classifies
  them.
* **Part IV (sections 28–32)** collects effectivity, the verification record,
  the full list of what is not claimed, the open questions and the conclusion.

### The one thing to read before generalizing anything

Both headline theorems of Parts I and II read *"the criterion is that the union
of the supports is well ordered"*, and **they are not the same criterion**.
Section 12 exists solely to keep them apart, and section 1.2 states both in a
box on page 2.

* **Criterion P** (Theorem 6.2, Part I): gluing is solvable iff the union over
  punctures of the supports of the **normalized polar factors**
  `Pol(G_a) - I_r` is well ordered, where each transition matrix is factored
  **independently and first** as `G_a = Pol(G_a) Reg(G_a)`. Well-ordering of
  the **full raw transition support** `union_a supp(G_a - I_r)` is sufficient
  but not necessary: every polar support lies in its generated positive monoid.
  Well-ordering of **raw singular-coefficient support** fails both directions.
* **Criterion M** (Theorem 14.2, Part II): a representation is realizable iff
  the union over punctures of the supports of `rho(ell_d) - I_r` is well
  ordered, for a compatible based-meridian basis — the **raw monodromy
  matrices**, with no factorization applied first. **Well-ordering of that
  union** is basis- and basepoint-independent (Proposition 14.4); the support
  set itself need not stay the same.

The trap is printed where a reader would otherwise generalize. Section 8 gives a
rank-three family over `Gamma = Q` whose determinant is one, whose only raw
singular exponent is `{1}`, and whose abelianized cocycle **splits** — yet which
admits no splitting, because the polar factors are forced to carry the
descending set `{1 + 1/n}` (Theorem 8.2). Example 8.3 then **adds** a term that
introduces exactly that descending set among the raw poles and thereby
**removes** the obstruction. Proposition 8.4 shows that even the true matrix
logarithm is not a repair: its `(1,3)` coefficient is off by a factor of `1/2`
from the correct polar coefficient.

### The second thing to read: what Part III does and does not answer

Part I proves its bundles nontrivial over the **integral** sheaf `I_Gamma`
only, and its open-question section asked whether the explicit hidden and deep
examples (Theorems 8.2, 9.2) survive **monomial localization**, i.e. over
`H_Gamma = O((t^Gamma))`. **That printed question is still open.** Part III
answers a broader question with a *different* family, and says so:

* The new bundles glue free modules on the star cover of the plane by the
  **finite** matrix exponentials `G_n = exp(t^(alpha_n) exp(1/(z-n)) N)`, `N`
  nilpotent, `alpha_1 > alpha_2 > ... > 0`: descending exponents in front of
  ordinary **essential** singularities, where Part I's examples use poles.
* Part I's pole-data examples, the diagonal counterexamples of Theorem 11.4,
  and the global-divisor report's explicit plane Picard classes all become
  **trivial over `Mer((t^Gamma))`** (Corollary 27.2, a merge observation that
  checks the hypothesis of Proposition 27.1 for each). This decides nothing
  about them over `H_Gamma`.

## Which archives it came from, and what each contributed

Three independently written manuscripts. Their code and recorded output are
preserved unchanged under `code/` and `data/`; the manuscripts themselves are
not shipped. The file prefixes `08-`, `09-`, `10-` are local to this
directory.

| | Archive | Repository pin | Contributes |
|---|---|---|---|
| 08 | `surcomplex_nonabelian_support` | `39f2be6` | Part I and the shared machinery |
| 09 | `surcomplex_riemann_hilbert` | `39f2be6` | Part II |
| 10 | `surreal_localization_bundles` | `0097304` | Part III, Theorem 28.4, the Part III check suite, items 23–28 of section 30, three questions of section 31 |

The third archive is named "surreal" but its objects are **surcomplex**
(complex-valued Hahn coefficients read in `No[i]`). At its pin `0097304` this
report and the global-divisor report already had exactly their present text
(checked with `git diff`), so its quotations of both are current.

### `surcomplex_nonabelian_support` → Part I (base)

It owns the machinery the parts share and contributes:

* the integral/positive/full common-domain Hahn sheaves `H_Gamma`, `I_Gamma`,
  `J_Gamma`, the reduction map, the positive matrix group, and the proof that
  these are sheaves on the *ordinary* base;
* the Neumann support calculus and the positive inversion/`exp`/`log` lemma
  (both of the first two members proved these independently; printed once);
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
  localization boundary (section 10.3);
* support-controlled **Stein splitting** and **deformation rigidity** (the
  latter with `End(V)` acyclicity, around a nontrivial ordinary bundle), and the
  cyclic-versus-noncyclic universal rigidity dichotomy with its
  determinant-one rank-two counterexample.

### `surcomplex_riemann_hilbert` → Part II

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

### `surreal_localization_bundles` → Part III

A 28-page manuscript, called "the localization manuscript" in the article.
Everything in sections 19–27 comes from it except the merge observations
listed below, and it also contributes Theorem 28.4 (section 28.5).

### How the merge was done

A merge here is a union, not a selection. Results more than one member proved
are printed once: the Neumann lemma and the positive inversion/`exp`/`log`
lemma (sources 08 and 09); the ordered-group lemma, Lemma 11.3 (sources 08 and
10, and a third copy is the global-divisor report's `global:lem:descending`);
the sheaf property (sources 08 and 10, extended to the meromorphic sheaf in
Lemma 20.2). Results reached by genuinely different routes keep **both**
routes, marked: the ordinary Mittag–Leffler input appears twice (section 4.2 and
section 4.3); "enlarging the workspace cannot repair the obstruction" is proved
for three different objects (Corollary 7.3, Proposition 14.5, Corollary 22.8);
bounded triviality is proved by explicit finite gauges (Theorem 22.3) and by the
Stein theorem (Corollary 10.3); the cyclic direction of Theorem 25.1 is printed
through Theorem 11.1, with source 10's `q`-adic version of the same recursion
described, not reprinted. The two local normal forms (Theorem 5.1 and Theorem
5.4) are two normalizations of two different objects. Section 2.3 is the
Part I/II name table, section 2.2 records where the members make **different
standing assumptions** (Part III follows Part I), and section 20.5 lists every
symbol renamed in the Part III material. Appendix C is the merge record.

**Renamed in the Part III material only** (never in Parts I–II): the
meromorphic sheaf `P_Gamma` → `M_Gamma` (Part I's `P` is its algebra of
negative Laurent parts and `P_{r,Gamma}` its polar group; `M_Gamma` is the
global-divisor report's name for the same recipe); the bundles
`E_alpha(N)`, `E_{alpha,r}` → `N_alpha(N)`, `N_{alpha,r}` (Part I's `E(G)` is
the polar support union and `E_G` its bundles); punctures `D`, disks `U_n` →
Part I's `A`, `D_n`, `W_n`; the diagonal `D_delta` → `Lambda_delta`; the
category `N_A` → `Nil_A`; `v` → Part I's valuation symbol. The gluing
convention of Part III (`s_n = G_n s_0`) inverts Part I's (`G_a = B_0 B_a^-1`);
section 22.1 states the translation once.

**Merge observations** (not stated by source 10, each marked in the text):

* Remark 22.2: over `I_Gamma`, nontriviality of the new bundles is already an
  instance of Criterion P (their normalized polar factor carries the
  descending set `{alpha_n}`). What Part I does not give is everything over
  `H_Gamma` and `Mer((t^Gamma))`, stable nontriviality, indecomposability and
  the classification.
* Corollary 27.2 and the paragraph after it (see below).
* Section 20.1: the meromorphic sheaf is **not** one of the four constructions
  in the collection index's ring table, but it is **not new to the
  collection**: the global-divisor report defines the same recipe over a
  compact base (`global:def:compactsheaf`, also named `M_Gamma`), and the
  analysis report's class `M(U)` (`d:def:clusterres`) is the same ring on a
  connected domain. Part III is its first use on the plane as a coefficient
  sheaf for vector bundles.
* Item 29 of section 30.

## What the report claims

Numbers refer to the built `article.pdf`.

**Part I.** Criterion P (Theorem 6.2); the hidden rank-three obstruction
(Theorem 8.2) with its repair (Example 8.3) and logarithm diagnostic
(Proposition 8.4); the depth hierarchy (Theorem 9.2); nontrivial integral
bundles (Corollary 10.2), trivial on every bounded domain (Corollary 10.3);
Stein splitting (Theorem 11.1), deformation rigidity (Theorem 11.2) and the
cyclic dichotomy (Theorem 11.4).

**Part II.** Criterion M (Theorem 14.2), its intrinsic form (Proposition 14.4)
and invariance (Proposition 14.5); the positive Frobenius form (Theorem 5.4);
framed gauge classification and its sharp extension statements (section 15);
the `SL_r` refinement (section 16); the calibrating examples (section 17); the
mixed commutator correction (section 18); no continuous period section
(Proposition 28.3).

**Part III.** Base: the ordinary plane; `Gamma` any set-sized ordered abelian
group (no rank, divisibility, Archimedean or cofinality assumption); sheaves
`I_Gamma ⊂ H_Gamma = O((t^Gamma)) ⊂ M_Gamma = Mer((t^Gamma))` with all
coefficients of a section on one common ordinary domain (Definition 20.1,
Lemmas 20.2–20.3). Profile `alpha_1 > alpha_2 > ... > 0`, `h_n = exp(1/(z-n))`,
`c_n = t^(alpha_n) h_n`.

1. **Zero-annihilator obstruction** (Theorem 21.2, Corollary 21.4): for
   `B ∈ {I, H, M}` and every nonzero global `f`, `b_n = b_0 + c_n f` has no
   solution, also after every ordered group enlargement.
2. **Sections and nontriviality** (Theorem 22.4, Corollaries 22.5–22.8):
   `H^0(C, N_{alpha,r}) = A_B e_1`, and `A_B ⊗ ker N` in general; for `r >= 2`
   not stably trivial over `I`, `H`, `M` or any sheaf between `H` and `M`; no
   meromorphic frame; survives group enlargement. Every restriction meeting
   finitely many punctures is `I`-trivial (Theorem 22.3).
3. **Morphisms** (Theorem 23.1, Corollaries 23.2–23.5, Theorem 23.3,
   Proposition 23.6): `Hom = A_B ⊗ {B : MB = BN}`, `End = A_B[T]/(T^r)`;
   indecomposable; a fully faithful realization of nilpotent representations;
   the flag is intrinsic.
4. **Classification** (Theorem 24.1, Corollaries 24.2–24.3, Examples 24.4–24.6):
   over `I`, isomorphic iff `alpha_n = beta_n` eventually; over `H` or `M`, iff
   `beta_n - alpha_n` is eventually one constant `delta ∈ Gamma`. Isomorphisms
   cover the identity of `C`.
5. **Dichotomy** (Theorem 25.1): `Gamma` is `0` or cyclic iff every `I`-bundle
   with trivial reduction is `I`-trivial, iff every such bundle becomes trivial
   over `H`, iff over `M`. Only the `M` side is new; the cyclic direction is
   Theorem 11.4.
6. **Continuum many classes** over `M` in every noncyclic group (Theorem 25.2,
   Examples 25.3–25.4); **tensor rule** `N_r ⊗ N_s = ⊕ N_{r+s-1-2j}` and
   self-duality (Theorem 26.1, Lemma 26.2, classical linear algebra).
7. **Poles versus essential singularities** (Proposition 27.1, Corollary 27.2,
   Proposition 27.3): transitions that extend meromorphically with their
   inverses give `M`-trivial bundles; hence Part I's hidden and deep examples,
   the diagonal examples of Theorem 11.4, the global-divisor report's line
   bundles `L(a)` (including every explicit class of its Picard dichotomy) and
   its root-cluster bundles all become trivial over `M`. Since those line
   bundles are nontrivial over `H` for noncyclic `Gamma ⊆ No`, extension of
   scalars from `H` to `M` kills nonzero plane Picard classes.
8. **Undecidability** (Theorem 28.4): for the rational binary profiles, neither
   isomorphism nor nonisomorphism is semidecidable, in all three categories.

## What is NOT claimed

Section 30 lists **29** numbered limitations (22 before Part III): items 1–11
from Part I's source, 12–21 from Part II's, 23–28 from Part III's, item 22 on
the two criteria, and item 29 added by the merge; Part III's generic
limitations are folded into items 1, 8, 9, 10, 11 and 21. None was weakened.
The load-bearing ones:

* Nothing is refereed or proof-assistant verified; all three sources are
  self-described AI-assisted research drafts. No Lean code is supplied.
* **Nontriviality of Part I's examples is proved only over `I_Gamma`.** It is
  *not* claimed over `H_Gamma`, where positive monomials are units and no
  reduction homomorphism to `O` exists. Part III does not change this: its
  localization-resistant bundles are a **different, essential-singularity
  family**, and the pole-only hidden and deep examples remain open over
  `H_Gamma` (section 31, "Monomial localization (open, re-scoped)"). Over
  `Mer((t^Gamma))` they are trivial.
* Corollary 27.2 concerns the displayed families only: it does **not** say that
  every class of `Pic(C, H_Gamma)` dies over `M_Gamma`, and nothing is claimed
  about the Picard group of `M_Gamma` or about rank-one `M_Gamma`-bundles.
* Part III is about a **specified** category: ordinary plane, set-sized
  `Gamma`, common ordinary coefficient domain, finite-dimensional complex
  nilpotents. `M_Gamma` is one specified inclusion, not every notion of
  Hahn-meromorphic function and not Müller–Strohmaier's category. **No theorem
  about arbitrary fine-topological bundles on the surcomplex class**; `exp(1/(z-n))`
  is an ordinary function.
* **The matrix exponentials are finite polynomials, not limits**; `(c_n)` is not
  a Hahn sum; bounded trivializations do not form an exhaustion-limit frame;
  the obstruction quotient is not identified with derived sheaf cohomology.
* Part III's classification is for its profile family and the image of the
  nilpotent-representation functor only, with fixed punctures and fixed `h_n`,
  over the identity of the base: no Krull–Schmidt theorem, no classification of
  all Hahn bundles, no nonabelian `H^1`, no extension groups, no connections,
  nothing about Berarducci–Mantova equations.
* **Semidecidability failure scope**: Theorem 28.4 is a reduction to the
  halting problem, not a new theorem about Turing machines; it concerns the
  promised computable class of rational binary profiles; finite or eventually
  periodic presentations are decidable by finite methods.
* In Proposition 27.3 sufficiency needs `h_n` to extend holomorphically to
  `C \ {n}`; no extension of locally specified functions is assumed.
* Criterion P is exact only on the puncture-and-disk (star) cover; for general
  covers only the *sufficient* Stein theorem is available, and its hypothesis
  is a condition on a **presentation**, not an invariant.
* Neither criterion is a decision algorithm for a black-box infinite family;
  Corollary 10.3 shows finite-puncture computation provably cannot detect the
  Part I examples. Finite cutoffs are justified only for finitely generated
  positive rational exponent monoids.
* Part I decides bundle triviality without classifying all isomorphism classes.
  Part II classifies framed positive gauge classes by admissible monodromy;
  Part III classifies one explicit family and nothing beyond it.
* **Neither Criterion P nor Criterion M is the unrestricted classical Cousin or
  Riemann–Hilbert theorem.** The base, universal cover and path category are
  *ordinary* complex by design.
* The infinite-puncture period section uses the axiom of choice and is not
  continuous (proved impossible). The continuum count of Part III uses
  cardinal arithmetic with choice. No norm estimate or effective procedure for
  the period section is supplied; no computability claim is made for a
  specified representation of its infinite input data.
* Part II assumes no sheaf property, uses no Hahn sheaf cohomology, and relies
  on no companion claim about Hahn Noetherianity or a Nullstellensatz.
* Credited, not new: the Neumann calculus; ordinary Laurent, Mittag–Leffler,
  Cartan B, Behnke–Stein, Oka–Grauert background; algebraic Birkhoff
  factorization; the Jordan tensor identity (Atiyah's elliptic-curve bundles
  are a precedent for its pattern, which is not evidence of novelty); the
  halting theorem; the scalar Picard dichotomy of the global-divisor report and
  Part I's cyclic rigidity (antecedents of Theorem 25.1).
* Novelty assessments are bounded by what each source inspected (source 10
  read this report's README and two line ranges of its article, and a
  truncated global-divisor README); they are not priority certificates.
* No physics, no empirical claim and no applied interpretation anywhere.
  "Positive" always means Hahn exponents. Surcomplex "resonance" senses used
  elsewhere in this collection are not in force here (Remark 2.1). "Picard"
  means the Picard group, never a Picard-type theorem.

## Relation to other reports in the collection

* `docs/surcomplex/global-divisors/` — its exact Cousin criterion (Theorem 13.1
  there) is **cited as the rank-one case that Proposition 7.4 recovers**, not
  reproved; its Picard-group vanishing dichotomy is the rank-one shadow of
  Theorem 11.4 and the rank-one antecedent of Theorem 25.1. Its explicit plane
  Picard classes become trivial over `M_Gamma` (Corollary 27.2), which does not
  contradict its dichotomy (that concerns `I` and `H` only). Its compact-base
  sheaf `M_Gamma` is the same recipe as Part III's.
* `docs/surcomplex/differential-equations/` — its theorem *"Monodromy valued in
  `GL_d(K_Gamma)`"* is the **forward** map; Theorem 14.2 here is the converse for
  near-identity representations.
* `docs/surcomplex/analysis/` — its class `M(U)` of Hahn series with meromorphic
  coefficients is Part III's `M_Gamma(U)`; its `t e^{1/Z}` is the same ordinary
  essential-singularity device as `h_n`.
* The analysis, analytic-geometry and contours-and-Stokes packages are credited
  by Part II as antecedents, not as contributions claimed here.

Parts I–II reviewed the repository at commit
`39f2be6667ade51bca2b45daa47e289d69c09764` (21 September 2026); Part III's
source at `0097304c7ae9d5de46d2ea342e2494f8fc126303` (22 September 2026). No
source audited every manuscript in the repository, and one repository
code-search response was marked incomplete; its empty result is not evidence
of absence.

The Frobenius theory used here is for the coordinate derivative. The
regular-singular systems of [differential-equations](../differential-equations/)
Part V are intrinsic, for the Euler derivation on the Hahn field, and are a
different theory.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Standalone LaTeX with an internal bibliography: no `.bib`, no graphics.

## Code and data

`code/` and `data/` hold all three delivered suites and their recorded outputs,
unchanged. No suite verifies a theorem; each audits finite identities and
prints its own scope disclaimer. Section 29 describes exactly what each checks.

```sh
check_dir=$(mktemp -d)
cp code/*-verify*.py "$check_dir/"
python "$check_dir/08-polar-support-matrix-cousin-verify.py"
python "$check_dir/09-support-monodromy-realization-verify-examples.py"
python "$check_dir/10-localization-bundles-verify.py" --max-rank 6 \
  --output "$check_dir/localization-verification.json"
```

* Part I: 2,899 exact rational-arithmetic checks. Recorded run Python 3.13.5 /
  SymPy 1.14.0; an independent rerun reproduced the same PASS lines and count
  under Python 3.14.4 / SymPy 1.14.0.
* Part II: eight exact algebraic checks plus four coefficient-ODE error checks;
  recorded maximum entrywise errors `1.17e-13` and `1.47e-13`, assertions at a
  looser `2e-9`.
* Part III: **12,355** exact checks (nilpotent exponentials, monomial
  conjugation, gauges, centralizers and intertwiner dimensions for ranks 1–6,
  Jordan tensor rank profiles, the rank-two gauge equation, 8,000 rational
  binary-profile inequalities, 4,000 lexicographic non-Archimedean samples).
  Recorded run Python 3.13.5 / SymPy 1.14.0 (pinned); an independent rerun
  under Python 3.14.4 / SymPy 1.14.0 reproduced the recorded JSON except for
  the Python version field. The two recorded files are byte-identical. It does
  **not** check the essential-singularity theorem, well-ordering, descent,
  classification, undecidability or novelty.

**Operational cautions, verified directly rather than read from a README.**

1. The Part II script **writes its own evidence**: it emits
   `verification_results.json` beside itself. In this maintained layout an
   in-place run writes under `code/`; the separately named historical record
   under `data/` is unchanged. In the original archive layout it could
   overwrite the record beside the script. **Run it on a copy**, as above.
2. The Part III script writes **only** to the path given with `--output`, so an
   in-place run does not overwrite `data/10-localization-bundles-verification.*`.
3. The Part II README as delivered lists `SHA256SUMS.txt`; that file was not
   delivered and is not here. The Part III archive did carry a SHA-256
   manifest: all nine entries verified at merge time and the six files placed
   here match it, but the manifest itself is not shipped.
4. `data/10-localization-bundles-build_qa.json` is layout QA of source 10's own
   28-page PDF (not shipped), not of this article and not theorem verification.
