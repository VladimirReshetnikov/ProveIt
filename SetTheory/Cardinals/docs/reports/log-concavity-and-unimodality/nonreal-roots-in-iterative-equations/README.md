# Nonreal Roots Survive in Polynomial Iterative Equations

**A cubic counterexample and a classification of circular spectra — Part II: the increasing spectral core on several circles — Part III: orientation-reversing spectra — Part IV: exact algebraic degree of polynomial coordinates**

This is a research report in four parts. Part I is the original report of
20 September 2026. Part II was added on 29 September 2026 in batch 41 of
ProveIt's incoming-report intake, from a later manuscript that classifies
what Part I left open for increasing maps: minimal iterative polynomials with
roots on several distinct circles. Part III was added on the same day in
batch 42, from a manuscript that treats the other orientation: decreasing
homeomorphisms of the real line, the boundary both earlier parts left open,
and Part II's first research question. Part IV was added on the same day in
batch 54, from a manuscript that answers Part III's Research question 35.7:
the exact algebraic degree of a polynomial-coordinate solution
`f = H ∘ (a·id) ∘ H⁻¹`. All four sources were prepared for Vladimir
Reshetnikov and are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection package *Nonreal Roots Survive in Polynomial Iterative Equations* (20 Sep 2026) | `nonreal_roots_research.zip` (as the collection manifest records it) | (none) | in ProveIt since `dc54c3cb3` | Part I: Sections 1–11 (pp. 7–23), Appendices A–B (pp. 96–97) |
| 02 | batch 41, manuscript 02 (*The Complete Increasing Spectral Core: Arbitrary-radius classification, optimal order reduction, and fixed-point spectra for polynomial iterative equations*, 28 Sep 2026, 20-page Letter PDF as delivered) | `ProveIt_Increasing_Spectral_Core.zip` (inner `Increasing_Spectral_Core/`, main file `article.tex`) | blob `ae6ea0aa` of Part I's `article.tex` | `eaf787d50` (prefix `02-spectral-core-`) | Part II: Sections 12–24 (pp. 24–43) |
| 03 | batch 42, manuscript 02 (*The Decreasing Spectral Core: Complete minimal spectra, finite-smoothness rigidity, and global polynomial conjugacy*, 29 Sep 2026, 27-page Letter PDF as delivered) | `ProveIt_Orientation_Reversing_Spectra.zip` (inner `ProveIt_Orientation_Reversing_Spectra/`, main file `article.tex`) | commit `afb2d1227` | `3609d0473` (prefix `03-decreasing-core-`) | Part III: Sections 25–37 (pp. 44–70) |
| 04 | batch 54, manuscript 01 (*Two Observations Determine the Coordinate: Exact algebraic degree, torsion exceptions, and nonradical solutions of order-two iterative equations*, 29 Sep 2026, 25-page Letter PDF as delivered) | `ProveIt_Exact_Algebraic_Degree.zip` (inner `ProveIt_Exact_Algebraic_Degree/`, main file `article.tex`) | commit `11e1e9001` (blob `b52eba81` of this report's `article.tex`, Parts I–III); Part III's source read from Vladimir's library as `article(20260929-151305).tex` (its `PROVENANCE.md`), i.e. the batch-42 arrival | `4d922d5b2` (prefix `04-exact-degree-`) | Part IV: Sections 38–50 (pp. 71–95) |

The references (p. 98) are shared; the title page and abstract are p. 1 and
the contents pp. 2–6.

**Pins.** Manuscript 02 of batch 41 is pinned by the Git blob
`ae6ea0aa0566316ba9ed06b1750c6e73275059da` of Part I's `article.tex`, which
its author retrieved through the GitHub content API on 28 September 2026, not
by a commit. That blob is the one committed in `dc54c3cb3` and was unchanged
at its placement commit, so every statement manuscript 02 makes about Part I
refers to the text printed here. The archive arrived in `9754e8360`; its
manuscript, PDF, delivery README and checksum ledger (`MANIFEST.sha256`,
11/11 verified at placement) are not shipped and survive in the arrival
commit.

Manuscript 02 of batch 42 is pinned to commit
`afb2d1227d8bc5df3beffc1463e958db3544960b`, an ancestor of its placement
commit. At that commit this report held Part I only, with the same blob
`ae6ea0aa`; Part II had not yet been placed. The manuscript read Part II's
source manuscript from Vladimir's file library (as
`article(20260929-042518).tex`) and says it does not assert that file belongs
to the pinned commit; Part II prints that manuscript. The archive arrived in
`8315d24e3` and was placed in `3609d0473`; its manuscript, PDF, delivery
README and checksum ledger (`CHECKSUMS.sha256`, 8/8 verified at placement
and again in the write phase) are not shipped and survive in the arrival
commit.

Manuscript 01 of batch 54 is pinned to commit
`11e1e900114e7c0cfdcd19fe346ddb4f2852dbc5` (the fourth arrival commit of
batch 52), an ancestor of its placement commit. At that commit this report
already held Parts I–III, as the blob
`b52eba816e4c6a108d740e4e4e0edd5b1f8631ec` of `article.tex`, which is
unchanged up to the placement commit; so every statement the manuscript makes
about "the repository" or "the source report" refers to the text of Parts
I–III printed here. It also read Part III's source manuscript from Vladimir's
file library (as `article(20260929-151305).tex`); the question it answers,
its "Section 11.7", is printed here as Section 35.7, and its text was checked
in the write phase against the batch-42 arrival `8315d24e3`. The archive
arrived in `392fff082` and was placed in `4d922d5b2`; its manuscript, PDF,
delivery README and checksum ledger (`CHECKSUMS.sha256`, 9/9 verified at
placement) are not shipped and survive in the arrival commit.

Each added part prints every result, proof, example, remark, limitation and
question of its manuscript. What a manuscript reproves from an earlier part is
printed once, in the earlier part, and credited at each use (Part II's
Section 12.1, Part III's Section 25.1 and Part IV's Section 38.1 list these
and every other point where the merge had to choose; Part IV reproves nothing
from Parts I–III).

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. The finite
computations check stated finite ranges and implementations; they are not a
proof of the universal statements. No part makes a priority claim.

## Results

For `P(z) = Σ a_j z^j`, `P[f]` means `Σ a_j f^{∘j}` (composition, not
pointwise powers); `μ_f` is the monic least-degree annihilator.

**Part I** (unchanged apart from three added subtitle lines, three
title-page paragraphs on Parts II–IV, set in a smaller size since batch 54
so that the title page stays one page, and dated pointers) answers Problem 6.1 of Draga
and Morawiec (*Aequationes Math.* 90 (2016), 935–950; arXiv:1503.00570v2,
p. 13) negatively: an odd increasing bi-Lipschitz homeomorphism `F` with
`F^{∘3}(x) = 8x`, `F(1) = 3` and `μ_F = z^3 − 8` (Theorem 2.1, Hankel
determinant −56), and a real-analytic map with `μ_f = (z−1)^2(z^2+1)`
(Theorem 3.1). It classifies the minimal polynomials of increasing
homeomorphisms with all roots on one circle `|z| = r` (Theorem 6.1): for
`r ≠ 1` the root `r` has odd multiplicity at least every other; at `r = 1`
either `μ = z − 1` or `1` has even multiplicity exceeding every other. It
also gives quantitative square-free realizations (Proposition 7.1), circular
rigidity criteria (Corollaries 8.1, 8.2) and fixed-point regularity results
(Theorems 9.1, 9.2 and a `C^1` counterexample).

**Part II** (batch-41 manuscript 02) works with the *difference spectrum*
`𝒟μ`, `μ` with one copy of `z − 1` removed. It proves:

1. **Classification with arbitrary root moduli** (Theorem 12.2; manuscript
   Theorem 1.2). A nonconstant monic real `μ` with `μ(0) ≠ 0` is `μ_f` for an
   increasing homeomorphism of `R` iff `μ = z − 1` or `𝒟μ` is
   *positive-admissible*: on each extreme modulus circle the positive real
   root is present with maximal multiplicity on that circle, and it is odd if
   there is only one circle; interior circles are unrestricted. Every
   permitted spectrum is realized by a globally bi-Lipschitz map, real
   analytic except possibly at one fixed point (everywhere analytic and
   fixed-point-free when the extreme moduli of `𝒟μ` bracket 1). Example:
   `(z−2)^2(z−4)^2` is realizable, `(z−2)^2` and `(z−1)(z−2)^2` are not.
2. **The increasing spectral core** `ℛ(P) = (z−1)^{δ(P)} 𝒦(𝒟P)`
   (Definition 16.1, Theorem 16.3; manuscript Theorem 5.3): an explicit
   root-by-root divisor of `P` such that every continuous increasing solution
   of `P[f] = 0` satisfies `Q[f] = 0` iff `ℛ(P) | Q`, and one bi-Lipschitz map
   has minimal polynomial exactly `ℛ(P)`. Increasing solutions exist iff `P`
   has a positive real root. Worked example: degree 32 → 23 (Section 19.4).
3. **Rigidity** (Theorem 17.1; manuscript Theorem 6.1): all increasing
   solutions are affine iff `ℛ(P) = z − r` (`r > 0`) or `(z−1)^2`, and
   homogeneous linear iff `ℛ(P) = z − r`.
4. **Fixed points**: the fixed set is empty or a closed interval
   (Proposition 18.2); a fixed-point-free realization exists iff
   `r_− ≤ 1 ≤ r_+` for the extreme moduli of `𝒟μ` (Theorem 18.3; manuscript
   7.3); an exact criterion for realizations with a fixed point
   (Theorem 18.4; manuscript 7.4).
5. **Examples**: a rational polygonal map with `μ = (z−2)^2(z−4)^2` (Hankel
   determinant 16384/9), an everywhere analytic map with
   `μ = (z−½)(z−2)(z^2+1)` (Hankel 225/256), and, for every `m ≥ 1`, an
   analytic fixed-point-free map with `μ = (z−½)(z−2)(z^2+1)^m` and
   `1/6 ≤ f' ≤ 6` (Theorem 19.1; manuscript 8.1).
6. Ten research questions and a staged Lean plan (Section 21; none started).
   Q1 (decreasing spectra) is now answered by Part III for maps of `R` with
   `P(0) ≠ 0`, and Q2 gains a pointer to Part III's decreasing smoothness
   theorem; both carry dated notes.

Added in the batch-41 merge (not stated by the manuscript): Remark 15.3 shows
that on one circle Theorem 12.2 is Part I's Theorem 6.1, and Remark 17.2 that
Theorem 17.1 gives Part I's Corollaries 8.1 and 8.2. As a finite check, the
manuscript's `realizable()` was compared in that write phase with the
conditions of Theorem 6.1 on **638 single-circle spectra** (radii 2 and 1;
roots `±r`, the pair `±ri` and the pair `r(3±4i)/5`; positive-root
multiplicity 0–4, the other three 0–3; empty spectrum excluded; 2 × 319):
**0 disagreements**. That comparison script is not shipped; the grid
specifies it.

**Part III** (batch-42 manuscript 02), for continuous maps of `R` and
`P(0) ≠ 0`. A polynomial `R` without unit roots is *negative-admissible* if on
its smallest and largest modulus circles the negative real root has maximal
multiplicity, odd when there is only one circle. It proves:

1. **Two-cycle geometry** (Theorem 27.1, Corollary 27.2): a decreasing solution
   has a unique fixed point `c`; unless it is an involution, `Fix(f∘f)` is a
   compact interval `[α, β]` and every exterior orbit tends to the endpoint
   two-cycle in one common time direction. Hence the nonunit roots of `μ_f`
   all lie inside or all outside the unit circle, and `±1` are at most simple
   roots. On a bounded interval, a decreasing solution is an involution
   (Corollary 27.4).
2. **Classification of decreasing minimal spectra** (Theorem 25.1): exactly
   `z + 1`, `z^2 − 1`, and `(z−1)^{ε+}(z+1)^{ε−} R` with `R` nonconstant,
   negative-admissible and on one side of the unit circle; each realized by a
   globally bi-Lipschitz map analytic off at most two points. Decreasing
   solutions exist iff `P` has a negative real root (Corollary 29.2).
3. **The decreasing spectral core** `𝒞↓(P) = U R_< R_>` (Theorem 30.1): a
   root-by-root universal annihilator of all decreasing solutions, with at
   most two witnesses and an exact criterion for two (Corollary 30.3; this
   includes the disjunction of Draga's Theorem 3 and Remark 4, credited), and
   an exact affine and homogeneous-linear rigidity test (Theorem 30.4).
4. **Finite-smoothness rigidity** (Proposition 31.1, Theorem 31.3): a `C^1`
   non-involutive solution has a hyperbolic fixed point; above an explicit
   differentiability order `N > Θ(P)` every non-involutive solution is
   `f(c + H(t)) = c + H(at)` with `a < 0`, `a ≠ −1`, `H` a polynomial, hence
   real analytic, algebraic and bi-Lipschitz, with squarefree real-rooted
   spectrum `(z−1)^{[c≠0]} Π_{k∈K}(z − a^k)`. Nonanalytic smooth involutions
   are the exact exception (Corollary 31.4); rational solutions are affine
   (Corollary 31.6). The threshold is sufficient, not claimed optimal. The
   algebraic degree of such `f` over `R(x)` is exactly `deg H` (Part IV,
   Corollary 40.3; dated note after Corollary 31.6).
5. **Smooth spectra and the smooth core** (Theorems 32.1, 32.2): the exact
   `C^∞`/analytic spectra and the smooth core `𝒞∞(P)`; the number of smooth
   witnesses is unbounded, while one `C^1` witness attains the continuous core
   (Theorem 32.4).
6. **Examples** (Section 33): `(z+2)(z+½)` (Draga's example, credited), a
   plateau map with `μ = (z+1)(z+r)`, an analytic-off-zero map with
   `μ = z^3 + 8` (Hankel −27/625), `(z+2)(z^2+9)^m(z+4)` and
   `(z+2)^2(z+4)^2`, an analytic nonlinear map with `μ = (z+2)(z−4)(z+8)`
   (Hankel 46656), and a sharp `C^1`/`C^2` example.
7. Ten research questions and a formalization route (Sections 34–35; none
   started); §35.7 (exact algebraic degree) is answered by Part IV (dated
   note there). Of its family question Part IV answers only the case of one
   fixed coordinate; two unrelated coordinates stay open (Section 47.7).

Added in the batch-42 merge (not stated by the manuscript): Remark 30.2
expresses the decreasing core through Part II's positive-recurrence core,
`𝒞↓(P) = (z−1)^{ε+}(z+1)^{ε−} 𝒦(P_<^#)^# 𝒦(P_>^#)^#` whenever `P` has a
negative root (`A^#(z) = (−1)^{deg A} A(−z)`). As a finite check, the shipped
verifier's closed core was compared in the write phase with that formula
evaluated by Part II's `positive_core` on every profile of Part III's four
continuous atlases that has a negative real root: **2,552 of 2,693 profiles,
0 disagreements**. That comparison script is not shipped; the description
specifies it. Remark 30.5 combines Part II's Theorem 17.1 with Part III's
Theorem 30.4 into an answer to Petrov's linearity question for every `P` with
`P(0) ≠ 0`; the combination is immediate and not claimed as a result of
either manuscript. A sentence after Corollary 29.2, also marked as added,
notes that `P[f] = 0` has a continuous solution iff `P` has a real root.

**Part IV** (batch-54 manuscript 01), for a nonconstant `H ∈ C[t]`, a
multiplier `a ∈ C^×`, `f_a = H ∘ (a·id) ∘ H⁻¹` and the field
`K_{H,a} = C(H(t), H(at))`; `adeg` is the algebraic degree over `R(x)`
(equal to that over `C(x)`), not the iterative order `deg μ_f`. It proves:

1. **Common-field theorem** (Theorem 39.3): `K_{H,a} = C(W(t))`, where `W`
   is the unique monic, zero-constant right compositional factor of `H` of
   maximal degree with `W(at) = a^{deg W} W(t)`; so `adeg f_a = deg H / deg W`.
   The tools are polynomial Lüroth theory and uniqueness of a normalized
   right factor of fixed degree (Lemmas 39.1, 39.2; classical, credited to
   Zieve–Müller).
2. **Infinite-order multipliers** (Theorem 40.2, Corollary 40.3): if `a` is
   not a root of unity, `K_{H,a} = C(t^g)` with `g` the gcd of the positive
   exponents of `H`, so `adeg = deg H / g`. For every coordinate of Part
   III's Theorem 31.3 the degree is exactly `deg H`: compositional structure
   of `H` causes no drop (example: `H = U∘U`, `U = t + t³`, `a = −2` gives
   degree 9). When `g = 1`, any two distinct orbit observations recover `t` rationally,
   and all nonzero iterates have the same degree (Corollary 40.6).
3. **Torsion multipliers** (Theorem 41.1): `W = t^r R(t^q)` with
   `r ≡ deg W (mod q)`; for involutions (`a = −1`) the degree is `deg H`
   divided by the largest degree of an odd right factor (Corollary 41.2),
   and for odd coordinate degree `n` the attainable degrees are exactly the
   divisors of `n`, with rational realizations (Theorem 41.4).
4. **Curves and algorithms**: the graph equation `F_{H,a}` has degree
   `adeg` in each variable and genus 0, and
   `Res_t(H(t)−X, H(at)−Y) = (−1)^n h_n^n F_{H,a}^{deg W}` (Theorem 42.1); a
   terminating exact right-factor algorithm computes the degree for every
   multiplier (Proposition 42.2); an explicit rational recovery for
   `H = t + t² + t³`, `a = 2` (Example 42.3).
5. **Monodromy** (Theorem 43.1, Lemma 43.3): the normal closure of the graph
   extension is that of `C(s)/C(A(s))` for `H = A ∘ W`; Morse polynomials
   have monodromy `S_r` (classical, credited to Kreso–Tichy).
6. **Nonradical solutions**: for odd `n ≥ 3` and real `a ≠ 0, ±1`,
   `H_n = t + t^n` gives `μ_f = (z−a)(z−a^n)`, `adeg n`, the graph equation
   `(Y − a^n X)^n + (a − a^n)^{n−1}(Y − aX) = 0`, Galois group `S_n`, hence
   no radical expression over `C(x)` for `n ≥ 5` (Theorem 44.1), with exact
   distortion formulas (Proposition 44.3). For every odd `n ≥ 5` and every
   `η > 0` there is a rational `ε ≠ 0` such that `H = t + t^n + εt^{n−1}`
   gives a real-analytic involution with `μ = z² − 1`, `adeg n`, Galois
   group `S_n`, distortion `< 1 + η`, not expressible by radicals
   (Theorem 45.4); a terminating rational search finds `ε`, and
   `ε = 1/200, 1/400, 1/600, 1/800, 1/1000` pass for `n = 3, 5, 7, 9, 11`
   (distortion ≤ 10201/9801).
7. Ten research questions, including a staged Lean or Rocq plan
   (Section 47; none started).

Added in the batch-54 merge (not stated by the manuscript): the notation
table (Table 5), two dated notes in Part III (after Corollary 31.6 and after
§35.7), and bracketed merge notes (Section 38.1 lists them).

## Not claimed

- No classification for equations with zero constant coefficient
  (noninjective solutions), in either orientation; none for arbitrary
  proper-interval or one-sided domains, except that a decreasing solution on
  a bounded interval is an involution (Part III); none of all individual maps
  realizing an admissible spectrum, in either orientation (Part III does
  classify every individual non-involutive solution above its smoothness
  threshold). Petrov's unrestricted linearity question is answered only for
  `P(0) ≠ 0`.
- No optimality of Part III's finite-smoothness threshold, no classification
  of intermediate regularity classes, and no nonhomogeneous or
  higher-dimensional results.
- No global complex analyticity, and no differentiability at the fixed point
  in the half-line case of Theorem 12.2 (Remark 15.2); Part III's continuous
  realizations are analytic only off at most two points.
- No factorization of arbitrary polynomials by the shipped code: Part II's
  module accepts factored spectra with Gaussian-rational roots only, and Part
  III's verifier works on root profiles (radius, type, multiplicity).
- No claim that the finite grids (Part II: 1,354 spectra, 97,281 divisors;
  Part III: 2,693 profiles and 203,149 divisors, plus 1,024 smooth root sets
  and 59,049 divisors), recurrence windows or Hankel determinants certify the
  universal or analytic statements. Part III's profile predicate encodes the
  theorem's conditions; agreement with it does not prove them.
- No novelty for the conjugacy method (Part I), for the piecewise-linear
  non-affine map of Theorem 17.1 (Bogdanov's comment on Petrov's question),
  for the classical recurrence framework, for the two-branch disjunction and
  its quadratic example (Draga 2016, Theorem 3 and Remark 4), or for the
  orientation-reversed cubic (a counterpart of Part I's). No priority: every
  literature check was targeted (Part I on 20 September 2026, Parts II–III on
  28–29 September 2026; Part III read Yang–Zhang, Li–Zhang and Xia–Huo–Wang–Xia
  at abstract level only), not exhaustive; the research questions of
  Sections 21 and 35 are not claimed open throughout the literature.
- Part IV: no classification of all continuous solutions of an iterative
  equation, of all smooth involutions, or of all real algebraic
  diffeomorphisms; its domain is the polynomial-coordinate family, and that
  every sufficiently smooth non-involutive decreasing solution belongs to it
  is Part III's theorem, not reproved there. No closed formula for the degree
  at torsion multipliers (an exact algorithm and, for involutions, a complete
  classification); no bit-complexity or numerical-stability bound for that
  algorithm. No classification of field relations between two unrelated
  coordinates `H`, `G` (Section 47.7), and no rational-coordinate,
  positive-characteristic or multivariate analogue. The radical obstruction
  concerns algebraic functions over `C(x)`: no claim that values at
  particular inputs are nonradical (every normalized map takes the value 0
  at 0), and no classification of the rational inputs where the specialized
  Galois group drops. The fixed-involution examples rule out a degree bound
  in terms of iterative order and distortion only, not bounds using
  coefficient heights, a non-torsion multiplier, a coordinate-degree bound or
  a ramification configuration. Its 447 finite test cases (315 + 90 + 8 +
  18 + 7 + 1 + 1 + 2 + 5) check implementations and certify the listed
  examples only. No priority:
  its literature check (Zieve–Müller and Kreso–Tichy in full preprint,
  Draga–Morawiec for context) was not a historical survey.
- No referee report and no Lean or Rocq certification.

## Labels

Part I's 87 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `cor:`,
`tab:`, `fig:`, `app:`), Part II's 69 carry `nrr:sc:` ("nonreal roots,
spectral core"), and Part III added **84** with the prefix `nrr:dc:`
("nonreal roots, decreasing core"). Total: 240. No label was renamed or
removed, and every one of the 156 earlier labels keeps its number (compared
in the `.aux` files of the committed and the new build; their pages moved,
because the title page and contents grew). Of the manuscript's 85 labels, 72
are printed with the prefix and two shortened (`thm:main-preview` →
`nrr:dc:thm:main`, `thm:smooth-preview` → `nrr:dc:thm:smooth`); the eleven
whose content is printed once in Parts I–II are not (`eq:right`,
`lem:recurrence`, `eq:expansion`, `prop:positive-necessary`, `lem:envelope`,
`eq:envelope`, `eq:weight`, `thm:positive-realization`, `eq:ratio`,
`eq:mode`, `eq:primitive`). Ten labels are new: `sec:source`,
`sec:notation`, `tab:notation`, `sec:main`, `sec:imported`,
`sec:conclusion`, `cor:bounded`, `cor:deletion`, `rem:reflected-core`,
`rem:petrov` (each with the prefix). Part III starts at Section 25; its
numbered table is Table 4, its equations continue from (104), and its
manuscript appendix is printed as Section 37. Part I's appendices come last
and contain no numbered items.

Part IV added **82** labels with the prefix `nrr:ed:` ("nonreal roots,
exact degree"). Total: 322. Again no label was renamed or removed, and all
240 earlier labels keep their numbers (compared in the `.aux` files of the
committed and the new build). All 76 of the manuscript's labels are printed,
each with the prefix (three of them, `app:reproduce`, `eq:iterative` and
`sec:verification`, would otherwise collide with Part I). Six labels are
new: `sec:source`, `sec:notation`, `tab:notation`, `sec:conclusion`,
`q-coordinates` (Part IV's Section 47.7), and `q-degree`, which is placed
in Part III's Section 35.7 so that Part IV can cite that question (each with
the prefix). Part IV starts at Section 38; manuscript Section `k` is printed
as Section `k + 37`, with the same theorem numbers inside it (manuscript
Theorem 2.3 is Theorem 39.3); its notation table is Table 5, its equations
are (146)–(188), and its two appendices are printed as Sections 49–50.

## Notation

Part I's symbols keep their meanings; Tables 3 and 4 list Parts II's and III's
symbols with the tempting false readings. In particular:

- `𝒟A` removes **one** copy of `z − 1`, not the whole `(z−1)`-primary
  factor; it is not Part I's dilation `D_2`, `D_8` (Section 2.3), nor Part
  III's threshold `Θ(P)`.
- `ℛ(P)` is Part II's increasing core, not the real line; `𝒦(B)` the
  positive-recurrence core; `𝒞↓(P)` Part III's decreasing core and `𝒞∞(P)`
  its smooth decreasing core.
- `A` is a polynomial (a spectrum) in Part II, a polynomial *function* `A(t)`
  in Part I's constructions, and `A_S` a set of radii in Part III; `W`, `G`,
  `H`, `F`, `h`, `g` are local to their constructions (Part I's `F` is the
  cubic counterexample; Part II's positive coordinate `g` is Part III's `w`).
- `ε+`, `ε−` (Part III) are the exponents of `z − 1` and `z + 1`; `ε+` is
  Part II's `δ(P)`, and `ε−` is not.
- Renamed from batch-41 manuscript 02: `T` → `Λ`, `a < b` → `b_− < b_+`,
  `k` → `κ`, `G` → `Φ`. Renamed from batch-42 manuscript 02: `ε`, `δ` →
  `ε+`, `ε−`; the odd cap `h` → `κ` (Part II's name for the same cap); the
  modulus bound `κ` → `ω`; `r(P)`, `R(P)` → `r_−(P)`, `r_+(P)`;
  `D_P(a)`, `D(P)` → `Θ_P(a)`, `Θ(P)`; the composition operator `T` → `E_g`;
  `mult_A(λ)` → `m_A(λ)`. No normalization changed.
- Part IV (Table 5) renames nothing. Its `K_{H,a}` is a field, not Part
  III's exponent set `K`; its `r(H,a)` is the algebraic degree, not a
  radius, and `d(H,a)` the discarded common-fibre multiplicity, not the
  degree; `adeg f` is not `deg μ_f` (Theorem 44.1: `adeg n`, iterative
  order 2); its `H` and `a` are arbitrary unless stated, whereas Part III's
  are always normalized with `a < 0`, `a ≠ −1`; its `δ = a − a^n` is not
  Part II's `δ(P)`; its `ε` is a perturbation parameter, not Part III's
  `ε±`.

## Files

```
article.tex                     the report, standalone LaTeX with an internal bibliography
article.pdf                     the compiled report, 98 Letter pages (title and abstract p. 1, contents pp. 2–6,
                                Part I pp. 7–23, Part II pp. 24–43, Part III pp. 44–70, Part IV pp. 71–95,
                                Part I's appendices pp. 96–97, references p. 98)
README.md                       this guide
Makefile                        Part I: verify, illustrations, pdf and clean targets (run in place; see below)
STATUS.md                       Part I: claims, computations and limits as delivered (stale in two lines; see below)
manifest_entry.tex              Part I: the suggested catalogue entry delivered with it (describes Part I only)
requirements-optional.txt       Part I: matplotlib, needed only for `analytic_demo.py --plots`
02-spectral-core-STATUS.md      Part II: manuscript's status and claim boundaries (delivered as STATUS.md)
02-spectral-core-source_audit.md  Part II: manuscript's source record (delivered as notes/source_audit.md)
03-decreasing-core-STATUS.md    Part III: manuscript's status, validation and priority limits (delivered as STATUS.md)
04-exact-degree-PROVENANCE.md   Part IV: manuscript's provenance and claim audit (delivered as PROVENANCE.md)
code/verify.py                  Part I: exact rational checker (two independent cubic implementations)
code/analytic_demo.py           Part I: floating-point illustration and optional plot generator
code/02-spectral-core-spectral_core.py  Part II: exact root-level core and classification routines
                                (delivered as code/spectral_core.py)
code/02-spectral-core-verify.py Part II: finite grid, recurrence and Hankel checks (delivered as code/verify.py)
code/02-spectral-core-example.py  Part II: the order-32 → 23 example (delivered as code/example.py)
code/03-decreasing-core-verify.py  Part III: exact atlas, smooth-atlas and example checks (delivered as code/verify.py)
code/03-decreasing-core-Makefile   Part III: pdf, verify and clean targets (delivered as Makefile; see below)
code/04-exact-degree-verify.py  Part IV: exact SymPy right-factor algorithm and independent fibre-gcd checks
                                (delivered as code/verify.py)
code/04-exact-degree-Makefile   Part IV: all, verify and clean targets (delivered as Makefile; see below)
data/exact_certificates.json    Part I: matrices, coefficients and results of code/verify.py
data/numerical_illustration.json  Part I: explicitly noncertifying floating-point results
data/selection.json             Part I: the random area draw and all 80 candidate areas
data/02-spectral-core-exact_checks.json  Part II: recorded verifier output (delivered as results/exact_checks.json)
data/02-spectral-core-verification.txt   Part II: its short log (delivered as results/verification.txt)
data/02-spectral-core-example.txt        Part II: recorded output of the example (delivered as results/example.txt)
data/03-decreasing-core-verification.json  Part III: recorded verifier output (delivered as results/verification.json)
data/03-decreasing-core-verification.txt   Part III: the same bytes (delivered as results/verification.txt)
data/04-exact-degree-verification.json     Part IV: recorded verifier output (delivered as results/verification.json)
data/04-exact-degree-verification.txt      Part IV: its summary (delivered as results/verification.txt)
data/04-exact-degree-requirements.txt      Part IV: sympy==1.14.0 (delivered as requirements.txt)
figures/cubic_counterexample.pdf, figures/analytic_displacement.pdf   Part I: the two figures
notes/literature_audit.md       Part I: source identifiers, what was checked, search limits
notes/selection_and_exclusion.md  Part I: random-draw and manifest-exclusion record
```

The eight `02-spectral-core-` files were staged in `eaf787d50`, the five
`03-decreasing-core-` files in `3609d0473` and the six `04-exact-degree-`
files in `4d922d5b2`, each byte-identical to its delivery (re-verified in the
write phases against fresh extractions). The manuscripts' `article.tex`,
`article.pdf`, `README.md` and checksum ledgers (`MANIFEST.sha256`, and the
two `CHECKSUMS.sha256` of batches 42 and 54) are not shipped.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex article.tex` three times. Build in a scratch copy of
`article.tex` and `figures/`, so that no auxiliary files land here: Part I's
`make pdf` and Part III's `code/03-decreasing-core-Makefile` run LaTeX in
place, and so would the `all` and `clean` targets of Part IV's
`code/04-exact-degree-Makefile`. Needed packages: newtx, amsmath/amsthm/mathtools, geometry,
microtype, graphicx, booktabs, tabularx, enumitem, fancyhdr, xurl, hyperref,
listings, caption, needspace (Part IV). No bibliography processor is needed.
The shipped PDF was built with MiKTeX (pdfTeX) on 29 September 2026 with no
errors, no warnings, no undefined or multiply defined references, no
duplicate destinations and no overfull or underfull boxes (as was the
committed three-part text). The DejaVu Type 3 fonts in it come from Part I's
two Matplotlib figures; every other font is embedded Type 1.

## Rerun the checks

Python with the standard library suffices for Parts I–III (Part I and II:
3.9+; Part III: 3.10+); Part IV needs SymPy (tested with 1.14.0, pinned in
`data/04-exact-degree-requirements.txt`). Run Parts I, II and IV normally,
not with `-O`: their verifiers use assertions. Part III's verifier raises
explicit exceptions and also passes under `-O`.

**Part I.** `code/verify.py` writes `data/exact_certificates.json` by default
and `code/analytic_demo.py` rewrites `data/numerical_illustration.json` (and,
with `--plots`, the two figures) in place, so do not run them here. From this
directory:

```sh
W=/path/to/scratch
py code/verify.py --output "$W/exact_certificates.json"   # 4,026 rational points, 4,025 secant checks,
                                                          # 4 Hankel determinants (-56, 1, -512, degree 15)
mkdir -p "$W/01" && cp -r code data figures "$W/01/" && (cd "$W/01" && py code/analytic_demo.py)
```

`make verify` and `make illustrations` run the same scripts in place and
would overwrite the shipped records.

**Part II.** The shipped scripts cannot run under their shipped names:
`02-spectral-core-verify.py` and `02-spectral-core-example.py` do
`from spectral_core import …` and fail with `ModuleNotFoundError`, and the
verifier writes to `parents[1]/results/`, which would create a stray
`results/` directory here. Restore the delivered layout in a scratch copy
(Git Bash or another POSIX shell, from this directory):

```sh
W=/path/to/scratch
mkdir -p "$W/02/code"
for f in code/02-spectral-core-*.py; do cp "$f" "$W/02/code/${f#code/02-spectral-core-}"; done
cd "$W/02"
py code/verify.py                    # writes results/exact_checks.json, results/verification.txt
py code/example.py > example.txt     # the recorded data/02-spectral-core-example.txt
```

This was run on 29 September 2026 (Python 3.14.4, about 1 s): the verifier
passed (1,354 spectra, 97,281 divisors, recurrences on −80 ≤ n ≤ 80, 402
monotonicity assertions, Hankel determinants 16384/9 and 225/256, 32 → 23),
and both outputs and the example's output equal the shipped files apart from
Windows line endings. The article's Python snippet (Section 20.1) likewise
needs the delivered name `spectral_core` on the module path of such a copy.
The grid check in the verifier enumerates divisors independently of the core
formula, but uses the same `positive_admissible` routine as the module; the
638-spectrum comparison above checks that routine against Part I's
independently stated theorem.

**Part III.** Run in place, `code/03-decreasing-core-verify.py` would write
`parents[1]/results/verification.json`, a stray `results/` directory here. It
takes an optional output path, so either pass one or use a scratch copy:

```sh
W=/path/to/scratch
py code/03-decreasing-core-verify.py "$W/verification.json" > "$W/verification.txt"
# or, with the delivered layout:
mkdir -p "$W/03/code" && cp code/03-decreasing-core-verify.py "$W/03/code/verify.py"
(cd "$W/03" && py code/verify.py > verification.txt)   # writes results/verification.json
```

The delivered `results/verification.txt` (shipped as
`data/03-decreasing-core-verification.txt`) is the script's standard output,
which is the same JSON. This was run on 29 September 2026 (Python 3.14.4,
about 2 s, also under `-O`): all checks passed (four continuous atlases, 2,693
profiles and 203,149 divisors, of which 992 + 1,050 + 270 + 240 profiles
admit solutions and 576 + 0 + 0 + 144 need two witnesses; a smooth atlas of
1,024 root sets and 59,049 divisors with 36 admissible minimal profiles;
Hankel determinants −27/625 and 46656; 401 plateau points; an eight-slope
witness example), and the JSON and printed output equal the shipped files
apart from Windows line endings. `code/03-decreasing-core-Makefile` is the
delivered `Makefile`: its `verify` target runs `python3 code/verify.py`,
which from this directory is **Part I's** verifier (overwriting
`data/exact_certificates.json`), and its `pdf` and `clean` targets build or
clean `article.*` in place. Do not use it here.

**Part IV.** `code/04-exact-degree-verify.py` takes `--output-dir`
(default `results`, relative to the working directory) and always writes
`verification.json` and `verification.txt` there, with the platform's line
endings (CRLF on Windows). Run in place with the default, it would create a
stray `results/` directory here; in the delivered layout the default
overwrites the recorded outputs. Run it in a scratch copy with an explicit
output directory:

```sh
W=/path/to/scratch
mkdir -p "$W/04/code" && cp code/04-exact-degree-verify.py "$W/04/code/verify.py"
cd "$W/04" && uv run --no-project --with sympy==1.14.0 python code/verify.py --output-dir "$W/04/rerun"
```

This was run on 29 September 2026 (uv resolved Python 3.13.5; SymPy 1.14.0;
about 11 s): all checks passed (315 support/multiplier cases over 63
support polynomials, 90 seeded cases, 8 structured cases, 18 odd-divisor
realizations, 7 binomial-family degrees, the rational recovery and the
resultant multiplicity, 2 near-reflection resultant identities and 5
near-reflection certificates), and both outputs equal
`data/04-exact-degree-verification.json` and `.txt` byte for byte after
CRLF → LF. The outputs record the Python and SymPy versions, so a run under
another Python (for example `py`, 3.14.4) differs in those fields only.
`code/04-exact-degree-Makefile` is the delivered `Makefile`: its `verify`
target runs `python code/verify.py --output-dir results`, which from this
directory calls **Part I's** verifier; that verifier rejects `--output-dir`
with a usage error and writes nothing (checked on a copy). Its `all` and
`clean` targets build or clean `article.*` in place. Do not use it here.

## Discrepancies and delivery names

- **Stale delivered text.** Part I's `STATUS.md` lists, under "Not
  established here", "A classification of decreasing solutions" (line 58)
  and "A classification when roots have different moduli" (line 59). For
  homeomorphisms of `R` with `P(0) ≠ 0`, the first is now established in
  Part III and the second, for increasing maps, in Part II; line 60 ("A full
  answer to Petrov's general linearity question") is answered for
  `P(0) ≠ 0` by Remark 30.5. The file is kept byte-identical; the article's
  corresponding sentences (title page, Sections 1.2, 6, 8 and 11, Part II's
  opening note, Sections 17, 21 and 22, the Petrov bibliography entry) carry
  dated pointers. `manifest_entry.tex` and `notes/literature_audit.md` also
  describe Part I only, and `02-spectral-core-STATUS.md` describes Part II's
  scope, which excludes decreasing solutions.
- **Unshipped files named in delivered text.** The delivery README of Part I
  listed `checksums.sha256`, which is not shipped (and this README replaces
  that delivery README). Part I's Appendix B names the user-supplied
  `manifest(1).tex`, which was never redistributed (its SHA-256 is recorded).
  Part II's scripts name `results/` and `spectral_core`; its source audit says
  "No source paper is repackaged in this archive" about the delivered archive.
  Part III's `03-decreasing-core-STATUS.md` speaks of "the manuscript" and
  "the article" (the unshipped delivered manuscript, printed here as Part
  III); its verifier's docstring says it accompanies `article.tex` (the same
  manuscript), its usage message names `code/verify.py`, and its default
  output is `results/verification.json`; its Makefile names `article.tex` and
  `code/verify.py` in the delivered layout. Part IV's
  `04-exact-degree-PROVENANCE.md` describes "the article" and "the included
  PDF" of 25 pages (the unshipped delivered manuscript, printed here as Part
  IV) and the Part III source `article(20260929-151305).tex` from
  Vladimir's library (not in the repository; the batch-42 arrival
  `8315d24e3` carries the same question); its verifier's docstring says to
  run `python code/verify.py --output-dir results` from the package root;
  its Makefile names `article.tex`, `code/verify.py` and `results` in the
  delivered layout.
- **Stale delivered text (Part IV).** The manuscript placed its question in
  "Part III, Section 34"; it is Section 35.7, and the printed text carries a
  merge note. Its sentence that the exact-degree question is "fully
  answered" also carries a merge note: for torsion multipliers the answer is
  an exact algorithm plus the involution classification, not a closed
  formula.
- **Delivery layout in Part I's text.** Part I's Appendix B and `Makefile`
  run from "the archive's top-level directory" and build in place; use the
  scratch-copy commands above instead.
- **Page size.** All four parts are US Letter, as delivered.
- **Citations.** Batch-41 manuscript 02 cites arXiv:1503.00570 without a
  version and Petrov's MathOverflow question with I. Bogdanov's comments;
  Part II uses Part I's bibliography entries for the same works, and the
  Petrov entry gained a dated note about the comments. Part I's statement
  that the question "had no posted answer" concerns answers, not comments,
  and stands. Batch-42 manuscript 02 cites Draga's note by its preprint title
  (*A note on the polynomial-like iterative equations order*); Part I's entry
  gives both the published and the preprint titles and is used. Its entries
  for "the ProveIt report" (a GitHub tree URL at `afb2d1227`, kept in Section
  37) and for Part II's manuscript (a library file name) are replaced by
  references to Parts I and II. Its three new works (Yang–Zhang 2004,
  Li–Zhang 2013, Xia–Huo–Wang–Xia 2026) were added to the bibliography after
  their DOIs were checked against Crossref in the write phase. Batch-54
  manuscript 01 cites Draga–Morawiec by arXiv:1503.00570 without a version;
  Part I's entry is used. Its entry for "the ProveIt report" (a GitHub tree
  URL at `11e1e9001`, kept in Section 49) is replaced by references to Parts
  I–III. Its two further works, Zieve–Müller (arXiv:0807.3578) and
  Kreso–Tichy (arXiv:1601.07316), were added after their arXiv records
  (titles, authors, submission dates) were checked in the write phase.
- **Symbols.** Part III's renames are listed above and in Table 4; its
  shipped status note and verifier keep the manuscript's names. Part IV
  renames nothing (Table 5).

## Relation to neighbouring reports and to the formal project

No other report in the research-report collection treats polynomial
iterative equations, and none of the added manuscripts names a report other
than this one, so no reciprocal note was written. Part IV's research
question on arithmetic specialization and radical values (Section 47.5)
bears on the collection report
`SetTheory/Cardinals/docs/reports/galois-theory-and-radicals/specialization-safe-radical-solvers/`
and on the Lean project `Algebra/PolynomialFormulas/`; a merge note there
names them, and neither is used by Part IV. That project's
`Algebra/PolynomialFormulas/Lean/PolynomialFormulas/AbelRuffini.lean`
proves, for example, `LeanProofs.PolynomialFormulas.abelRuffiniQuintic_root_not_solvableByRad`
(a root of the fixed rational quintic `X^5 − 4X + 2` is not expressible by
radicals); that is a statement about constant-coefficient polynomials and
formalizes nothing in Part IV, whose obstruction concerns algebraic functions
over `C(x)`.

The report sits in the `log-concavity-and-unimodality` category of the
research-report collection of the `SetTheory/Cardinals` Lean project. That
placement confers no formal status: no Lean or Rocq declaration anywhere in
ProveIt formalizes any statement of Parts I–IV. Section 21 (Q10), Section
34.3 and Section 47.10 record the formalization plans the three added
manuscripts propose; none of them has been started.

## Sources and attribution

S. Draga and J. Morawiec, *Reducing the polynomial-like iterative equations
order and a generalized Zoltán Boros' problem*, Aequationes Mathematicae 90
(2016), 935–950, https://doi.org/10.1007/s00010-016-0420-4, arXiv:1503.00570
— Problem 6.1 (preprint p. 13).

S. Draga, *A note on the order of polynomial-like iterative equations*,
Commentationes Mathematicae 56 (2016), 243–249, arXiv:1604.01287v2 —
Theorem 3 and Remark 4 (the two-branch disjunction, credited in Part III).

F. Petrov, *Continuous linear recurrent relations*, MathOverflow question
232493 (1 March 2016), with comments by I. Bogdanov.

Part I also cites Draga–Morawiec, *Means of iterates* (arXiv:1801.05006v2),
and Thangroongvongthana–Laohakosol–Mavecha, *Current Applied Science and
Technology* 21(3) (2021), 495–523. Part III also cites D. Yang and W. Zhang,
*Aequationes Math.* 67 (2004), 80–105; L. Li and W. Zhang, *Sci. China Math.*
56 (2013), 1051–1058; and C. Xia, R. Huo, X. Wang and Z. Xia, *Aequationes
Math.* 100 (2026), article 44. Part IV also cites M. E. Zieve and
P. Müller, *On Ritt's polynomial decomposition theorems*, arXiv:0807.3578
(Lemma 2.2, Corollary 2.9, Remark 2.16), and D. Kreso and R. F. Tichy,
*Diophantine equations and the monodromy groups*, arXiv:1601.07316. No
third-party paper PDFs are included.
