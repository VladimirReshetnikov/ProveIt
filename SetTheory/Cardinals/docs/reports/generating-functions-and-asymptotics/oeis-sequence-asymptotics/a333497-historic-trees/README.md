# Historic Tree Asymptotics and a High-Order Obstruction

**Reduced 5- and 7-historic trees (OEIS A333497, A336009): factorial-pole
equivalents with logarithmically oscillating corrections to every fixed grade,
the failure of Burghart–Wagner's Conjecture 1 for every order `m ≥ 29`, and
(since batch 103) A333497 and A336009 are not P-recursive**

A research report in four Parts, built from four manuscripts. Part I (2 October
2026) is the original single-source report; Parts II–IV (added 5 October 2026,
batch 103) print three manuscripts of the session bundle, Reports 113, 115 and
117, each dated 2 October 2026. No manuscript names an author or a tool, and
every PDF metadata Author field is empty; none of sources 02–04 carries
"prepared for private review" wording.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 24 | `historic-tree-report.zip` (wrapper `historic-tree-release/`), arrival `096ee7b87`; main file `historic-trees.tex`, now `article.tex`, with its `\input` file `extensions.tex` | none | `34f1acd4b` | Part I, Sections 1–11 and Appendix A |
| 02 | batch 103, bundle Report 113 | `A333497_B_Tree_Histories_All_Orders_and_Inversion_Source.zip` (wrapper `report113/`), arrival `60f54ea06`; `report113.tex`, 788 lines, 13-page PDF | none | `9c995cefe` (prefix `02-order5-`) | Part II, Sections 12–20, in full |
| 03 | batch 103, bundle Report 115 | `A336009_B_Tree_Histories_Transseries_and_Non_D_Finiteness_Source.zip` (wrapper `report115/`), arrival `60f54ea06`; `report115.tex`, 1100 lines, 17-page PDF | none | `9c995cefe` (prefix `03-order7-`) | Part III, Sections 21–32, in full |
| 04 | batch 103, bundle Report 117 | `B_Tree_Order_59_Counterexample_to_the_Universal_Asymptotic_Conjecture_Source.zip` (wrapper `report117/`), arrival `60f54ea06`; `report117.tex`, 859 lines, 14-page PDF | none | `9c995cefe` (prefix `04-order59-`) | Part IV, Sections 33–44, in full (its Appendices A and B are Sections 43 and 44) |

**The archive names mislead.** "All_Orders" (source 02) does not mean all
B-tree orders: the manuscript treats only B-tree order five (`m = 2`, A333497),
and "all orders" means every fixed *coefficient* order of that one sequence.
"Transseries" (source 03) does not describe the content: the expansions are
convergent psi series (power series in complex powers of `t`), with no
logarithmic or exponential transmonomials, and the manuscript never uses the
word. Source 04's "order 59" is the B-tree order; it is Part I's ODE order 30.

**Status:** presumed AI-assisted (no source names an author or a tool),
unrefereed, not formalized: no Lean or Rocq declaration exists for any
statement of this report. Exact rational and integer certificates corroborate
the finite algebraic identities and spectral certificates; all fitted
constants, residual tables and the figure are exploratory and not interval
certified.

## The order dictionary

| Burghart–Wagner parameter | B-tree (historic-tree) order | ODE order (Part I) | derivative order (Part IV) | sequence |
|---|---|---|---|---|
| `m = 2` | 5 | `r = 3` | `d = 3` | A333497 (Parts I, II) |
| `m = 3` | 7 | `r = 4` | `d = 4` | A336009 (Parts I, III) |
| `m = 29` | 59 | `r = 30` | `d = 30` | no OEIS number asserted (Parts I, IV) |

## What it proves

`h_n` are the exponential coefficients of the solution of `H''' = H²`,
`H(0) = H'(0) = H''(0) = 1` (reduced 5-historic trees, OEIS A333497, by
recurrence: 1, 1, 1, 1, 2, 4, 8, 18, 48, 144, …). The order-`r` all-one family
`H_r^(r) = H_r²` has conjecture parameter `m = r − 1` and historic-tree order
`2m + 1`.

### Part I (source 01)

- **Theorem 1.1 (A333497).** `H` has a finite positive blowup point `ρ` with
  `180^(1/4) ≤ ρ ≤ 60^(1/3)`, the unique singularity on its circle of
  convergence, and a convergent local expansion
  `H = 60 t^(-3) 𝓕(C t^λ, C̄ t^λ̄)`, `t = ρ − z`, `λ = (13 + i√71)/2`,
  `C ≠ 0`. For every fixed grade `d`,
  `h_n / (30 (n+2)! ρ^(-n-3)) = Q_d(n) + O(n^(-13(d+1)/2))` with exact Gamma
  ratios in `Q_d`.
- **Corollary 1.2 (oscillation).** `R_n − 1 = 2|K| n^(-13/2) cos(arg K − ω log n)
  + O(n^(-15/2))`, `ω = √71/2`, `K ≠ 0`; so `R_n − 1` changes sign infinitely
  often and is not `O(n^(-7))`.
- **Theorem 7.1 (inverse).** An eventual shrinking two-ceiling window for
  `N(X) = min{n : h_n ≥ X}` at every fixed grade, with existence constants;
  a Lambert-W starting value and the first oscillatory displacement.
- **Theorem 8.1 (A336009, `G'''' = G²`).** `g_n = 140 (n+3)! ρ_4^(-n-4)
  (1 + O(n^(-11/2)))`, a convergent three-mode local expansion with the exact
  real-mode coefficient `D = −1/18052070400` (from the conserved energy
  `1/6`), a nonzero complex amplitude (backward Metzler argument), all fixed
  grades and inverses.
- **Theorem 9.1 (obstruction).** For every ODE order `r ≥ 30` no `ρ > 0`
  gives `h_n^(r) ~ ((2r−1)!/((r−1)!)²) (n+r−1)! ρ^(-n-r)`: Burghart and
  Wagner's Conjecture 1 (Theor. Comput. Sci. 1070 (2026), Section 4) is false
  for every `m ≥ 29`. Method: an unstable conjugate pair (exact rational
  bridge for `30 ≤ r ≤ 37`, rational inequalities for `r ≥ 38`), a closed
  sign-variation cone containing the actual orbit, strict sign-regularity of
  order three, and a generalized stable manifold.
- Lemma 8.2: finite positive blowup for every order `r ≥ 2`.

### Parts II–IV (sources 02–04): what is new

- **Theorem 30.1 (source 03): the exponential generating functions of A333497
  and A336009 are not D-finite over `C(z)`, and A333497 and A336009 are not
  P-recursive over `C[n]`.** New to the repository; printed in full with its
  proof (Section 30). Proof: windings about the dominant singularity produce
  germs that are linearly independent in every finite collection (grouped
  uniqueness of complex exponents, infinitely many distinct characters
  `e^{2πikα}` on the pure complex axis), which contradicts the finite-dimensional
  solution space of a linear ODE at an ordinary point; a polynomial recurrence
  gives such an ODE. Its order-five input is Part I's Theorem 1.1 (expansion,
  universal recurrence, `C ≠ 0`), proved again in Part II; its order-seven input
  is proved in Part III and also by Part I's Theorem 8.1.
- **`16800^(1/6) ≤ ρ_4 ≤ 840^(1/4)`** (`5.0607… ≤ ρ_4 ≤ 5.3835…`; source 03,
  display (22.4)); Part I gave no bounds at order four.
- **Blowup enclosure for every order** (source 04, Proposition 35.1):
  `min_j r_j ≤ ρ_* ≤ max_j r_j`, `r_j = [A (d)_j]^(1/(d+j))`, `A = (d)_d`. It is
  Part I's `180^(1/4) ≤ ρ ≤ 60^(1/3)` at `d = 3`, the bound above at `d = 4`,
  and `41.0820… ≤ ρ_* ≤ 43.6364…` at `d = 30`.
- **Explicit convergence radii of the local series:** the bidisk
  `max(|q_1|, |q_2|) < 1183/960` at order five (source 02, Section 16) and the
  tridisk `max_j |q_j| < 121/6720` at order seven (source 03, Section 25), in
  the variables `q = C t^λ`, … of the local series. A radius in `t` needs a
  bound on `|C|`, which no source supplies.
- **The complete spectrum at `r = d = 30` as a proved statement** (source 04,
  Proposition 37.1 and Corollary 38.1): all thirty roots of
  `∏_{a=30}^{59}(λ + a) − 2A` are simple, the real parts are strictly ordered,
  the equilibrium is hyperbolic with unstable eigenvalues exactly `1, λ_1, λ̄_1`
  and a 27-dimensional stable subspace; certified by seven exact integer or
  rational inequalities with `q = 911/100`. Part I had this count only as an
  exact Routh check.
- Smaller additions: the Bernoulli-polynomial algorithm for the gamma-ratio
  coefficients `d_j(b)` with `d_2(b)` (source 02); the nonresonance bound
  `|D(β)| ≥ 363/2` at order seven (source 03); the datum that the journal's
  Table 1 entry `5.1792` at `m = 3` cannot be a reciprocal (source 03).
- **Write remarks (5 October 2026, proofs in the text).** Remark 33.1: source
  04's cyclic cone `{V ≤ 2}` *equals* Part I's cone `𝒞_3 = {s^- ≤ 2}`.
  Remark 33.2: hence source 04's Euler-step Lemma 36.2 proves Part I's cone
  invariance (9.16) in every order without the strong-k-positivity
  theorem. Part I's other use of that theorem (Weiss–Margaliot), the strict
  sign-regularity of `T_r = exp(δ J_r)` that Alseidi–Margaliot–Garloff need
  for (9.17), is not replaced. Remark 33.3: credit and a pointer (below).
- *[Independent check, 5 October 2026.]* An adversarial check of Parts II–IV
  made by the intake after the write (`6603ab5a8`) found all eight items it
  examined valid, with no counterexample and no gap in any proof chain:
  Theorem 30.1 with its proof, the write's precision note on the step from a
  recurrence to an ODE, Remarks 33.1–33.3 with Lemma 36.2, the radii
  `1183/960` and `121/6720` with the note that a radius in `t` needs a bound
  on `|c|`, the order dictionary, and `16800^(1/6) ≤ ρ_4 ≤ 840^(1/4)` with
  the extreme `r_j` of Proposition 35.1. Three passages of the write said
  more than the mathematics gives and are corrected where they stand, each
  with a dated note keeping the first wording. Part I uses Weiss–Margaliot
  twice: for the cone invariance (9.16), which Lemma 36.2 replaces, and for
  the strict sign-regularity of `T_r` feeding Alseidi–Margaliot–Garloff's
  spectral step (9.17), which it does not; Part IV's credit-table row
  "Cyclic cone K" and the note after Lemma 36.2 had said that the whole
  strong-k-positivity step was replaced (dated note after Remark 33.2, and
  inside the note after Lemma 36.2). Remark 33.3 said the cyclic count is
  Mallet-Paret and Smith's discrete Lyapunov function for couplings "of
  fixed sign"; they assume strictly signed couplings and weight each change
  by the coupling's sign, so the plain cyclic count is theirs only when every
  coupling is positive (dated note after the remark). Remark 33.2 now names
  the second use of Weiss–Margaliot, and Part I's note after (9.16) says that
  it is still used for `T_r`. The tests, none of which used the delivered or
  the write's programs: a line-by-line reading of the proof of Theorem 30.1
  (the branch-counting argument: the continuations `H_0, …, H_N` around `ρ`
  are independent for every `N`, against the finite-dimensional solution
  space of a linear ODE at an ordinary point), with `D_2`, `D_3`, the
  exponents and the P-recursive-to-D-finite step recomputed; its own
  `h_0..h_600` for A333497, equal to `data/independent-exact_h_0_600.txt`,
  and the A336009 terms against the 31-term OEIS prefix fixture; brute force
  over every `v ∈ {-1,0,1}^d`, `d ≤ 9`, for Remark 33.1 (29,523 vectors);
  200,000 random Euler steps for Lemma 36.2 (and a negative-coupling control
  that raises `V` from 0 to 2); an RK4 run of Part I's nonlinear system at
  `r = 30` for six values of `ρ`, with `V(Z(s)) ≤ 2` throughout; the radii,
  `c_0`, the order dictionary (`59!/(29!)² = 1773968723472921360`), the
  `ρ_4` bounds and the `r_j` extremes re-derived. As corroborating evidence
  only, not part of the proof, a recurrence search over `GF(p)`,
  `p = 2147483629`: 204 systems (both sequences, every order `s ≤ 60` from
  `n = 0` and `s ≤ 40` from `n = 150`, each at the largest degree 601 terms
  allow, e.g. degree 286 at order 1, 42 at order 12, 7 at order 60) all
  have full column rank, so no recurrence of those orders and degrees exists;
  the same code finds the known recurrences of the Apéry numbers and of
  `n![zⁿ] eᶻ/(1-z)³` (positive controls). Theorem 30.1 covers every order
  and degree and does not depend on the search. Its account of Mallet-Paret
  and Smith rests on a citing paper and recollection, not a reread of the
  paper. The record is an unlabelled dated paragraph at the end of
  Section 41. This was a careful reading with exact computations, not a
  formal verification.

### Parts II–IV: second routes (re-proofs of Part I)

| Source | Proves again | Different devices |
|---|---|---|
| 02 (Report 113) | Theorem 1.1 and Corollary 1.2 (its Theorem 13.1; `C_02 = C_I ρ^λ`) | explicit convergent invariant surface with a Catalan majorant and a transverse coordinate instead of Poincaré linearization; `C ≠ 0` by an exact-pole contradiction (`ρ = 3` vs `ρ³ = 60`) |
| 03 (Report 115) | Theorem 8.1 (its Theorem 22.1; `c_0` is Part I's `D`) | derivative limits by integrating the ODE; explicit convergent surface; `C ≠ 0` by a scalar majorant that reaches `z = 0` (`H'(0)/H(0) < 169/175`) instead of the backward Metzler argument |
| 04 (Report 117) | the case `r = 30` of Theorem 9.1 (its Theorem 34.1) | a cyclic sign-change cone invariant by Euler steps; complete spectral ordering by a modulus curve with monotone phase; `E^s ∩ K = {0}` by a leading-mode limit instead of Alseidi–Margaliot–Garloff; the ordinary stable manifold |

The inversion sections of sources 02 and 03 are instances of Part I's
Theorem 7.1 and Section 8.6 and of the repository's transseries volume; no
novelty is claimed for them.

## What is not claimed

- No replacement high-order asymptotic and no periodic limiting profile for
  `m ≥ 29`; no claim that `m = 29` is the first failure (the orders
  `4 ≤ m ≤ 28` remain unresolved after batch 103; Part I's exact Routh check
  shows `r = 29` spectrally stable, which does not settle the orbit);
  Conjecture 2 (even order) is not addressed. Source 04 treats `d = 30` only.
- Numerical constants (`ρ ≈ 3.77462757572068`, `C`, `K`; source 02's 38-digit
  `ρ`; source 03's `ρ_4 ≈ 5.1791758159` and `C`) are fitted and not interval
  certified. Source 02's fits agree with Part I's in all 38 printed digits of
  `ρ` and to 28 digits for `C ρ^λ`: two uncertified fits agreeing, not a
  certificate. `|C|` is quantified nowhere.
- No convergent large-`n` expansion; no summation of infinitely many
  transferred sectors at fixed `n`; the inverse constants are existence
  constants and no unconditional ceiling rule is claimed.
- **Credited, not claimed:** Astashova's real-axis blowup laws (2013,
  Theorem 3, orders 3 and 4; the real input of Part I at order four and of
  source 03), the B-urn spectral family (Chauvin–Gardy–Pouyanne–Ton-That
  2016), Kozlov's large-order instability (1999), the sign-regularity theorems
  (Weiss–Margaliot 2021; Alseidi–Margaliot–Garloff 2019), Lanford's stable
  manifolds, Flajolet–Odlyzko transfer.
- **Likely prior art, credited at the write:** the cyclic sign-change count
  of source 04's Lemma 36.2 is the positive-feedback case of the discrete
  Lyapunov function of J. Mallet-Paret and H. L. Smith, *The
  Poincaré–Bendixson theorem for monotone cyclic feedback systems*, J. Dynam.
  Differential Equations 2 (1990), no. 4, 367–421 (bibliographic data checked
  at the write and again at the independent check; internal statement
  numbers not). They assume strictly signed couplings and count sign changes
  weighted by the coupling signs, which is the plain cyclic count only when
  every coupling is positive; Lemma 36.2 allows vanishing couplings
  (wording corrected at the independent check). Source 04 does not cite it. Their Poincaré–Bendixson theorem
  may bear on the open order-59 question (Part I's Question 1): the
  uncentred Fowler system is a monotone cyclic feedback system, so once the
  normalized orbit is known to be bounded, its limit set may be restricted to
  a periodic orbit or to equilibria and connecting orbits. A pointer, not a
  result (Remark 33.3).
- **Abstracts overstate novelty, corrected by dated notes.** Source 02's "We
  prove the order-five case", source 03's "We prove the order-seven case" and
  source 04's "We disprove the universal form" describe theorems Part I had
  already proved in the repository; Parts II–IV are independent second routes
  (their sources were written without sight of Part I). Each source abstract
  is printed with a dated note.
- Priority rests on bounded searches (Part I: "a bounded negative finding, not
  an exhaustive priority certificate"); sources 02–04 claim no priority.
- **Claims about external sources, kept as the manuscripts':** Theorem 9.1
  refutes a published conjecture; the journal's Table 1 heads its column
  `ρ_m^(-1)` but lists radii (`3.7746` at `m = 2`, Parts I and II; `5.1792` at
  `m = 3`, Part III); source 02 says the case `m = 1` (A007558) is settled by an
  elliptic function. The intake checked the conjecture's constants and reran
  the certificates; it did not re-read the journal's table or the `m = 1`
  claim, nor re-read Astashova's paper.

## Standing rule: unproved and wrong claims

No claim of any source was found to be wrong. The unproved claims and open
questions of sources 02–04 are in "Further questions and research" sections
(20.1, 32.1, 41.3), each merged with Part I's Section 11.2 questions:
certified constants (Part I Q3), higher orders `4 ≤ m ≤ 28` (Q2), other initial
data (Q5), global continuation (Q4, re-scoped by Theorem 30.1), effective
truncation, the order-59 limit set, coefficient asymptotics and inverses at
order 59, the transition across orders (Q1, Q2), the external claims above, and
the write's own question whether source 04's spectral route extends to every
`r ≥ 30`. Part I's questions carry dated notes: Q4 is partly answered (explicit
radii; infinitely many branches at `ρ`), Q1 gains the Mallet-Paret–Smith
pointer, Q2, Q3 and Q5 remain open.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
and its place in the collection gives it no formal status; no manuscript used
a ProveIt theorem. The generic staircase arithmetic named in the Section 7
note is formalized as `Fabius.staircase_ceil` and `Fabius.staircase_separation`
in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `h_n`.

**Neighbouring reports.** No other repository report treats historic trees,
B-tree histories, A333497, A336009 or the Burghart–Wagner conjectures. The
inversion steps are instances of `p0:thm:lambert-core`, `p0:thm:staircase`,
`p0:thm:perturbed-inversion` and (for the all-order Lambert coefficients)
`p0:thm:lambert-centered` in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
Batch 103 also placed a report on one-sided rectangulations
(`../a348351-one-sided-rectangulations/`, bundle Report 111), which proves
non-D-finiteness for another sequence by another method (a log-scale law);
only the conclusion is shared.

## Notation

Part I's letters are fixed by section in the table at the end of Section 1
(`ρ` four ways; `a`, `A`, `B`, `b`, `D`, `K`, `P`, `Q`, `R`, `s`, `L`, `η`, `W`/`Z`
two to four ways each). Parts II–IV keep their sources' letters, and each opens
with its own table (Sections 12.3, 21.4, 33.4) mapping them to Part I with the
false readings. The dangerous ones: source 02's `α` is Part I's `λ` (not its
weight `α = 13/2`) and its `C` is `C_I ρ^λ`; source 03's `H_2`, `H_3` are indexed by
`m`, so its `H_2` is Part I's `H = H_3`; source 03's `c_0` is Part I's `D`; source
04's `d` is Part I's `r`, its `b_j = p^(j)(0)` is the *reciprocal* of Part I's
`b_j = Y_j(0)`, and its `r_j` are radii, not orders; `r` in sources 02 and 03 is
a radius, never an ODE order. No symbol was renamed.

## Labels

Every label carries the prefix `his:`. Part I's 116 labels (106 delivered, all
prefixed by the batch-77 write, plus ten section labels; 76 in `article.tex`,
40 in `extensions.tex`) are unchanged; batch 103 added `his:part:one` and the
labels of Parts II–IV under the sub-prefixes `his:o5:` (53), `his:o7:` (64) and
`his:o59:` (65): 299 labels in all. The sources' labels were prefixed before
anything cited them, and the build of the new text resolves every existing
label to the same number as the build of the committed text. After the
write, the intake's independent check (5 October 2026) corrected the
credit-table row "Cyclic cone K" of Section 33.3, the first two sentences of
Remark 33.3 and the note after Lemma 36.2, added a clause to Remark 33.2 and
a sentence to Part I's note after (9.16), dated notes after Remarks 33.2 and
33.3 and inside the note after Lemma 36.2, pointers in the batch-103 note of
Section 1 and before Theorem 30.1's proof, and an unlabelled dated paragraph
at the end of Section 41; no label was added, and none was renumbered (aux
files compared).

## Files

```text
README.md                                   this guide
REPRODUCIBILITY.md                          source 01's delivered replay guide (delivery paths; see below)
article.tex                                 the report, Parts I-IV (source 01 delivered as historic-trees.tex)
extensions.tex                              Part I Sections 8-9, \input by article.tex (label prefixes; batch-103 dated notes; one sentence of the independent check)
references.bib                              source 01's delivered bibliography (BibTeX)
article.pdf                                 compiled report, 84 pages
figures/oscillation.pdf                     Part I's figure (exploratory)
figures/oscillation.csv                     its data, written by make_figure.py (CRLF, kept by a -text line)
code/build.sh                               source 01: delivered PDF build (compiles historic-trees.tex)
code/replay.sh                              source 01: replay entry point (runs code/run_replay.py)
code/run_replay.py                          source 01: replay driver, ten stages, comparison summary
code/make_figure.py                         source 01: figure/CSV regeneration (needs matplotlib)
code/verify_symbolics.py                    source 01: exact symbolic checks; h_0..h_202
code/numerical_expansion.py                 source 01: 120- and 150-digit fits of rho, Re C, Im C
code/verify_inverse.py                      source 01: exploratory inverse experiments
code/independent_checks.py                  source 01: independent exact h_0..h_600, rational recurrence, DOP853 ODE
code/extensions-verify_stability.py         source 01: Routh certificates r = 2..40, root counts, compound graph, finite bridge
code/extensions-verify_audit.py             source 01: independent order-30 certificate
code/extensions-verify_r4_checks.py         source 01: exact order-4 supplement
code/extensions-verify_phase.py             source 01: independent finite-bridge phase/modulus check
code/extensions-verify_uniform_constants.py source 01: rational constants for r >= 38
code/02-order5-build.py                     source 02: build report113.pdf twice, require byte equality
code/02-order5-pack.py                      source 02: deterministic ZIP builder
code/02-order5-checks-exact_check.py        source 02: exact finite checks (SymPy), h_0..h_500, psi coefficients
code/02-order5-checks-exploratory_fit.py    source 02: 100-digit fits of rho, C (not certified)
code/02-order5-checks-validate.py           source 02: normal/-O runs, 23 fixture and 9 manifest mutations, fresh-directory replay
code/02-order5-checks-check_manifest.py     source 02: closed SHA-256 inventory checker (MANIFEST.json)
code/03-order7-build.py                     source 03: build report115.pdf twice, require byte equality
code/03-order7-pack.py                      source 03: deterministic ZIP builder
code/03-order7-checks-check.py              source 03: exact finite checks (SymPy), sealed-manifest check first
code/03-order7-checks-check_manifest.py     source 03 (and source 04, byte-identical): package CHECKSUMS.sha256 checker
code/03-order7-checks-exploratory_fit.py    source 03: 100-digit fits of rho, C (not certified)
code/03-order7-checks-validate_bundle.py    source 03: replay, integrity and named-mutation harness
code/04-order59-build.py                    source 04: build report117.pdf twice, require byte equality
code/04-order59-pack.py                     source 04: deterministic ZIP builder
code/04-order59-checks-check.py             source 04: the seven exact inequalities, Routh table, identities (standard library)
code/04-order59-checks-validate_bundle.py   source 04: bounded replay and semantic-mutation harness (180 s budget)
02-order5-checks-README.txt                 source 02: delivered checks README (delivery paths)
03-order7-checks-README.md                  source 03: delivered checks README (delivery paths)
04-order59-checks-README.md                 source 04: delivered checks README (delivery paths)
data/producer-exact_values_0_202.json                    source 01: exact h_0..h_202
data/producer-symbolic_validation.json                   source 01: exact symbolic checks
data/producer-numerics_120dps.json                       source 01: 120-digit fit (exploratory)
data/producer-numerics_150dps.json                       source 01: 150-digit fit (exploratory)
data/producer-inverse_validation.json                    source 01: inverse experiments (exploratory)
data/independent-exact_h_0_600.txt                       source 01: exact h_0..h_600 (SHA-256 aa02b70d…bf635, as printed in Section 10.1)
data/independent-independent_checks.json                 source 01: independent checks (mixed exact/float)
data/extensions-routh_certificates_2_40.json             source 01: exact Routh certificates, orders 2..40
data/extensions-independent_complex_root_counts.json     source 01: exact complex root counts at orders 29, 30
data/extensions-compound_graph_certificate.json          source 01: order-30 third-compound graph
data/extensions-certificate.json                         source 01: independent order-30 certificate
data/extensions-rational_phase_certificates_30_37.json   source 01: finite-bridge phase/modulus margins
data/extensions-phase_certificate.json                   source 01: independent phase check
data/extensions-phase_finite.json                        source 01: second original phase reference
data/extensions-r4_exact_certificate.json                source 01: exact order-4 supplement
data/extensions-exact_h_r4_0_100.json                    source 01: exact g_0..g_100 (A336009)
data/extensions-uniform_threshold_certificate.json       source 01: rational constants for r >= 38
data/provenance.json                        source 01: original and bundled SHA-256 of scripts and reference artifacts
data/verified_replay.json                   source 01: earliest replay snapshot (order 3)
data/verified_extension_replay.json         source 01: intermediate snapshot (orders 4 and 30)
data/verified_final_replay.json             source 01: final replay snapshot
data/requirements.txt                       source 01: mpmath 1.3.0, sympy 1.14.0, numpy 2.3.5, scipy 1.17.0
data/requirements-figure.txt                source 01: adds matplotlib 3.10.8
data/02-order5-checks-fixtures.json                       source 02: exact formulas and the 29-term OEIS display (CC BY-SA 4.0 terms)
data/02-order5-checks-exact_results.json                  source 02: frozen exact-check output
data/02-order5-checks-exploratory_results.json            source 02: frozen 100-digit fits (exploratory)
data/02-order5-checks-validation_results.json             source 02: delivered validation run (PASS)
data/03-order7-checks-fixtures-oeis_A336009_prefix.json   source 03: the 31 displayed OEIS terms (CC BY-SA 4.0)
data/03-order7-checks-fixtures-recurrence_terms_0_500.txt source 03: 501 generated exact terms of A336009 (not an OEIS table)
data/03-order7-checks-fixtures-reference_formulas.json    source 03: exact constants and coefficients
data/03-order7-checks-fixtures-exploratory_reference.json source 03: reproduced exploratory fit (exploratory)
data/03-order7-verification_results.json                  source 03: delivered validation run (PASS)
data/04-order59-checks-fixtures-certificate.json          source 04: exact d = 30 certificate fixture
data/04-order59-checks-requirements.txt                   source 04: "standard library only"
data/04-order59-verification_results.json                 source 04: delivered validation run (PASS)
```

Every file except `README.md`, `article.tex`, `extensions.tex` and
`article.pdf` is byte-identical to its delivery.

Placement of source 01 renamed `historic-trees.tex` to `article.tex`, moved
`build.sh`, `replay.sh` and `make_figure.py` to `code/`, flattened
`code/extensions/` to `code/extensions-*.py` and `data/{producer,independent,
extensions}/` to `data/<subdirectory>-*`, and moved both requirements files to
`data/`. Not shipped: the delivered PDF `historic-trees.pdf` and
`MANIFEST.sha256` (verified 44/44, retired). Retrieve with
`git show 096ee7b87:docs/incoming/historic-tree-report.zip > <scratch>/historic-tree-report.zip`.

Placement of sources 02–04 (`9c995cefe`) flattened `reportNNN/checks/…` to
`code/0k-…-checks-*.py`, `data/0k-…-checks-*` and the root
`0k-…-checks-README.*`, and `reportNNN/{build,pack}.py` to `code/0k-…-*.py`.
**Not shipped** (all in the archives of arrival commit `60f54ea06`, retrieve
with `git show 60f54ea06:docs/incoming/<archive>.zip > <scratch>/<archive>.zip`):
the three manuscripts `reportNNN.tex` and their PDFs (printed in full in
Parts II–IV); the three delivery `README.txt`; source 02's `MANIFEST.json` and
`checks/recurrence_terms_0_500.txt` (byte-identical to the first 501 lines of
`data/independent-exact_h_0_600.txt`: rebuild it with
`head -n 501 data/independent-exact_h_0_600.txt`); sources 03 and 04's
`CHECKSUMS.sha256` and `checks/MANIFEST.json` (all verified at placement);
source 03's generic `checks/requirements.txt` (SymPy 1.14.0, mpmath 1.3.0);
source 04's `checks/check_manifest.py` (byte copy of
`code/03-order7-checks-check_manifest.py`). Nothing heavy was excluded.

Delivered text that names the delivery layout or unshipped files:
`REPRODUCIBILITY.md`, `code/build.sh`, `code/replay.sh`, `code/run_replay.py`,
`code/make_figure.py`, `data/provenance.json` and Part I's Sections 10.1 and
10.3 (source 01; see the rerun section); the three checks READMEs (they run
`check.py`, `validate_bundle.py`, `check_manifest.py ..` from inside
`checks/`, and refer to `MANIFEST.json`, `CHECKSUMS.sha256`, `README.txt`,
`/tmp/…` outputs); the `build.py` scripts (compile `reportNNN.tex`); the
`pack.py` scripts; Sections 19, 31 and 42 of the article (the sources'
reproducibility sections, each with a dated note giving the shipped names).

Byte-level notes. `figures/oscillation.csv` is the only CRLF file; the line
`.../a333497-historic-trees/figures/oscillation.csv -text` in
`SetTheory/Cardinals/.gitattributes` keeps its bytes. Five source-01 JSON
certificates
(`data/extensions-{compound_graph_certificate,independent_complex_root_counts,phase_finite,rational_phase_certificates_30_37,routh_certificates_2_40}.json`)
have no final newline; keep them so, because `data/provenance.json` hashes the
exact bytes. OEIS terms in `data/02-order5-checks-fixtures.json` (29 terms of
A333497) and `data/03-order7-checks-fixtures-oeis_A336009_prefix.json` (31
terms of A336009) are OEIS data, CC BY-SA 4.0.

## Rerun the checks (on scratch copies only)

Never run the scripts in this directory: they expect the delivered layouts and
some write next to themselves.

### Source 01 (Part I)

The scripts use delivery-relative paths, and `run_replay.py` first checks every
script and reference artifact against `data/provenance.json` at its delivered
path. Rebuild the delivered layout on a copy, then replay into an empty
directory outside it (Git Bash, from this directory):

```sh
R=$(mktemp -d)/historic-tree-release
mkdir -p "$R"/code/extensions "$R"/data/producer "$R"/data/independent "$R"/data/extensions "$R"/figures
for f in code/*; do b=${f#code/}; case $b in
  0[234]-*) ;;
  extensions-*) cp "$f" "$R/code/extensions/${b#extensions-}";;
  make_figure.py|build.sh|replay.sh) cp "$f" "$R/$b";;
  *) cp "$f" "$R/code/$b";; esac; done
for f in data/*; do b=${f#data/}; case $b in
  0[234]-*) ;;
  producer-*) cp "$f" "$R/data/producer/${b#producer-}";;
  independent-*) cp "$f" "$R/data/independent/${b#independent-}";;
  extensions-*) cp "$f" "$R/data/extensions/${b#extensions-}";;
  requirements*) cp "$f" "$R/$b";;
  *) cp "$f" "$R/data/$b";; esac; done
cp figures/* "$R/figures/"; cp article.tex "$R/historic-trees.tex"; cp extensions.tex references.bib "$R/"
cd "$R"
PYTHONUTF8=1 uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 \
  --with numpy==2.3.5 --with scipy==1.17.0 python code/run_replay.py --output-dir "$(mktemp -d)"
```

(The two `0[234]-` cases skip the files of sources 02–04. `bash replay.sh`
from `$R` does the same with `python3`. The replay does not read the TeX
files; to rebuild the delivered 26-page PDF with `bash build.sh`, take
`historic-trees.tex` and `extensions.tex` from the archive,
`git show 096ee7b87:docs/incoming/historic-tree-report.zip`, since the
report's copies now hold Parts II–IV and the dated notes.) At intake (2 October 2026, heavily
loaded machine) one call took 143 s and all ten stages exited 0 with matching
provenance hashes. **On Windows the driver reports `FAIL`**: the producers
write with `Path.write_text`, which emits CRLF there, while `run_replay.py`
compares bytes against LF references. Byte identity holds on POSIX; on
Windows compare after CRLF→LF — at intake all twelve exact artifacts and the
three producer float JSONs were then byte-identical, and the only other
difference was the last digit of the double-precision `rho_approx` in
`independent_checks.json`.

### Sources 02–04 (Parts II–IV), route A: the exact checks from the shipped files

Rebuild the three `checks/` directories on a copy (Git Bash, from this
directory). Source 02's term file is regenerated from Part I's table; sources
03 and 04 have no shipped manifests, so their checkers run with
`--skip-integrity` (the checkers' development option: the mathematics is
checked, the sealed inventory is not).

```sh
R=$(mktemp -d)
mkdir -p $R/report113/checks $R/report115/checks/fixtures $R/report117/checks/fixtures
for f in check_manifest exact_check exploratory_fit validate; do cp code/02-order5-checks-$f.py $R/report113/checks/$f.py; done
for f in exact_results exploratory_results fixtures validation_results; do cp data/02-order5-checks-$f.json $R/report113/checks/$f.json; done
head -n 501 data/independent-exact_h_0_600.txt > $R/report113/checks/recurrence_terms_0_500.txt
for f in check check_manifest exploratory_fit validate_bundle; do cp code/03-order7-checks-$f.py $R/report115/checks/$f.py; done
for f in data/03-order7-checks-fixtures-*; do cp $f $R/report115/checks/fixtures/${f#data/03-order7-checks-fixtures-}; done
for f in check validate_bundle; do cp code/04-order59-checks-$f.py $R/report117/checks/$f.py; done
cp data/04-order59-checks-fixtures-certificate.json $R/report117/checks/fixtures/certificate.json
cd $R
PYTHONUTF8=1 uv run --no-project --with sympy==1.14.0 python -B report113/checks/exact_check.py --output "$(mktemp -d)/o113.json"
PYTHONUTF8=1 uv run --no-project --with sympy==1.14.0 python -B report115/checks/check.py --skip-integrity
python -B report117/checks/check.py --skip-integrity
```

At the write (5 October 2026, Windows, loaded machine): source 02
`PASS_EXACT_FINITE_CHECKS` in 3 s, output equal to the frozen
`exact_results.json`; source 03 `PASS` in 16 s; source 04 `PASS` in under 1 s.

### Sources 02–04, route B: the sealed packages and the full harnesses

The validation harnesses need the sealed delivered layouts. Extract the three
archives into a scratch directory:

```sh
R=$(mktemp -d); cd $R
for z in A333497_B_Tree_Histories_All_Orders_and_Inversion_Source \
         A336009_B_Tree_Histories_Transseries_and_Non_D_Finiteness_Source \
         B_Tree_Order_59_Counterexample_to_the_Universal_Asymptotic_Conjecture_Source; do
  git -C <repository root> show 60f54ea06:docs/incoming/$z.zip > $z.zip
  python -m zipfile -e $z.zip .
done
```

On POSIX the delivered commands then work as documented (`python
report113/checks/validate.py --with-numerics --output …`;
`cd report115/checks && python -B validate_bundle.py --with-exploratory
--output …`; `cd report117/checks && python -B validate_bundle.py --output …`;
outputs outside `checks/`). **On Windows all three harnesses fail for reasons
of the harnesses, not of the mathematics:**

- source 02, `validate.py --with-numerics`: FAIL at the `changed_size` control
  (after the baseline, the numerics and 23 fixture and 9 manifest mutations
  pass), because `write_text('abc\n')` writes CRLF, so the payload is 5 bytes,
  the size of the mutated file;
- source 03, `validate_bundle.py`: ERROR, `os.mkfifo` does not exist on Windows
  (one POSIX-only negative control);
- source 04, `validate_bundle.py`: `HARNESS_TIMEOUT`; its fixed budget of 180 s
  total and 15 s per process is too short for about 380 Python subprocesses on
  a loaded Windows machine (it also has two `os.mkfifo` controls).

The patches, applied to the extracted copies only: in source 02's
`checks/validate.py` replace both `(simple/'payload.txt').write_text('abc\n')`
by `(simple/'payload.txt').write_bytes(b'abc\n')`; in source 03's
`checks/validate_bundle.py` delete the line containing
`('package_special_file','MANIFEST_SPECIAL_FILE',lambda r:os.mkfifo(`; in
source 04's set `PER_PROCESS_SECONDS=120`, `TOTAL_SECONDS=3600` and delete the
two lines containing `os.mkfifo(`; then, for sources 03 and 04, write the new
SHA-256 of `checks/validate_bundle.py` into `checks/MANIFEST.json` and the new
hashes of `checks/validate_bundle.py` and `checks/MANIFEST.json` into
`CHECKSUMS.sha256`. Results: at intake the patched source 02 harness exited 0
in 3 min and the patched source 03 harness in 4 min, both equal to the
delivered result files except the patched script's hash (and, for source 03,
the removed case); at the write the patched source 04 harness passed in 74 s
with 338 mutation runs (delivered: 340; the two removed controls), and the
resealed source 03 package passed `check.py` with integrity in 16 s. The
delivered result files `data/0k-…validation_results.json` /
`verification_results.json` record the delivered (POSIX) runs.

## Build the PDF

pdfLaTeX and BibTeX (amsmath, amssymb, amsthm, mathtools, booktabs, graphicx,
microtype, enumitem, array, hyperref, lmodern). From a scratch copy of this
directory (`article.tex`, `extensions.tex`, `references.bib`, `figures/`):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 83 pages, no
errors or warnings (LaTeX or BibTeX), no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes; every Part I label has the same number as in the build of the
batch-77 text (28 pages). After the independent check of 5 October 2026 it was
rebuilt the same way with pdfLaTeX and BibTeX (four pdfLaTeX passes): 84 pages
(was 83), the same clean log, all 299 labels with the same numbers and the
same bibliography numbers as before; Parts I–III keep their pagination. `code/build.sh` and the three `build.py` scripts are
kept as delivered; they compile the delivered sources, not `article.tex`.

## Provenance

- Burghart–Wagner, Theoret. Comput. Sci. 1070 (2026) 115821 (Conjecture 1),
  and AofA 2024, LIPIcs 302, 10 (Conjecture 10); Astashova, Adv. Difference
  Equ. 2013:220 and St. Petersburg Math. J. 31 (2020); Kozlov, Ark. Mat. 37
  (1999); Chauvin–Gardy–Pouyanne–Ton-That, ALEA 13 (2016); Weiss–Margaliot,
  Automatica 123 (2021); Alseidi–Margaliot–Garloff, J. Math. Anal. Appl. 474
  (2019); Lanford, ETH lecture notes (1997); Ilyashenko–Yakovenko (2008);
  Flajolet–Sedgewick (2009); Flajolet–Odlyzko, SIAM J. Discrete Math. 3 (1990)
  (sources 02, 03; cited inline as [FO]); Mallet-Paret–Smith, J. Dynam.
  Differential Equations 2 (1990) (credited at the write, cited inline); OEIS
  A333497, A336009 (inspected 2 October 2026).
- Repository input: none recorded; no source has a pin.
- Source 01: batch 77 of `docs/incoming`, manuscript 24 (cluster P3); arrival
  `096ee7b87`, placement `34f1acd4b`, written in the batch-77 write
  (`48c008375`, 2 October 2026).
- Sources 02–04: bundle Reports 113, 115, 117 of batch 103; arrival
  `60f54ea06`, placement `9c995cefe`, written in the batch-103 write
  (5 October 2026). Merge choices: each manuscript is printed in full as its
  own Part, after Part I, in archive order; the existing text became Part I
  with no label or number changed; Part I's appendix stays last (it belongs to
  Part I), so source 04's appendices are printed as Sections 43–44; duplicated
  theorems are printed again and marked as second routes, because their proofs
  differ; citation keys were mapped to `references.bib`, with Flajolet–Odlyzko
  and Mallet-Paret–Smith cited inline because `references.bib` stays as
  delivered.
