# Global Support Obstructions: Moving Divisors, Mittag–Leffler, and a Picard Dichotomy

*Two ordinary bases, one coefficient sheaf: the noncompact plane, and a compact Riemann surface.*

`article.tex` / `article.pdf` — one merged research article, 69 pages, 92 numbered results, self-contained LaTeX with an internal bibliography. Build with

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

## What the report is

A local-to-global theory for the sheaf `ℋ_Γ` of well-ordered Hahn series whose coefficients are ordinary holomorphic functions on a **common** ordinary domain, over a fixed set-sized surreal value group `Γ ⊆ No`, together with its nonnegative-support subring sheaf `ℋ_{Γ,≥0}` and its positive-support additive subsheaf `ℋ_{Γ,+}`.

The article has **two parts, over two different ordinary bases**, and neither contains the other.

**Part I (§§1–15), base `ℂ`.** When do infinitely many individually legitimate infinitesimal prescriptions admit one coherent global realization over the ordinary complex plane? The answer is always a well-ordering condition on the right invariant.

**Part II (§§16–23), base a compact connected ordinary Riemann surface `X` of genus `g`.** Only finitely many clusters can be prescribed, so the well-ordering question is vacuous and what remains is cohomological: the Picard group is classified completely, sections are obstructed by a valuation monodromy, and a finite matrix computes the rest.

§16.1 states, and the article repeats at each point of use, that **neither part may be quoted for the other's base**. The compact comparison theorem (Thm 17.7) uses compactness twice — finite-dimensional ordinary harmonic spaces, and one global well-ordered support bound for smooth Hahn forms (Lem 17.2) — and *must not be applied to the plane by setting `X = ℂ`, `g = 0`* (Rem 17.8). Conversely the plane obstructions come precisely from infinitely many centres, which a compact base cannot carry.

### Part I headline results (base `ℂ`)

- **Sharp moving-divisor criterion** (Thm 8.2). A cluster family `P_c(u) = u^{m_c} + Σ_{j<m_c} a_{c,j} u^j`, `a_{c,j} ∈ 𝔪_Γ`, over a closed discrete ordinary `A ⊂ ℂ` is the exact zero divisor of a nonzero `F ∈ ℋ_Γ(ℂ)` **iff** the *symmetric support* `E(P) = ⋃_c ⋃_j supp(a_{c,j})` is well ordered — the supports of the symmetric coefficients, not of separately chosen roots. When it holds, any prescribed ordinary entire `f_0` with the right ordinary divisor can be kept as the exponent-zero coefficient, with support in `E(P)*`.
- **The two discriminating examples.** `n + t^{1/n}` alone is not realizable (descending symmetric support `{1/n}`); *all* roots of `(z−n)^n = t` are, with symmetric support the singleton `{1}`. Hence a globally principal effective divisor can have a nonprincipal effective sub-divisor.
- **Mittag–Leffler**, at the ordinary centres (Thm 7.2: solvable iff the union of principal-part supports is well ordered) and for **moving poles** relative to an admissible bound (Thm 11.1).
- **Support-restricted Chinese remainder theory** (§10): the correct target of global interpolation is the restricted product `𝔅(P)` of the `K_Γ[u]/(P_c)`, with an explicit Neumann right inverse, and `ℋ_Γ(ℂ)/(G) ≅ 𝔅(P)`.
- **Exact Cousin criterion** (Thm 13.1) on the puncture-and-disk cover, in terms of the *singular support* `Σ(b)`: only exponents carrying nonremovable ordinary coefficient singularities count.
- **PID stalks and the Picard dichotomy over the plane** (Thm 6.1, Thm 14.3, Thm 14.4): every ordinary-base stalk is a principal ideal domain though nonlocal when `Γ ≠ {0}`, so tensor-invertible = locally free rank one here; `Pic(ℂ, ℋ_Γ) = 0` iff `Γ = {0}` or `Γ = Zδ`; otherwise `dim_ℂ Pic ≥ 2^ℵ₀`, with equality for countable noncyclic `Γ`, so `dim_ℂ Pic(ℂ, ℋ_ℚ) = 2^ℵ₀`.

### Part II headline results (base compact `X`)

- **Compact cohomology comparison** (Thm 17.7). For an ordinary holomorphic bundle `V` and `q = 0, 1`, `H^q(X, V_Γ) ≅ H^q(X, V) ⊗_ℂ K_Γ`, and likewise with `𝒪_Γ` and `𝔪_Γ` for the nonnegative- and positive-support sheaves; higher cohomology vanishes. So `H¹(X, ℋ_{Γ,+}) ≅ H¹(X, 𝒪_X) ⊗ 𝔪_Γ` and `H⁰(X, ℋ_Γ) = K_Γ`.
- **Exact Picard classification** (Thm 18.3). `Pic_lf(X, ℋ_Γ) ≅ H¹(X, Γ) ⊕ Pic(X) ⊕ (H¹(X, 𝒪_X) ⊗ 𝔪_Γ) ≅ Γ^{2g} ⊕ Pic(X) ⊕ 𝔪_Γ^g`; the integral version drops the first summand and the extension `ℋ_{Γ,≥0} → ℋ_Γ` is injective with image the zero-valuation sector.
- **Valuation monodromy is exactly the meromorphic obstruction** (Thm 20.1). A nonzero coherent meromorphic section exists **iff** the valuation class vanishes in `H¹(X, Γ)`; otherwise `H⁰(X, L) = 0` at *every* degree. Ex 20.3 gives bundles of arbitrarily high degree with no nonzero coherent meromorphic or holomorphic section — the sharpest single statement of Part II, and the one that rules out naive comparison with algebraic Riemann–Roch over `K_Γ`. Cor 20.2: divisor classes occupy precisely the zero-valuation sector.
- **A finite obstruction matrix** (Thm 19.2, Cor 19.4). In the zero-valuation sector, `B = p₁ δ (1 + h δ)^{-1} i₀` is an honest finite matrix over `𝒪_Γ` with all entries in `𝔪_Γ`; `H⁰ ≅ ker B`, `H¹ ≅ coker B`, and `h⁰ − h¹ = d + 1 − g` with **no valuation-rank and no cofinality hypothesis**. The Neumann inverse is a Hahn identity, not a limit. Prop 19.5 records integral torsion: on an elliptic curve `H¹` of the integral model is `𝒪_Γ / λ𝒪_Γ` while the field-coefficient cohomology vanishes in both degrees.
- **A root-free Abel criterion** (Thm 21.5). A finite signed cluster Cartier datum is principal **iff** its ordinary divisor is principal and the Newton-power-sum functional `𝒜_D(η)` vanishes for every ordinary holomorphic differential. Defined by the integer Newton recurrences and *not* by choosing roots, so it is stated over arbitrary — not necessarily divisible — ordered groups, with `𝒜_D(η) = −Σ_c Res_c(ℓ_c η)`. Ex 22.3: on `y² = 1 + x⁵`, `P⁺ = u² − s`, `P⁻ = u²` has `p₁ = 0` for both clusters, yet `𝒜(x dx/y) = s + s⁶/16 + 35s¹¹/1408 + …` is nonzero, so the balanced cluster is provably not principal.
- **What one scale can see** (Thm 23.3). `Pic_lf(X, ℋ_{Γ,≥0}) → lim_n Pic_lf(X, ℋ_{Γ,≥0}/t^{nδ})` is split surjective onto `Pic(X) ⊕ (H¹(X, 𝒪_X) ⊗ 𝔪_Δ)` with kernel exactly `H¹(X, 𝒪_X) ⊗ I_δ`, injective **iff** `g = 0` or `Δ = Γ`. Ex 23.5, the `t^ω` witness in `Γ = ℚ + ℚω`: nontrivial over both sheaves, trivial mod `t^n` for every integer `n`. Cor 23.6: for *any* set `B` of positive surreal exponents there is a set-sized `Γ ⊇ B` and a nontrivial integral bundle invisible modulo every `t^β` and every integer multiple thereof.

### The two bases side by side (§18.3)

| | base `ℂ` | base compact `X` |
| --- | --- | --- |
| prescriptions | infinitely many centres | finitely many centres |
| governing invariant | well ordering of one global support | ordinary cohomology of the base |
| `H¹(base, Γ)` | `0` | `Γ^{2g}` — the valuation monodromy |
| ordinary Picard factor | `0` | `Pic(X)`, nonzero already for `g = 0` |
| infinitesimal factor | `H¹(ℂ, ℋ_{Γ,+})`, **not** computed in general | `𝔪_Γ^g`, computed exactly |
| vanishing | iff `Γ = 0` or `Γ = Zδ` | never for `g ≥ 1`, `Γ ≠ 0`; `= Z` for `g = 0` |

Ex 22.1 computes `Pic_lf(ℙ¹, ℋ_Γ) = ℤ` with no Abel obstruction, and flags explicitly that **this is not a Mittag–Leffler assertion for the noncompact plane**, where the same `Γ = ℚ` gives `dim_ℂ Pic = 2^ℵ₀`.

## Which archives it came from

Sources are in `sources/`:

| file | manuscript |
| --- | --- |
| `09-moving-divisors-picard-dichotomy.tex` | **Manuscript A**, "Global Support Obstructions in Surcomplex Analysis: Moving Divisors, Mittag–Leffler Theory, and a Picard-Group Dichotomy" (archive `surcomplex_global_support`) |
| `10-cohomological-obstructions.tex` | **Manuscript B**, "Global Divisors and Cohomological Obstructions in Hahn-Coherent Surcomplex Analysis" (archive `surcomplex_global_theorems`) |
| `11-compact-curve-picard-classification.tex` | **Manuscript C**, "Compact-Curve Geometry over Surcomplex Hahn Fields: Picard classification, valuation monodromy, finite cohomology models, and an exact Abel criterion" (archive `surcomplex_compact_curves`) |

Manuscripts A and B are continuations of the supplied `surcomplex_analysis(3).tex`, 21 September 2026, from which the Hahn-coherent framework, evaluation, support-preserving gluing, local preparation, division, root lifting and pole-free fractions are inherited and credited rather than claimed. Manuscript C is a continuation of a different kind: it was written against **this repository**, inspected at commit `aa846271b4dcae2c055b216126a87210292ec19b` (documentation index and this README), changed nothing remotely, and names the gap it fills — "The global-divisors report explicitly emphasizes common ordinary domains and noncompact support obstructions. It does not provide the compact-base classification or the fixed-scale Picard comparison proved here."

Code and data:

| file | what it is |
| --- | --- |
| `code/09-moving-divisors-picard-dichotomy.py`, `code/10-cohomological-obstructions.py` | Manuscript A and B symbolic checks (Appendix B) |
| `code/11-compact-curve-picard-classification-verification.py`, `-Makefile` | Manuscript C symbolic checks, recorded 53/53 exact |
| `data/*-verification*.{txt,json}`, `data/*-requirements.txt` | recorded outputs and the pinned `sympy==1.14.0` |

A and B overlap heavily: both prove the same sharp divisor criterion, use the same pair of discriminating examples, prove the matching principal-parts criterion, derive the same line-bundle dichotomy, use the same classical inputs (Weierstrass products, Mittag–Leffler, `H¹(ℂ,𝒪) = 0`), and both insist that Cartan's theorem is not being applied to a sheaf that is not a coherent `𝒪`-module and that this category is not Müller–Strohmaier's. The shared core is printed once, in Manuscript A's version. C shares with them only the support calculus (Lem 2.1) and the unit splitting (Prop 3.5), both of which it proves for itself and which are printed once, in Part I.

### What each contributed

**Manuscript A** (the base of Part I — it proves strictly more at both points where A and B differ):

- Thm 6.1, PID stalks, with the degree function and gcd/Euclidean argument covering *arbitrary* ideals, nonlocality for every `Γ ≠ 0`, and the maximal ideals `(u − ε)` with residue field `K_Γ` for divisible `Γ`.
- Cor 6.3, the proof that tensor-invertible ⇒ rank-one locally free here, with the named Stacks Tag 09NT appeal.
- Thm 14.4, the **exact** dimension `2^ℵ₀` for countable noncyclic `Γ` (almost-disjoint prefix family for the lower bound; cocycle counting for the upper).
- §12 entirely: the near-identity automorphism theorem, exact interpolation of simple motions, and the Catalan inverse of `z + tz²`.
- Cor 9.3, the principal divisor with a nonprincipal effective sub-divisor, both halves shown nonrealizable, plus "no repair by enlarging the value group".
- The explicit construction of the `(z−n)^n = t` realizer from a Weierstrass product and the series `b_k`.
- Thm 7.2 (fixed-centre Mittag–Leffler) with Cor 7.3; Thm 13.3 (the `𝒱_Γ/𝒲_Γ` obstruction subspace), Ex 13.6, Prop 13.7.

**Manuscript B**:

- §4, constructive scalar tools: Weierstrass/Mittag–Leffler, discrete Hermite interpolation with a linear right inverse, and a from-scratch scalar additive Cousin theorem via ∂̄ and corrected Cauchy transforms.
- Deformed division with the `S + E*` certificate, and the pole-free-fraction lemma.
- §10 entirely: the restricted product algebra `𝔅(P)`, deformed Hermite interpolation with the explicit Neumann interpolator `𝓘_P(B) = L Σ_k (−NL)^k B`, the CRT quotient, and the 0/1 root-selector counterexample.
- §11, moving-pole Mittag–Leffler, and the example with globally realizable poles but non-well-ordered individual residue scales.
- Thm 13.1, the exact (iff) Cousin criterion with the singular support `Σ(b)`, plus the cohomology-free correcting-polynomial construction.
- The positive half of the stalk proposition: `ℋ_{Γ,≥0}` **is** local, residue field `ℂ`, `ℋ_{Γ,≥0}/ℋ_{Γ,+} ≅ 𝒪` — the integral model.
- Prop 14.6 in containment form, and Prop 15.1, the locally principal effective divisor with principal ordinary reduction but nontrivial bundle.
- The `Pic_lf` versus tensor-invertible distinction with its Stacks citation, kept as the statement of what Manuscript A's PID theorem buys.

**Manuscript C** — the whole of Part II, §§16–23:

- Lem 17.2 compact support uniformity, Lem 17.4 the operator form of the Neumann inverse, Prop 17.6 the coefficientwise Dolbeault resolution, Thm 17.7 the comparison theorem, and Rem 17.8, the load-bearing warning that compactness is used twice.
- Thm 18.3 the exact Picard classification, with the normal cocycle of §18.2 and Rem 18.4, which states what is *not* computed.
- §19: Prop 19.1 the positive Dolbeault normal form, Thm 19.2 the finite matrix, Cor 19.4 Riemann–Roch, Prop 19.5 with the elliptic integral torsion, Cor 19.6 base extension.
- §20: Thm 20.1 the meromorphic criterion, Cor 20.2 the divisor-class sequence, Ex 20.3 high degree without sections.
- §21: Lem 21.2 the Newton/logarithm identity, Def 21.3 and Prop 21.4 the Abel functional and its residue formula, Thm 21.5 the criterion, Rem 21.6 on periods versus infinitesimal displacement.
- §22: the sphere, the elliptic displacement conservation, and the genus-two `y² = 1 + x⁵` witness.
- §23: Lem 23.1 truncated Picard, Lem 23.2 the coefficient inverse limit, Thm 23.3 the one-scale comparison, Ex 23.5 the `t^ω` witness, Cor 23.6 the set-indexed detection obstruction.
- The compact rows of Appendix A and the compact half of Appendix B.

### The conflicts, and how they are resolved

**A versus B, on the size and the category of the plane Picard group.** They diverge on whether the dichotomy holds for **all tensor-invertible modules** or only for **locally free rank-one sheaves**, and on how large the group is. Both agree the stalks of `ℋ_Γ` are not local for `Γ ≠ 0`. A proves the PID stalk theorem, deduces tensor-invertible ⇒ rank-one locally free, and states the dichotomy for the unrestricted `Pic`; B explicitly refuses that substitution ("We do not silently substitute the larger category of all tensor-invertible modules on an arbitrary ringed space"), restricts to `Pic_lf`, and claims only that the group *contains* a copy of `ℂ^ℕ/ℂ^(ℕ)`.

The merge does not average this. Thm 6.1 is printed with its proof; Rem 6.4 states that this theorem is exactly what licenses dropping the "locally free" qualification, keeps B's distinction and its Stacks Tag 09NT citation as the statement of what is at stake, and records that every Picard statement specializes verbatim to `Pic_lf` and to `Pic(ℂ, ℋ_{Γ,≥0})` for a reader who declines it. Rem 14.5 does the same for the size.

**C, independently, declines the same identification.** Written without access to A or B, C defines `Pic_lf` by actual rank-one local trivializations, says explicitly that an ordinary-base Hahn stalk may not be a local ring, and states that it "does not assume the repository's unrefereed claims about principal ideal stalks". That is recorded as Rem 18.5 and noted in Rem 6.4: it is an independent confirmation of Prop 6.2 (nonlocality), not a competing claim. Nothing in Part II imports Thm 6.1, and no analogue of it over a compact base is asserted.

**Cofinality, used for two different jobs.** Part I's Rem 2.2 and Part II's Rem 17.5 both record that `nδ` need **not** eventually exceed every positive element of `Γ` — the witness in both is `Γ = ℚ + ℚω`, where `n < ω` for every integer `n`. C's version is kept verbatim in Part II because it is what prevents its Neumann inverse from being misread as a convergence argument: the mechanism is finite decomposability of an *exact* exponent, not domination. Cofinality enters Part II at exactly one place, Thm 23.3, where `Δ = Γ` decides whether a one-scale test is faithful.

## Ring discipline

Every numbered statement is over **one** coefficient ring family and says so: `ℋ_Γ(U) = 𝒪(U)((t^Γ))`, whose Hahn coefficients are ordinary holomorphic on the **common** domain `U`, together with its subsheaves `ℋ_{Γ,≥0}`, `ℋ_{Γ,+}`, and — in Part II only — the ordinary-meromorphic-coefficient sheaf `ℳ_Γ` and the smooth Hahn forms. **The ordinary base is part of the statement**: `U ⊆ ℂ` in Part I, `U ⊆ X` in Part II, and every theorem names its base (§1.2). Two rings inside that family are named apart where it matters — the fixed-disk ring `𝒪(D)((t^Γ))`, where preparation and division happen, and the ordinary-base stalk `R_c`, a filtered colimit of those, of which the PID theorem speaks. `𝒪(D)((t^Γ))` for fixed `D` is *not* claimed to be a PID. Nothing is stated over, or transported to or from, a radius-free ring `ℂ{z}((t^Γ))` of individually convergent coefficient germs with no common domain, or a formal ring `ℂ[[z]]((t^Γ))`; the common-domain hypothesis is load-bearing in the sheaf property, in the "no disk shrinking" clause of the divisor recursion, and in the uniform support bound of local preparation. Appendix D tabulates the symbols, with a separate block for the compact part.

## Notation

One symbol per concept, fixed in §1.2. `ℋ_Γ, ℋ_{Γ,≥0}, ℋ_{Γ,+}`; `𝔪_Γ` for the infinitesimals of `K_Γ` and `𝔪_SC` for those of `SC`; `Exp_H`/`Log_H` for the positive-support exponential and logarithm, kept apart from the ordinary `e^h`; `E(P)` for the symmetric support (Manuscript A writes `S_𝒟`); `ℛ_P` for the deformed remainder map; `Σ(b)` for the singular support; `𝒱_Γ/𝒲_Γ` for the obstruction quotient. The exponent-zero coefficient map `ℋ_{Γ,≥0} → 𝒪` is called the **reduction** throughout; the sources and the literature also call it the residue map, the standard part and the shadow — noted once, then unused. Part II adds `ℳ_Γ`, `𝒟_Γ`, `𝒜^{0,q}_Γ`, the three classes `ν(L), L_0, ξ(L)`, the Hodge data `i_q, p_q, h, δ, T, B`, the Newton sums `p_k(P)` and Abel functional `𝒜_D(η)`, and `Δ, I_δ, ℛ_n` for the one-scale material. `𝒪_Γ` is the valuation ring of `K_Γ` — Manuscript C writes `R_Γ` — and is a ring of scalars, never the structure sheaf `𝒪_X`. All `\label`s are prefixed `global:`.

## What is not proved

Preserved from all three manuscripts, at their points of use.

### Common

- **Status.** The global criteria, the restricted interpolation algebra, the exact singular-support obstruction, the plane dichotomy, and the compact classification, finite matrix, Abel criterion and one-scale kernel are *proposed* new results in the stated frameworks. The literature checks of 21 September 2026 were targeted, not exhaustive; they do not certify priority. No named published conjecture is claimed solved. Not refereed, **no proof-assistant verification**, no Lean formalization of any statement.
- The proofs are support-controlled constructions, **not** convergence arguments in the fine surreal topology. No sequence of partial Hahn sums is asserted to converge there; no transfinite recursion is treated as a convergent fine-topological iteration.
- In a non-Archimedean ordered group, `nδ` need not eventually exceed every positive element; no proof relies on that false implication. Strong summability is not a valuation limit.
- No ordinary sheaf cohomology is assigned to the proper class of all surcomplex points; everything is set-sized, including the construction in Cor 23.6.
- The symbolic checks (Appendix B) validate displayed finite examples only. **Rem B.1 records a defect in the shipped compact script**: it writes `verification_results.json` beside itself, and its check helper raises on the first nonzero residual while the JSON is written only after every check passes — so the results file can never structurally record a failure, and a failing run leaves the previous all-pass file in place. Nothing in the article depends on that file.

### Part I (base `ℂ`)

- On Berarducci–Mantova and Costin–Ehrlich: *we do not identify their function classes with the sheaf studied here*. On Ehrlich–Kaplan: *no novelty claim about merely defining a surcomplex exponential*. On Müller–Strohmaier: *similar terminology does not make the objects or the global support conditions identical*.
- *The present proofs do not apply Cartan's theorem to `ℋ_Γ` as though it were a coherent `𝒪`-module* — `ℋ_Γ` is not locally finitely generated over `𝒪` for `Γ ≠ 0` (§14.5).
- No global logarithm of an arbitrary ordinary holomorphic unit is selected; only the positive-support factor is logarithmized canonically.
- Reduction is **not** asserted on the full ring `ℋ_Γ`; positive monomials are units there, so reduction is performed on the `ℋ_{Γ,≥0}` integral model.
- The sheaf property does **not** say arbitrary local sections glue after solving a correction problem.
- The line-bundle work over the plane is a vanishing/nonvanishing dichotomy plus a large explicit subspace plus an exact dimension for countable noncyclic `Γ`. It is **not** a computation of every element of `H¹(ℂ, ℋ_{Γ,+})`; the injections are not claimed surjective; no canonical basis or normal form is supplied. The exact Cousin criterion is for the displayed puncture-and-disk cover only.
- Cor 9.3 does not claim that `F` is irreducible or that the global ring has any unique-factorization property. Cor 13.5's local-invisibility statement is about those particular classes only.
- "Entire" means every coefficient is ordinary entire and evaluation is defined on `ℂ^♯` — not coherence at every surreal scale.

### Part II (base compact `X`)

- **The compact theorems are not statements about the plane** and must not be specialized by setting `X = ℂ`, `g = 0` (Rem 17.8). Compactness is used twice: finite-dimensional ordinary harmonic spaces, and one global well-ordered support bound for smooth Hahn forms.
- **Cohomology in the nonzero-valuation sector is not computed** (Rem 18.4). The positive perturbation argument does not apply there — no global ordinary bundle and no global scalar positive gauge in the required form — so the proved vanishing `H⁰(X, L) = 0` determines **neither `H¹` nor an Euler characteristic** in that sector. Part I has no analogous gap.
- The Abel theorem covers **finite polynomial cluster Cartier data only**. It is not asserted that every section of `𝒟_Γ` has such a presentation, nor that an arbitrary meromorphic-coefficient Hahn series has a classical finite zero count.
- Divisibility of `Γ` is what would license the root interpretation of a cluster (and makes `K_Γ` algebraically closed). The theorems are stated root-free to avoid it; **without divisibility the root picture is simply unavailable**.
- **No comparison functor** is constructed to an algebraic curve over `K_Γ`, or to a rigid-analytic, Berkovich or logarithmic Picard functor. The valuation-monodromy examples already rule out the most naive degree- and section-preserving comparison. The existence of a monodromy obstruction is *not* claimed as a new general idea — logarithmic Picard theory and its tropicalization are cited and distinguished.
- The objects are **not** compact subsets of the fine surcomplex plane; no fine-topological convergence, and **no general surreal version of Hodge theory or Serre duality** is proved or assumed. The finite matrix is a two-term instance of classical homological perturbation, credited, not discovered here.
- **No uniform decision procedure** is asserted for unrestricted surcomplex symbolic inputs; only each *fixed* Hahn coefficient is a finite computation.
- Manuscript C does not assume, and does **not verify**, this repository's own unrefereed claims — it names the principal-ideal stalk theorem specifically — and does not claim that every source manuscript or Lean file was individually audited.
- The genus-two obstruction is exhibited via its leading coefficients: the displayed series are proved, but **only the first few coefficients were symbolically confirmed** by the shipped script.
- Thm 23.3 computes an inverse limit of *isomorphism classes of line bundles* in the stated integral quotient sheaves. It does not replace them by bundles over any fine surcomplex topology, and the source Picard group is given no complete Hausdorff topology a priori.

## Build result

`latexmk -pdf -interaction=nonstopmode article.tex` then `latexmk -c`, run in this directory: **69 pages, 0 errors, 0 warnings, 0 undefined references, 0 undefined citations, 0 multiply-defined labels, 0 duplicate destinations.** Three overfull `\hbox` warnings predate this merge and are cosmetic.
