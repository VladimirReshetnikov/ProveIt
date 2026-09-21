# Global Support Obstructions: Moving Divisors, Mittag–Leffler, and a Picard Dichotomy

`article.tex` / `article.pdf` — one merged research article, 41 pages, 53 numbered results, self-contained LaTeX with an internal bibliography. Build with

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

## What the report is

A local-to-global theory for the sheaf `ℋ_Γ` of well-ordered Hahn series whose coefficients are ordinary holomorphic functions on a **common** ordinary domain, over a fixed set-sized surreal value group `Γ ⊆ No`, together with its nonnegative-support subring sheaf `ℋ_{Γ,≥0}` and its positive-support additive subsheaf `ℋ_{Γ,+}`. The question throughout is when infinitely many individually legitimate infinitesimal prescriptions admit one coherent global realization over the ordinary complex plane.

The headline results:

- **Sharp moving-divisor criterion** (Thm 8.2). A cluster family `P_c(u) = u^{m_c} + Σ_{j<m_c} a_{c,j} u^j`, `a_{c,j} ∈ 𝔪_Γ`, over a closed discrete ordinary `A ⊂ ℂ` is the exact zero divisor of a nonzero `F ∈ ℋ_Γ(ℂ)` **iff** the *symmetric support* `E(P) = ⋃_c ⋃_j supp(a_{c,j})` is well ordered — the supports of the symmetric coefficients, not of separately chosen roots. When it holds, any prescribed ordinary entire `f_0` with the right ordinary divisor can be kept as the exponent-zero coefficient, with support in `E(P)*`.
- **The two discriminating examples.** `n + t^{1/n}` alone is not realizable (descending symmetric support `{1/n}`); *all* roots of `(z−n)^n = t` are, with symmetric support the singleton `{1}`. Hence a globally principal effective divisor can have a nonprincipal effective sub-divisor.
- **Mittag–Leffler**, at the ordinary centres (Thm 7.2: solvable iff the union of principal-part supports is well ordered) and for **moving poles** relative to an admissible bound (Thm 11.1).
- **Support-restricted Chinese remainder theory** (§10): the correct target of global interpolation is the restricted product `𝔅(P)` of the `K_Γ[u]/(P_c)`, with an explicit Neumann right inverse, and `ℋ_Γ(ℂ)/(G) ≅ 𝔅(P)`.
- **Exact Cousin criterion** (Thm 13.1) on the puncture-and-disk cover, in terms of the *singular support* `Σ(b)`: only exponents carrying nonremovable ordinary coefficient singularities count.
- **PID stalks and the Picard dichotomy** (Thm 6.1, Thm 14.3, Thm 14.4): every ordinary-base stalk is a principal ideal domain though nonlocal, so tensor-invertible = locally free rank one here; `Pic(ℂ, ℋ_Γ) = 0` iff `Γ = {0}` or `Γ = Zδ`; otherwise `dim_ℂ Pic ≥ 2^ℵ₀`, with equality for countable noncyclic `Γ`, so `dim_ℂ Pic(ℂ, ℋ_ℚ) = 2^ℵ₀`.

## Which archives it came from

Sources are in `sources/`:

| file | manuscript |
| --- | --- |
| `09-moving-divisors-picard-dichotomy.tex` | **Manuscript A**, "Global Support Obstructions in Surcomplex Analysis: Moving Divisors, Mittag–Leffler Theory, and a Picard-Group Dichotomy" (archive `surcomplex_global_support`) |
| `10-cohomological-obstructions.tex` | **Manuscript B**, "Global Divisors and Cohomological Obstructions in Hahn-Coherent Surcomplex Analysis" (archive `surcomplex_global_theorems`) |

Both are continuations of the supplied `surcomplex_analysis(3).tex`, 21 September 2026, from which the Hahn-coherent framework, evaluation, support-preserving gluing, local preparation, division, root lifting and pole-free fractions are inherited and credited rather than claimed.

Overlap is high: both prove the same sharp divisor criterion, use the same pair of discriminating examples, prove the matching principal-parts criterion, derive the same line-bundle dichotomy, use the same classical inputs (Weierstrass products, Mittag–Leffler, `H¹(ℂ,𝒪) = 0`), and both insist that Cartan's theorem is not being applied to a sheaf that is not a coherent `𝒪`-module and that this category is not Müller–Strohmaier's. The shared core is printed once, in Manuscript A's version.

### What each contributed

**Manuscript A** (the base — it proves strictly more at both points where the two differ):

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

### The conflict, and how it is resolved

The two diverge on whether the dichotomy holds for **all tensor-invertible modules** or only for **locally free rank-one sheaves**, and on how large the group is. Both agree the stalks of `ℋ_Γ` are not local for `Γ ≠ 0`. A proves the PID stalk theorem, deduces tensor-invertible ⇒ rank-one locally free, and states the dichotomy for the unrestricted `Pic`; B explicitly refuses that substitution ("We do not silently substitute the larger category of all tensor-invertible modules on an arbitrary ringed space"), restricts to `Pic_lf`, and claims only that the group *contains* a copy of `ℂ^ℕ/ℂ^(ℕ)`.

The merge does not average this. Thm 6.1 is printed with its proof; Rem 6.4 states that this theorem is exactly what licenses dropping the "locally free" qualification, keeps B's distinction and its Stacks Tag 09NT citation as the statement of what is at stake, and records that every Picard statement specializes verbatim to `Pic_lf` and to `Pic(ℂ, ℋ_{Γ,≥0})` for a reader who declines it. Rem 14.5 does the same for the size: A's exact dimension with its countability hypothesis is printed, and B's weaker containment is kept as what survives without the stalk theorem, with a note on which is sharper for which purpose.

## Ring discipline

Every numbered statement is over **one** coefficient ring family and says so: `ℋ_Γ(U) = 𝒪(U)((t^Γ))`, whose Hahn coefficients are ordinary holomorphic on the **common** domain `U`, together with its subsheaves `ℋ_{Γ,≥0}`, `ℋ_{Γ,+}`. Two rings inside that family are named apart where it matters — the fixed-disk ring `𝒪(D)((t^Γ))`, where preparation and division happen, and the ordinary-base stalk `R_c`, a filtered colimit of those, of which the PID theorem speaks. `𝒪(D)((t^Γ))` for fixed `D` is *not* claimed to be a PID. Nothing is stated over, or transported to or from, a radius-free ring `ℂ{z}((t^Γ))` of individually convergent coefficient germs with no common domain, or a formal ring `ℂ[[z]]((t^Γ))`; the common-domain hypothesis is load-bearing in the sheaf property, in the "no disk shrinking" clause of the divisor recursion, and in the uniform support bound of local preparation. §1.2 states this; Appendix D tabulates the symbols.

## Notation

One symbol per concept, fixed in §1.2. `ℋ_Γ, ℋ_{Γ,≥0}, ℋ_{Γ,+}`; `𝔪_Γ` for the infinitesimals of `K_Γ` and `𝔪_SC` for those of `SC`; `Exp_H`/`Log_H` for the positive-support exponential and logarithm, kept apart from the ordinary `e^h`; `E(P)` for the symmetric support (Manuscript A writes `S_𝒟`); `ℛ_P` for the deformed remainder map; `Σ(b)` for the singular support; `𝒱_Γ/𝒲_Γ` for the obstruction quotient. The exponent-zero coefficient map `ℋ_{Γ,≥0} → 𝒪` is called the **reduction** throughout; the sources and the literature also call it the residue map, the standard part and the shadow — noted once, then unused. All `\label`s are prefixed `global:`.

## What is not proved

Preserved from both manuscripts, at their points of use:

- **Status.** The global criteria, the restricted interpolation algebra, the exact singular-support obstruction and the dichotomy are *proposed* new results in the framework of the supplied manuscript. The literature check of 21 September 2026 was targeted, not exhaustive; it does not certify priority. No named published conjecture is claimed solved. Not refereed, not machine checked.
- The proofs are support-controlled constructions, **not** convergence arguments in the fine surreal topology. No sequence of partial Hahn sums is asserted to converge there; no ordinary partial sums are claimed to converge in the full fine topology; no transfinite recursion is treated as a convergent fine-topological iteration.
- On Berarducci–Mantova and Costin–Ehrlich: *we do not identify their function classes with the sheaf studied here*. On Ehrlich–Kaplan: *no novelty claim about merely defining a surcomplex exponential; no global exponential construction claimed as a contribution*. On Müller–Strohmaier: *similar terminology does not make the objects or the global support conditions identical; no equivalence of the two categories is assumed*.
- *The present proofs do not apply Cartan's theorem to `ℋ_Γ` as though it were a coherent `𝒪`-module* — `ℋ_Γ` is not locally finitely generated over `𝒪` for `Γ ≠ 0` (§14.5).
- No global logarithm of an arbitrary ordinary holomorphic unit is selected; that factor stays in `𝒪^×`, and only the positive-support factor is logarithmized canonically. The Hahn logarithm is a logarithm of a positive-exponent perturbation of one — nothing to do with a global branch of the ordinary logarithm or a surcomplex exponential at infinite imaginary arguments.
- Reduction is **not** asserted on the full ring `ℋ_Γ`; positive monomials are units there, so reduction is performed on the `ℋ_{Γ,≥0}` integral model.
- The sheaf property does **not** say arbitrary local sections glue after solving a correction problem: the corrections themselves may fail to have a common admissible support.
- No contradiction with the fine-germ ring at a *single* surcomplex point in the supplied manuscript: the two stalk constructions use different neighbourhoods.
- In a non-Archimedean ordered group, `nδ` need not eventually exceed every positive element; no proof relies on that false implication. Strong summability is not a valuation limit.
- The ordinary interpolation tools are classical, not results of this article.
- The line-bundle work is a vanishing/nonvanishing dichotomy plus a large explicit subspace plus an exact dimension for countable noncyclic `Γ`. It is **not** a computation of every element of `H¹(ℂ, ℋ_{Γ,+})`, the injections are not claimed surjective, and no canonical basis or normal form is supplied. The exact Cousin criterion is for the displayed puncture-and-disk cover only; no criterion for arbitrary covers is established.
- Cor 9.3 does not claim that `F` is irreducible, that every factorization fails, or that the global ring has any unique-factorization property.
- Cor 13.5's local-invisibility statement is about those particular classes; it does not assert vanishing of the sheaf cohomology of every bounded disk for arbitrary data.
- No ordinary sheaf cohomology is assigned to the proper class of all surcomplex points; everything is set-sized. "Entire" means every coefficient is ordinary entire and evaluation is defined on `ℂ^♯` — not coherence at every surreal scale, and the results neither contradict nor weaken the supplied manuscript's all-scale polynomial rigidity.
- The symbolic checks (Appendix B) validate displayed finite examples. No finite computation establishes the nonexistence of a well ordering for an infinite descending sequence, the Picard dimension, the universality of the dichotomy, or an arbitrary-support transfinite recursion. Not a proof assistant, not a novelty checker.

## Build result

`latexmk -pdf -interaction=nonstopmode article.tex` then `latexmk -c`, run in this directory: **41 pages, 0 errors, 0 undefined references, 0 duplicate destinations.**
