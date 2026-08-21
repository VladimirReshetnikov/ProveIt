Replacing ℤ by **ℚ changes nothing** — the conclusion is still x ∈ ℤ, and in fact the rational form is the *original* theorem (it's what Siegel communicated to Alaoglu and Erdős, and what the published six exponentials theorem of Lang and Ramachandra later covered). Replacing ℤ by **𝔸 weakens the conclusion to exactly x ∈ ℚ**, and that is sharp: the solution set becomes precisely ℚ. The reason both answers are clean is that the three-base theorem decomposes into two fully decoupled mechanisms, only one of which ever sees the difference between ℤ, ℚ, and 𝔸.

## Mechanism 1: transcendence (sees only "algebraic or not")

Suppose 2^x, 3^x, 5^x ∈ 𝔸 and x ∉ ℚ. Then {1, x} is ℚ-linearly independent, {log 2, log 3, log 5} is ℚ-linearly independent (unique factorization), and the six products of the two lists exponentiate to

$$2,\; 3,\; 5,\; 2^x,\; 3^x,\; 5^x,$$

all algebraic — contradicting the six exponentials theorem. Hence

$$2^x, 3^x, 5^x \in \mathbb{A} \;\Longrightarrow\; x \in \mathbb{Q}.$$

This step is blind to integrality: it uses only algebraicity of the values. (This is why your report is right to call the six exponentials theorem the entire transcendence content of the three-base theorem.)

## Mechanism 2: descent from ℚ to ℤ (elementary, one base suffices)

If additionally the values are *rational*, write x = p/q in lowest terms. Then 2^{p/q} ∈ ℚ is a rational root of the monic polynomial X^q − 2^p (for p < 0 pass to 2^{−x} = 1/2^x), hence an integer m, and comparing 2-adic valuations in 2^p = m^q gives p = q·v₂(m), so q ∣ p, so q = 1. One rational value of one base kills the denominator. So

$$2^x, 3^x, 5^x \in \mathbb{Q} \;\Longrightarrow\; x \in \mathbb{Z},$$

and the same holds for values in any subring of ℚ (S-integers, ℤ[1/6], …): the dividing line is simply whether the value ring sits inside ℚ or contains irrational algebraics. A small aesthetic bonus of the ℚ form: its solution set is exactly ℤ (negative x included, 2^{−3} = 1/8 ∈ ℚ), restoring the x ↔ −x symmetry that the ℤ form breaks by truncating to ℕ₀.

## Sharpness of the 𝔸 version, and the interpolation between 𝔸 and ℚ

Every rational x = p/q genuinely occurs: 2^{p/q}, 3^{p/q}, 5^{p/q} are algebraic, each of degree *exactly* q (X^q − 2^p is irreducible for gcd(p, q) = 1 by Capelli, since 2^p is no ℓ-th power for ℓ ∣ q and is positive). So the 𝔸-antecedent solution set is exactly ℚ — no strengthening of six exponentials can improve the conclusion. The degree computation also gives the graded refinement: "2^x, 3^x, 5^x algebraic of degree ≤ d" forces x ∈ ℚ with denominator ≤ d. Your kernel-verified RadicalDegree statement is the two-base conditional shadow of exactly this.

One caveat worth recording, because it localizes where primality is used: Mechanism 1 only needs the three bases multiplicatively independent, but Mechanism 2 needs at least one base that is not a perfect power. With bases 4, 9, 25 (multiplicatively independent!) the point x = 1/2 satisfies 4^x = 2, 9^x = 3, 25^x = 5 ∈ ℤ. The exact statement for general multiplicatively independent integer bases is: values in ℚ force x ∈ ℚ with denominator q such that every base is a perfect q-th power. This is precisely the phenomenon your power-primitive normalization exists to quotient away.

## The same replacement in *your* two-base problem

This is where the question earns its keep. Running the antecedent ladder on the two-base conjecture gives three statements:

- **(𝔸₂)** 2^x, 3^x ∈ 𝔸 ⇒ x ∈ ℚ. This *is* the four exponentials instance in its cleanest clothing — the conclusion cannot be pushed past ℚ, for the same sharpness reason as above. (Its only unconditionally settled part is the parallel of your transcendence theorem: a counterexample x must be transcendental, since x algebraic irrational already contradicts Gelfond–Schneider at the single base 2.)
- **(ℚ₂)** 2^x, 3^x ∈ ℚ ⇒ x ∈ ℤ. This is the conjecture *as Alaoglu and Erdős actually posed it* — "simultaneous rational powers" — and it is the form the colossally abundant application (your Priority J) consumes.
- **(ℤ₂)** your program's form.

The implications 𝔸₂ ⇒ ℚ₂ ⇒ ℤ₂ hold (the first via Mechanism 2, the second trivially), and I'd flag one exact statement of the gap in the middle: **ℚ₂ is equivalent to ℤ₂ plus a denominator-support lemma.** If 2^x = a/b, 3^x = c/d in lowest terms and one knew b is a power of 2 and d a power of 3, then y = x + s for large s has 2^y = 2^s a/b ∈ ℤ and 3^y = 3^s c/d ∈ ℤ with y nonintegral iff x is — collapsing ℚ₂ into ℤ₂. Absent that support lemma, no reduction in either direction is known, and it is the same flavor of statement as your kernel-verified RationalThirdBase gateway ("rational with denominator supported by the known outputs"), so your ThreeDenominatorNormalization / RationalPowerIndex modules already live in exactly this gap — worth checking whether they state the equivalence explicitly, since it would pin down ℚ₂'s precise cost.

A final caution if you ever consider attacking ℚ₂ directly: your strongest unconditional artifacts don't transfer as stated. The conditional structure theory survives in weakened form (valuation vectors move from the cone ℕ² to ℤ², rank ≤ 2 persists), but the |D| ≥ 1 mechanism underlying the whole determinant hierarchy degrades to |D| ≥ (denominator)^{−O(weight)} with an uncontrolled denominator, and the finite scans become height-stratified rather than value-bounded. Everything holds for complex x verbatim (principal powers; six exponentials is a ℂ-statement), and quantitative versions of Mechanism 1 exist via measures of linear independence in Waldschmidt's Grundlehren if you ever want an effective "how close to rational can all three powers simultaneously be" statement.

---

For the principal power function, complexifying the domain is completely free — every complex solution is automatically real, by an elementary argument whose only input is the irrationality of θ = log₂3 — so the conjecture, the three-base theorem, and all your variants are unchanged, and the "x ∈ ℝ" in the statement is cosmetic. But the question has real content once you look at the two places where that reduction does *not* apply: multivalued branches, and complexifying the *codomain*. I'll do all three, since the second and third produce statements your catalogue doesn't have.

First, the definition. For x ∈ ℂ, "2^x" needs a branch; the canonical reading (and the one Mathlib's `Complex.cpow` implements, with principal log — and Complex.log 2 = Real.log 2 since 2 > 0) is 2^x := exp(x ln 2), 3^x := exp(x ln 3) with the real logarithms. I take that reading as the default.

## 1. Principal branch: every complex solution is real

Write x = s + it. Then |2^x| = 2^s and arg(2^x) = t ln 2 mod 2π. If 2^x = m ∈ ℤ∖{0}, the modulus gives 2^s = |m| ∈ ℤ≥1 and the argument gives t ln 2 ∈ πℤ (argument 0 for m > 0, π for m < 0). Likewise 3^x ∈ ℤ gives 3^s ∈ ℤ≥1 and t ln 3 ∈ πℤ. If t ≠ 0, dividing t ln 3 = πb by t ln 2 = πa (and a = 0 forces t = 0 outright) yields θ = b/a ∈ ℚ — contradicting the elementary irrationality of θ. So t = 0, x = s is real (and then m > 0, s ≥ 0 automatically, matching your ℕ₀ normalization).

Geometrically: {x : 2^x ∈ ℤ} and {x : 3^x ∈ ℤ} live on families of horizontal lines Im x ∈ (π/ln 2)ℤ and Im x ∈ (π/ln 3)ℤ, and the two gratings have **incommensurable spacings** — incommensurable *precisely because* θ is irrational — so they intersect only on the real axis. Note what carried the load: the modulus condition on Re x reproduces the original real hypothesis exactly, and the argument condition on Im x dies on unique factorization. The identical argument runs for the ℚ-antecedent (rational values are real, so arguments still lie in {0, π}), so:

$$x \in \mathbb{C},\ 2^x, 3^x \in \mathbb{Z} \text{ (or } \mathbb{Q}\text{)} \quad\Longleftrightarrow\quad x \in \mathbb{R},\ 2^x, 3^x \in \mathbb{Z} \text{ (or } \mathbb{Q}\text{)},$$

and the same for three bases. Formalization remark: this is a ~20-line lemma over `Complex.cpow` on top of your existing irrationality of θ, and it permanently inoculates the repository against the ℂ question — the headline conjecture can be *stated* over ℂ at zero mathematical cost. Cheap, catalogue-worthy (Cluster A).

## 2. The 𝔸 antecedent over ℂ: a clean splitting principle

Here the reduction to ℝ genuinely fails elementarily — algebraic values need not have argument in {0, π} — but something better is true. Since 𝔸 is closed under complex conjugation and division, z ∈ 𝔸∖{0} gives |z| = √(z·z̄) ∈ 𝔸. So if 2^x, 3^x ∈ 𝔸 with x = s + it, then 2^s = |2^x| and 3^s = |3^x| are (positive real) algebraic, and 2^{it} = 2^x/2^s, 3^{it} = 3^x/3^s are algebraic of modulus one. Conversely the factors multiply back. Hence the complex solution set **splits as a direct sum**:

$$\{x \in \mathbb{C} : 2^x, 3^x \in \mathbb{A}\} \;=\; \{s \in \mathbb{R} : 2^s, 3^s \in \mathbb{A}\} \;+\; i\,\{t \in \mathbb{R} : 2^{it}, 3^{it} \in \mathbb{A}\}.$$

The real slice is your (𝔸₂) from last time; the imaginary slice is the **unit-circle problem**: does t ≠ 0 exist with 2^{it}, 3^{it} both algebraic? Both slices are four-exponentials instances — genuinely *different* instances of the same conjecture (rows {1, s} vs. {1, it}, same columns {ln 2, ln 3}) — so the complex two-base 𝔸-problem is exactly *two* decoupled 4EC instances, and under 4EC the conclusion is still x ∈ ℚ, still sharp. For three bases, everything closes unconditionally: six exponentials is already a theorem over ℂ, the real slice gives s ∈ ℚ as before, and the imaginary slice is the textbook six-exponentials corollary that 2^{it}, 3^{it}, 5^{it} cannot all be algebraic for real t ≠ 0. So the three-base 𝔸-solution set over ℂ is *exactly* ℚ — complexification adds nothing. One unconditional crumb for two bases: nonreal *algebraic* x are excluded, since Gelfond–Schneider holds for complex algebraic irrational exponents (2^x is then transcendental); so your "every counterexample is transcendental" theorem extends to ℂ verbatim.

## 3. Multivalued branches: the only reading with conceivable nonreal solutions — and it adjoins the prime −1

Suppose we only demand that *some* determination of 2^x and some determination of 3^x be integers: e^{xL₂} = m, e^{xL₃} = m′ with L₂ = ln 2 + 2πiJ, L₃ = ln 3 + 2πiK. Writing xL₂ = ln|m| + iπa, xL₃ = ln|m′| + iπb and eliminating x, the imaginary part gives a ℤ-linear log relation, hence by unique factorization the multiplicative constraint |m|^{2K} 3^a = |m′|^{2J} 2^b, while the real part gives

$$\ln|m|\ln 3 \;-\; \ln|m'|\ln 2 \;=\; 2\pi^2\,(aK - bJ).$$

Two regimes. If aK − bJ = 0, the left side vanishes, which is exactly your log-product wall: either |m| = |m′| = 1 (then x = 0 by a two-line check) or (|m|, |m′|) is a *real* counterexample pair (2^σ, 3^σ) — and if the real conjecture holds, a short computation with the imaginary-part relation forces x = n ∈ ℤ with the branch phases trivializing. If aK − bJ ≠ 0, one needs the log-product form to equal a nonzero integer multiple of 2π². Since iπ = log(−1), this is precisely your linear-form-in-log-products wall over the prime set **extended by the "prime" −1**: the bilinear lattice gains the directions π² = −(log(−1))² and iπ·ln p. Your Section-on-log-products independence criterion, extended to this lattice, covers the multivalued complex conjecture too, and it remains a Schanuel consequence (algebraic independence of π, ln 2, ln 3, … kills all such relations). And the four exponentials conjecture masters this reading wholesale, because the branch logs L₂, L₃ stay ℚ-independent (their real parts already are): 4EC ⇒ x ∈ ℚ, and then the modulus argument on 2^{p/q}ζ ∈ ℤ forces q | p, so x ∈ ℤ with all phases equal to 1. Conjectural answer unchanged; only the wall widens.

## 4. The dual move — complexifying the codomain — is where new content lives

Since the domain extension is free, the honest locus of "what does ℂ buy" is values in ℤ[i] rather than ℤ. Claim: **the Gaussian-integer version is equivalent to the original conjecture.** One direction is trivial (ℤ ⊂ ℤ[i]). For the other, assume the real conjecture and let 2^x, 3^x ∈ ℤ[i], x = s + it. Taking norms: N(2^x) = 2^{2s} and N(3^x) = 3^{2s} are positive integers — the real hypothesis at exponent 2s — so 2s ∈ ℤ. Now 3^{2s} is genuinely a power of 3, and **3 is inert in ℤ[i]**, so 3^x = i^j·3^k with 9^k = 3^{2s}, forcing s = k ∈ ℤ: the inert prime upgrades the half-integer ambiguity to integrality for free. Then 2^{2s} = 4^s means 2^x is divisible only by the ramified prime (1+i), so 2^x = u·(1+i)^{2s} = 2^s·i^s u — in both bases the values are 2^s and 3^s times **fourth roots of unity** (the only unit-modulus Gaussian integers). The argument gratings become t ln 2, t ln 3 ∈ (π/2)ℤ, and irrationality of θ kills t again. So x = s ∈ ℤ exactly, no new solutions: a self-contained equivalence, and a nice low-cost kernel target (Gaussian factorization + your θ-irrationality module + the real conjecture as hypothesis) for the status matrix.

Two boundary markers so the picture is sharp. Replace ℤ[i] by ℚ(i) and the reduction breaks at exactly one point: unit-modulus elements of ℚ(i) are not just roots of unity ((3+4i)/5), so the imaginary slice reopens as a genuine unit-circle 4EC instance — integrality-up-to-units, not rationality, is what closes the argument direction. And replace ℤ[i] by the integers of another imaginary quadratic field in which 2 or 3 *splits* (e.g. ℚ(√−2), where 3 splits and 1+√−2 has modulus √3): then values like (1+√−2)^{2s} are not roots of unity times 3^s, the argument condition involves arctan √2, and eliminating t produces relations mixing θ·π with logs of complex algebraic numbers — the product-of-logs wall again, now with more rooms. I'd record the ℤ[i] equivalence and flag the split-prime variants as open, rather than pursue them; they hit the same wall with worse constants.

## Summary table for the catalogue

Domain ℝ→ℂ, principal branch, values in ℤ or ℚ: **equivalent to the original** (elementary; θ irrational). Values in 𝔸: splits into real ⊕ unit-circle slices; three-base solution set still exactly ℚ (theorem); two-base = two decoupled 4EC instances, conclusion under 4EC still ℚ, counterexamples still transcendental (GS over ℂ). Multivalued branches: conjecturally still x ∈ ℤ (4EC suffices); unconditionally governed by your log-product lattice extended by log(−1) = iπ. Values in ℤ[i]: **unconditionally equivalent** to the original, via norms plus inertness of 3. In every reading, the answer the conjecture *predicts* never changes; what changes is only which wall stands guard.