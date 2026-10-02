# Mathematical review of the integrated fixed arity Airy report

Date: 2 October 2026

## Verdict and exact scope

**Approved for every fixed integer k ≥ 3 and every fixed finite expansion order.** The integrated article faithfully combines the reviewed relaxed leading-amplitude argument, the all-orders polynomial–Airy construction, and the compacted/DFA finite-memory extension. Its normalization constants, first two count corrections, first model-dependent ratio terms, cancellation coefficient, and inverse-count formulas are consistent. No unresolved mathematical issue was found.

This verdict applies to `fixed-arity-airy-expansions.tex` with SHA-256

`897d48808a501dd1d72dc781df7e2a9697ce95f18e108c6be32b390ba5ef0a38`.

The conclusion is a Poincaré expansion with a separately controlled remainder at every fixed order and a single positive amplitude per model. It does not establish convergence of the infinite series, an exponentially completed transseries, explicit amplitude values, or uniformity as k grows. This is a mathematical consistency and proof review, not a claim of publication or literature novelty.

## Source correspondence and exact initialization

The recurrences and endpoint conversion agree with [Dastidar–Wallner, Asymptotics of relaxed k-ary trees](https://arxiv.org/html/2404.08415v1), Propositions 7, 10, and 11 and equations (3)–(5). The article correctly distinguishes the published relaxed Θ theorem from its additional equivalence and finite-order conclusions. The published lower bound is used only to exclude a zero relaxed amplitude after existence of the limit has been established.

For q = k−1, the transform is dᵢ(j) = q²ˣa(x,m)/x!, with i = x+m and j = x−qm. Thus Rₙ = (qn)!q⁻²ᑫⁿdₖₙ(0). The DFA normalization uses a(x,m) = b(x,m)/2ᵐ. Its exceptional source b(−1,0) = 1 is stated explicitly rather than silently inferred from the ordinary nonnegative base row. It gives b(q,1) = 1 and b(x,1) = 2^(x−q+1)−1. At time k the normalized DFA bottom seed is q²ᑫ/(2q!), exactly half the relaxed and compacted seed. The auxiliary negative coordinate never receives a factorial transform.

At time i ≥ k+1, X ≥ k on every physical site, so the delayed falling factorial is nonzero. The delayed predecessor is (i−k−1,j−1), and its coefficient is δₘq²ᵏ/(X)ₖ, with δₘ = m−1 or m/2. Setting δ₀ = 0 correctly excludes a source recurrence outside its domain.

The indexing was independently checked against the current OEIS entries. [A082162](https://oeis.org/A082162) starts at index 1 with 1, 7, 139, 5711; R₀ = 1 is an additional convention. [A102102](https://oeis.org/A102102) starts at index 0 with 1, 1, 15, 1000, 189035. [A128249](https://oeis.org/A128249) uses column index plus one as alphabet size, so the article's arity k is column k−1, read through the stated antidiagonal arrangement. These are relaxed counts, not minimal accepting-DFA counts.

## Leading scale and the first two corrections

With B = (2/q)^(1/3), λ = a₁/B, and β = (7k−6)/6, the transformed endpoint contributes i^(β−1/3). Stirling's conversion contributes n^((1−q)/2). Their sum is (2k−1)/3. The exponential conversion gives (kᵏ/qᑫ)ⁿ and the Airy exponent 3(kq/2)^(1/3)a₁n^(1/3). The normalized DFA contributes the separate factor 2ⁿ. These checks confirm every factor in the common scale and the factor two in ρ_B = 2A_B/A_R.

The scalar coefficients printed in the article give

h₁ = −3(σ₄/k−λ²/2) = λ²(3q²+27q+23)/(45q)

and

h₂ = (3/2)(λ/3−σ₅/k+λβ).

The endpoint has no relative ε term. Its relative ε² coefficient is e₂ = λ(6q²−51q+86)/(135q), so

h₂+e₂ = λ(4q³+321q²+429q+126)/(270q).

Consequently c₁ = k^(−1/3)h₁ and c₂ = k^(−2/3)(h₁²/2+h₂+e₂), exactly as stated. The ternary simplifications also agree. Stirling starts at ε³ and cannot alter these two coefficients.

## Analytic transfer and the signed extension

The integrated account retains the essential analytic safeguards: a positive fixed harmonic weight; the shifted positive variance form; localization before use of the terminal-edge identity; zero Dirichlet trace; compactness and min–max for singular values rather than a nonnormal eigenvalue assertion; exact bottom cancellation for the weighted adjoint; phase norms with three common coefficients; and the singular-overlap bound needed for the stable compression.

The renewal stopping-time argument correctly proves j+1 ≤ lⱼ ≤ j+q. The final article explicitly starts the profile and scalar-product construction at a sufficiently large fixed time, avoiding any unintended positivity assertion for early scalar factors.

The all-orders argument preserves a fixed amplitude gauge, exact bottom zeros, and an absolute polynomial–Airy remainder envelope. Its high-order approximate solutions are normalized to the same central limit. Backward summation from the established zero central limit is therefore legitimate; the norm-to-endpoint loss is paid for by choosing an arbitrarily high finite residual order.

For the signed extension, completed-run factors yield positive infinite-product lower comparisons for q ≥ 2. The global delayed norm bound is O(i⁻ᑫ), including sites outside the Airy window. The finite-memory bootstrap uses scalar norm inequalities and does not presume positivity of the signed propagator. Its additional terms are summable or absorbable in the stable decrement. The argument therefore establishes the stated positive amplitudes and all finite orders for both additional models.

## Ratios, monotonicity, and cancellation

The delay begins at ε^(3q). Its first pure-f contribution shifts the scalar by −qᵏ/k for compacted trees and half that for normalized DFAs. Scalar summation and i = kn give the logarithmic defects

(q/k)ᵏ/(k−2) and (q/k)ᵏ/[2(k−2)]

at n^(−(k−2)). Thus the first two count coefficients are common to all three models. Eventual strict decrease is justified by taking enough finite terms that the remainder is o(n^(−(k−1))) before subtracting consecutive values. No derivative of an uncontrolled remainder or all-n monotonicity is asserted.

The cancellation subsection is consistent with its separately approved proof. With d = 3q, the first individual profile change is delayed to ε^(d−1); nonlinear terms in the recurrence begin no earlier than 2d−1 > d+3, including k = 3. The exact difference of delay coefficients is −q²ᵏ/(X)ₖ. After the k inverse scalar factors this gives combined scalar coefficient +qᵏ at ε^(d+3), combined h_d = −q^(k−1)/k, and endpoint coefficient

−qᑫ/kᵏ at n⁻ᑫ.

Combined endpoint logarithms cannot alter this coefficient. The displayed values −4/27 and −27/256 follow. The inherited finite-order theorem supplies the stated O(n^(−q−1/3)) remainder with the same amplitudes.

## Inversion and integer thresholds

Writing the logarithm as

qn log n + (log A−q)n + γn^(1/3) + ν log n + d + O(n^(−1/3)),

gives ν = (7k−5)/6 and d = log C+(q/2)log(2π). The positive principal Lambert branch solves the leading equation exactly:

w = W₀(A^(1/q)L/(qe)), n₀ = L/(qw), D = q(w+1).

The first displacement is −[γn₀^(1/3)+ν log n₀+d]/D. Taylor substitution leaves O(n₀^(−1/3)) logarithmic residual, so division by slopes asymptotic to q log n₀ yields the claimed o(1/log n₀) inverse error. The equivalent constant-displacement form uses the identity D = q log n₀+log A and is algebraically correct.

For arbitrary finite accuracy, interpolation of integer values of a sufficiently long logarithmic truncation preserves the proven count error; inversion divides it by order log n. Smooth inversion alone needs the lattice correction. A convex logarithmic graph has chord excess H″(z)θ(1−θ)/2, so its inverse correction is negative, namely −qθ(1−θ)/(2zH′(z)) to first order. The sign and scale printed in the article are correct.

For large y the exact threshold is the ceiling of the exact log-linear inverse. A finite approximate inverse is not safe to round when its uncertainty reaches an integer. The article states this necessary qualification and does not turn an asymptotic estimate into an unjustified exact threshold algorithm. Numerical evaluation would additionally require certified amplitude and remainder information.

## Reproducibility and limits of finite checks

The review read the prior analytic, all-orders, signed-extension, and cancellation audits and compared the integrated arguments against their exact approved source versions. It also independently checked the integrated scalar-to-count algebra and inverse formulas. Replays completed successfully:

- 2,095 exact fixed-weight phase/form checks
- 11,016 independent source/run, signed-transform, scaled-delay, ratio, and published-table checks
- Symbolic general-q recurrence verification through ε⁵, including unique bottom/gauge solutions and c₁/c₂

These computations corroborate constants and indexing; the compactness, tracking, and all-finite-orders conclusions rest on the analytic arguments. The reviewed document contains no outstanding correction needed within its stated fixed-k, finite-order scope.
