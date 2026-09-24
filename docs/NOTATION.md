# Notation and conventions across the reports

Use this guide when moving between the main reports listed in
[the canonical inventory](FORMALIZATION.md#canonical-report-inventory).
It translates their local notation and recommends common names for new text.
It does not identify objects merely because they share a symbol, or transfer
a theorem between coefficient rings, topologies, or derivative notions.
Merged reports record source notation in their reconciliation and provenance
material. Original manuscripts are not distributed in the current tree;
previously tracked archives remain available in repository history.

## Scalars, workspaces, and size

| Object | Recommended notation | Existing local conventions |
|---|---|---|
| Ordinary fields | `ℝ`, `ℂ` | These are the coefficient fields, with their ordinary analysis. |
| Surreal and surcomplex classes | `No`, `SC = No[i]` | The analysis report writes `K = No[i]`. Most other reports reserve `K` for a **set-sized** field. |
| Ordered exponent group | `Γ` | A set-sized ordered abelian group; divisibility, nontriviality, and an embedding in `No` must be stated where needed. |
| Real Hahn workspace | `F_Γ = ℝ((t^Γ))` | Analytic geometry and contours also use `R_Γ`; surquaternions uses `K_Γ` for this **real** field. |
| Complex Hahn workspace | `K_Γ = ℂ((t^Γ)) = F_Γ[i]` | `K` or `𝕂` after the workspace is fixed. In the rank-one report, `K = ℂ((t^ℝ))`. |
| Surquaternions | `SQ = ℍ_No` | The quaternion report uses `D_Γ = ℍ_{K_Γ}`, with its local real-field convention above. |

An abstract Hahn field needs no surreal embedding to be defined. Its
interpretation by Conway normal forms uses an ordered additive-group embedding in
`No`. A workspace contains the specified set of input numbers; it need not
be closed under a surreal exponential, a selected scalar derivation, or every
operation used later. An enlargement or closure hypothesis is additional data.
See [foundations](foundations-and-computation/foundations/article.tex)
(`found:thm:workspace`), [spectral theory](surcomplex/spectral-theory/article.tex)
(`eq:workspace`, `spec:rem:divisibility`), and
[surquaternions](surquaternions/surquaternions/article.tex)
(`squat:thm:localization`).

Supports, families being summed, covers, polynomial degrees, and matrix
sizes have their stated set or finite size restrictions. The whole surreal
class is not one such workspace. `∞` in a valuation is an added symbol with
`v(0) = ∞`, not a surreal number. Natural numbers are ordinary finite integers;
write `ℕ = {0,1,2,…}` and `n ≥ 1` where division by `n` is intended.

## Omnific integers and the constant coefficient

The [Diophantine report](surreal/omnific-diophantine-geometry/article.tex)
now writes `Oz = ℤ ⊕ Π`, agreeing with the foundations report. Its original
base used `A = Oz = ℤ ⊕ J`; below `J` denotes the same ideal. The
[set-sized quotient report](surreal/set-sized-quotients-of-omnific-integers/article.tex)
now also uses `Π` (its base used `I`) for the infinite-part ideal. The decomposition is additive, not a
product of unital rings. In growth notation `ω^γ`, every exponent of `Oz`
is nonnegative and the coefficient at zero is an ordinary integer.
`J` consists of the forms with strictly positive support, including zero.
Its nonzero elements can have either sign. In `t^γ = ω^(−γ)` notation these
conditions become nonpositive and strictly negative support, respectively.
They constrain **every** exponent, not only the leading exponent.

For a general coefficient field `k`, multiplication by any nonzero scalar
preserves `Π_k` bijectively. The formula `nΠ_k = Π_k` therefore requires
the integer `n` to have nonzero image in `k`; in characteristic `p`,
`pΠ_k = 0`. The quotient report's notation `a ≪ c` compares positive
exponents: `na < c` for every ordinary positive integer `n`. These integer
multiples are taken in the ordered exponent group, independently of the
characteristic of the coefficient field. They do not say that `X^a` is small.

Constant coefficient `ct` is a ring retraction on these support-restricted
rings. It is not a ring homomorphism on all of `No`, since `ω · ω⁻¹ = 1`,
and it is not order preserving: `ω − 1 > 0` but `ct(ω − 1) = −1`.
The ring of finite surreals has the opposite growth-support condition;
its standard-part homomorphism has a different domain and an infinitesimal
kernel. The omnific counterexample `X² − X − ω` has two simple roots modulo
`Π` and no omnific root. Its infinite coefficient `−ω` excludes it from
finite-surreal residue lifting; it does not contradict that theorem. In the complex
nonnegative-growth subring, the constant-coefficient kernel is `J + iJ`.
For a nonzero form, growth degree is the largest supported exponent and
satisfies `v = −deg` under the reversed valuation convention.

For an automorphism `σ` of `Oz`, preservation of constant coefficient means
`ct ∘ σ = ct`. A claim that it fixes `ℝ` refers to its extension to `No`:
the ordinary reals contained in `Oz` are only `ℤ`. In the omnific-automorphism
factorization `M_{χ,τ} ∘ u`, apply `u` first, then the monomial map `M_{χ,τ}`.

In the curve part of the Diophantine report, `𝒜_k(Γ)` has nonnegative
growth support, while the valuation ring `𝒪_k(Γ)` has nonpositive growth
support. For `Γ = 0` both are the coefficient field; the assertion that
`𝒜_k(Γ)` is not a valuation ring requires `Γ ≠ 0`. An Euler derivation
sends these rings into their strictly positive and strictly negative
support ideals, respectively. This concerns the exponents of the image;
it does not assert a proper inclusion of the image in either ideal.
For example, on `k[ω]` with `∂(ωⁿ) = nωⁿ` in characteristic zero,
the image is exactly `ω k[ω]`. For any nonzero Hahn series `u`,
`ct(∂_λ u/u) = λ(deg u)`; when `u` is a valuation-ring unit this
residue is zero. Here `ct` is applied to the logarithmic derivative in
the valuation ring, not asserted multiplicative on the whole Hahn field.

In that report's two-ring principle, `∂p_L` is the tangent functional
`p_L*Ω¹_{X/k} → L` taking `df` to `∂(f(p_L))`. The field derivation
`∂: L → L` kills `k`; the associated tangent derivation on a base-changed
chart sends `f ⊗ a` to `a∂(f(p_L))` and kills the new scalar factor `L`.
Symmetric differentials use the quotient symmetric power, evaluated by
the same tangent functional in every factor. The annihilation statement
requires positive degree; the degree-zero section `1` does not vanish.
For the cotangent bundle, `P(E)` parametrizes one-dimensional quotients
of `E`, so a nonzero tangent functional gives a point of `P(Ω¹)` and
`O(1)` is the tautological quotient line bundle. Semiampleness here means
that some positive power of this line bundle is globally generated.

In the Diophantine report's Section 11, `𝒜_k(Γ)` is the ring of all
nonnegative-growth-support forms over `k`, and `ℛ_o(k,Γ) = o + Π_k(Γ)`
restricts the constant coefficient to `o`. The quotient report writes its
corresponding latter ring as `𝒜_{D,k}`; the subscript `D` records that
restriction. An **intermediate ring** `o ⊆ A ⊆ 𝒜_k(Γ)` with `A ∩ k = o`
need not satisfy `ct(A) ⊆ o`: for example `Z[ω + 1/2]` does not. This
condition is enough for the Pell-based integer definition, but not for the
quadratic ideal predicate, whose witness `x/√2` must belong to the ring.
`Inf(x)` in that report names the positive-growth-support ideal, including
zero and elements of either sign; it does not mean a positive infinite
number or an infinitesimal. The detector `Θ(a)` means `ct(a) ≠ 0`,
which differs from `a ≠ 0` and from invertibility. The graph predicate
`CT(x,n)` has the unique output `n = ct(x)`; its existential witness tuple
need not be unique. The predicate `Mult(a,b)` describes the fraction
`a/b` preserving the ideal under multiplication, with `b ≠ 0`. Recovering
the coefficient field requires both a nonzero multiplier and its inverse
to be multipliers. The interpreted value group uses `v(x) ≥ v(y)` exactly
when `x/y` is finite, consistent with `v = −leading exponent`.

For fractions, `𝔇(x₁,…,xₙ)` includes zero; actual
denominators are its nonzero members. It is defined for affine tuples,
not for the projective point at infinity. In the multiplier theorem, if
`λv` is primitive integral, the allowed scalar set is `λR_ℤ` for the
original vector and `R_ℤ` after rescaling the vector by `λ`.
The specialization label is a real projective point, so it can be infinity
even for an affine surreal value. The topology on `P¹(No)` uses the order
topology in both affine charts, with reciprocal coordinate `1/z` at infinity.
For `0 ≠ t ∈ Π`, the fixed field `ℝ(t)` is discrete in the induced surreal
order topology; its degree topology is a different, non-discrete topology.
The focusing matrix `F_{x,b}`
is the identity when `b = 0`; its value `x + 1/b` at infinity requires `b ≠ 0`.

For projective coordinates over a domain, an invertible coordinate ideal
need not be the unit ideal; only the latter means that the tuple is
unimodular. On a rigid projective target, the Diophantine report proves
that invertible omnific coordinate ideals detect ordinary rational points.
On rational curves its earlier criterion instead tests constant-term
specialization. For `[ω:1]`, that specialization is `[0:1]`, while projective
standard part is `[1:0]`, computed in the reciprocal chart. The point itself
is not rational, although its coordinate ideal is the unit ideal.

For a domain `R`, **normal** means integrally closed in `Frac(R)`, not
in every ambient Hahn field containing it. For a nonconstant point of an
integral constant affine curve over `R = 𝒜_𝕜(Γ)`, the function field embeds
in `Frac(R)`. Normality of `R` therefore suffices for a normalization lift.
A square root lying outside `Frac(R)` does not obstruct this argument;
failure of normality alone does not supply a curve point without a lift.
The singular-curve criterion concerns existence of nonconstant points,
not surjectivity of normalization on `R`-points. Its nonconstant-point
criterion requires `Γ ≠ 0`. For affine arithmetic models with smooth
geometrically integral generic curve, the exception means that the real fiber is isomorphic to `𝔸¹_ℝ` and an integer
point exists; the model need not be `𝔸¹_ℤ`. The coordinates of its real
polynomial parametrization need not have integer coefficients. Evaluating
at a monomial gives a finite-support witness, whereas an arbitrary
parameter from `Π` can have infinite support.

In that proof the curve function field `F` has restricted value group
`γℤ`, although the ambient Hahn group can have any rank. An Euler
derivation may map `F` into the larger Hahn field without preserving `F`.
The identity `α(∂) = h∂u`, with `h ∈ F` and the chosen
`v(∂u) = v(u) = γ`, puts the contraction's valuation in `γℤ`;
it does not put the contraction itself in `F`.

For `Y^m = P(X)` over an algebraically closed field of characteristic zero,
`e_i` are the root multiplicities and irreducibility requires
`gcd(m,e₁,…,e_k)=1`. The local exponent at infinity is `−deg P` in
the coordinate `s=1/X`. In the quadratic test, `P_odd` is the monic product
of factors of odd multiplicity, not the odd-degree part of the polynomial.
Over `ℝ` a factor may be quadratic; use its degree when computing
`deg P_odd`. The normalization parameter `T` is a function-field element
and need not be a regular function on the singular model.

In the group-variety applications, `ct:X(𝒜_k(Γ))→X(k)` is the map on
scheme-valued points induced by the ring retraction. The splitting
`G(𝒜_k(Γ)) ≅ G(k) ⊕ Π_k(Γ)^d` is a splitting of abelian groups of
points; it does not assert an algebraic-group product decomposition.
The vector coordinates on the unipotent subgroup are chosen.
For coefficient algebras, `S[ε]` means `S[T]/(T²)`, with `ε` the class
of `T`. This nilpotent is not a surreal infinitesimal. Finite coefficient
bases allow the Hahn construction to commute with finite scalar extension
and dual numbers; arbitrary coefficient algebras need not give a tensor
product. Joint injectivity of all coefficient maps is the descent condition
used for reduced algebras.

In the logarithmic applications, `X = X̄ ∖ E` and `E` is a reduced
simple normal-crossings boundary. A logarithmic factor contracts to
`∂u/u`, which need only lie in the valuation ring `𝒪`, rather than its
maximal ideal. Vanishing therefore uses `∂(𝒜) ⊆ Π` and `Π ∩ 𝒪 = 0`.
Both contractions are compared in the ambient Hahn field. Constant
extraction gives ring maps between `𝒜` and `𝒪`, but those maps do not
respect their inclusions in that field when the exponent group is nonzero.
For source C15's `t^γ = ω^(−γ)`, extend its additive functional `ℓ`
uniquely to the rational hull: `D_ℓ` corresponds to `∂_(−ℓ)`.

Workspace qualifications also govern the geometric summaries. At `Γ = 0`
the point ring is the coefficient field. For a smooth geometrically integral
curve, constant-term fibers over ordinary points are singletons in the rigid
case and copies of `Π_k(Γ)` in the affine-line case. The latter formula is not
a claim about arbitrary singular curves. A vanishing contraction of a
differential against an Euler tangent does not mean that the differential
itself vanishes at that point.

The localization `Oz_Π = (Oz \ Π)⁻¹Oz` differs from `Oz/Π`.
Its rational residue `res` has domain `Oz_Π`; standard part `st` has
domain the finite surreals. On their common domain, the maps agree
exactly on `ℚ ⊕ (ker st ∩ ker res)` additively, not just on `ℚ`.
In the Gaussian version these are the complex standard part and
Gaussian-rational residue, with values in `ℂ` and `ℚ(i)`.
The polynomial model `𝒫[T] = ℤ + Tℝ[T]` uses a formal variable;
`𝒫_t` denotes its evaluated image at `0 ≠ t ∈ Π`. The scale-defect
quotient `Uℝ[U]/Uᵐℝ[U]` has real dimension `m−1` but infinite
length as a `𝒫[U]`-module for `m ≥ 2`. The class `Ex(x)` consists
of exponents `β`; its associated denominators are `ω^β`.

For the full proper class, `Oz/J ≅ ℤ` and, for nonzero ordinary `n`,
`Oz/nOz ≅ ℤ/nℤ` describe quotient
maps and ordinary representatives; proper-class cosets are not elements of
a set. Similarly, `Frac(Oz) = No` asserts representation by fractions
inside `No`. Common support bounds for set-sized families may require a
larger exponent group than the input workspace. These class statements
must be distinguished from the corresponding assertions in any fixed Hahn
field or fixed universe.

For quadratic forms the omnific report uses `q(x) = B(x,x)` and
`B(x,y) = (q(x+y) − q(x) − q(y))/2`. Off-diagonal entries of the bilinear
matrix are half the mixed-term polynomial coefficients; an integral
quadratic polynomial need not have an integral bilinear matrix. Polarization
is performed over `ℝ` and extended by the same finite expressions to `No`.
The parameter `t` in its polynomial isometries `U_t` is free and may be
purely infinite; it is distinct from the fixed monomial `t = ω⁻¹` used below.
The quadratic energy `π(n) = ½ nᵀΠn` in Hahn–Tate Part II has an explicit
factor `½`; its associated polarized form therefore has matrix `Π/2`.

For omnific tuples, **primitive** means nonzero with no common nonunit
divisor; **unimodular** means that an `Oz`-linear combination of the
coordinates is `1`. Unimodularity implies primitivity. Their equivalence
for representatives of real projective directions in the Diophantine
report is a special result, not a convention for arbitrary tuples.
Its polynomial-arc variable `T` is formal; evaluation at `t ∈ Π` preserves
omnific membership, while preservation of eventual positive-real signs
requires `t > 0`. Choosing `t = ω` also ensures finite supports.

For decomposable equations, the real kernel is the kernel of the stacked
real and imaginary coefficient matrices over `ℝ`; Gaussian variables use
the complex kernel. A kernel-basis parametrization is coefficientwise Hahn
linear algebra, without an assertion of partial-sum convergence. The norm
`N_{E/K}(ΣeⱼXⱼ)` is a finite determinant polynomial over `K`; it does not
assume an embedding of `E` into the surreal field. Its trace pairing uses
ordinary transpose, not conjugate transpose. The arbitrary-characteristic
norm extension concerns abstract Hahn rings with finite étale coefficient
algebras; actual omnific and Gaussian omnific rings retain `ℝ` and `ℂ`.

## Monomials, support orientation, and valuation

The common Hahn convention is

```text
z = Σγ cγ t^γ,     t^γ := ω^(−γ),     support well ordered in increasing γ,
v(z) = min supp(z) for z ≠ 0,         v(0) = ∞.
```

Here `ω^a` is Conway's monomial map. It is not, for arbitrary surreal `a`,
an abbreviation for `exp(a log ω)` using the Gonshor exponential. In
particular, naming a monomial does not provide a differentiation rule for
arbitrary surreal exponents. The distinction is explicit in
[analysis](surcomplex/analysis/article.tex) (`a:rem:monomial`) and
[differential equations](surcomplex/differential-equations/article.tex)
(`diff:warn:monomialmap`).

An equivalent normal form writes `z = Σα cα ω^α` with **reverse**
well-ordered growth exponents. Translate by `α = −γ`; the leading growth
exponent is `−v(z)` for `z ≠ 0`. Negating an exponent reverses inequalities
in that exponent coordinate. It does not reverse ordinary coefficient
estimates or every inequality in a proof. The gamma-function report commonly
uses the growth convention; the two birthday reports use the specific
supports stated in their own hypotheses.

The [evaluation-at-omega report](surreal/hahn-evaluation-at-omega/article.tex)
(`eq:source`, `eq:prescription`) deliberately asks about the incompatible
prescription `x^a ↦ ω^a` on **increasing** source supports. Its negative
result is not a contradiction to `t^γ ↦ ω^(−γ)`. Keep the source variable
`x` visible when quoting that obstruction.

| Quantity | Meaning and guard |
|---|---|
| `v(z)` | Valuation of a scalar value; larger means smaller magnitude in the Archimedean comparison. |
| `lc(z)` | Coefficient at `v(z)`, defined for nonzero `z` unless an explicit zero convention is supplied. |
| `v_H(F)` | Least Hahn exponent whose **coefficient function** is nonzero; not necessarily the valuation of `F(a)` after evaluation. |
| `v_min(a)` | Minimum of the coordinate valuations of a finite tuple. |
| `w_{a,ρ}(P)` | Weighted Gauss valuation of a polynomial at a specified center and exponent threshold. |

The scalar rules are `v(xy) = v(x)+v(y)` and
`v(x+y) ≥ min(v(x),v(y))`; cancellation can make the second inequality
strict. A nonzero ordinary real or complex constant has valuation zero,
regardless of its ordinary absolute value.

The [Prony report](surcomplex/prony-reconstruction-at-surreal-scales/article.tex)
uses separation valuations `v(a_i−a_j)`: a collision has value `∞`, while
value zero means distinct residue classes for integral nodes. Its nonuniform
certificate (`prony:thm:graph`) permits a nondivisible `Γ`. Fractional scaling
potentials belong to the auxiliary ordered divisible hull `Γ_ℚ`; the input,
inverse correction matrix and reconstructed nodes and weights remain in the
original Hahn field. This temporary extension does not change the workspace
named in the theorem.

The [Wick report](surcomplex/wick-summability-certificates/article.tex)
uses `Hilbert basis` for the finite indecomposable generators of its integer
incidence semigroup, and `Gaussian expectation` for a finite pairing sum
with symmetric bilinear covariance. Its `D` is an incidence matrix.
Coefficientwise nonnegativity is stronger than ordered-field positivity.
The grouping proposition `wick:prop:signcoherent` permits one common
nonzero complex factor in the couplings; factoring its `n`th power out
of each order block prevents cancellation there.

The Wick balancing vector lies in the stated divisible group `Γ`.
For `P = x²` and `C = t` over integer exponents, the atoms are summable but
the required `0 < 2p < 1` has no solution in `ℤ`. A rational certificate
belongs to a larger group. The distinction from the Prony certificate above
is that the Wick equivalence explicitly asks for the scaling exponents
in the original group.

The [holonomic report](surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex)
uses `Dom_str(f)` for strong evaluation of the fixed formal coefficient
family. Its inward-stability lemma `hol:lem:inward` shows that membership
depends only on the nonzero argument's valuation and is preserved when that
valuation increases. This does not mean that the leading valuations of the
coefficients determine the domain; their higher support tails are retained.
The torsion substitution `z^r G(z^m)` preserves and reflects entireness
without divisible exponents.

A valuation coarsening changes the value map on the same field. Projecting
each Hahn exponent through a quotient with a nonzero kernel can collapse
infinitely many supported exponents to one value; it need not produce a
Hahn series over the quotient group. The example in `hol:rem:thetacoarse`
makes this distinction explicit.

The nonlinear holonomic argument keeps the scaled lowest-valuation layer
as a polynomial `φ_δ(X)`. Its coefficient Gauss value `γ_δ` need not equal
the valuation of the evaluated sum: `φ_δ(1)` may vanish even though the
polynomial is nonzero. The selected corner has integer data `(d_P,w_P)`;
its residue polynomial is `χ_P ∈ k[T]`, while its full-coefficient polynomial
is `I_P ∈ k((t^Γ))[T]`. Integer roots of `I_P` are roots of `χ_P`, but the
converse can fail. The degree cutoff `κ_P` is an ordinary rational number;
the exclusion scale `δ₀` is an element of `Γ`. Computing the former does
not divide elements of `Γ`. The coordinate derivative `D_z` kills the Hahn
coefficient field, including all monomials `t^γ`.

For the coefficient-field argument, `cvr(f)` is the dimension of the
rational span of the nonzero Taylor coefficient values in `Γ ⊗ ℚ`.
It differs from the rational rank of the full coefficient field's value
group and from the number of exponents in a coefficient's Hahn support.
“Rank one” means Archimedean here; it does not mean rational rank one.
“No order unit” means that no single positive scale has cofinal integer
multiples, a stronger condition than being non-Archimedean.

The linearization offset `θ = min(ord_z Π_ij − j)` is an integer and can
be negative. Its multiplier `Ξ(n)` depends on the solution and differs
from the equation's corner polynomials `χ_P` and `I_P`. Mixed jets use
differentiation before dilation: `(D_z^j f)(λz)`; differentiating `f(λz)`
instead multiplies this by `λ^j`. Coarsened residue is `red_Δ` in the field
`k_Δ`; when it embeds a coefficient field `L`, rational identities descend
through the embedded copy of `L`, without choosing a residue-field section.

The [hidden-negative-directions report](surcomplex/hidden-negative-hermitian-directions/article.tex)
uses `𝒫_Γ` for complex Hahn series supported in some finitely generated
additive subgroup of `Γ`; “finite-lattice support” permits infinite supports
and nondiscrete subgroups. Its valuation closure is `P̄_Γ`, written
`\overline{\mathscr P}_Γ` in the article, and uses neighborhoods
`v(x−a) > ρ` for `ρ ∈ Γ`. For `Γ = ℚ` it is the complex Levi–Civita field
of left-finite series. This differs from the Hahn–Herglotz notation `𝒞_Γ(X)`
for Hahn series with continuous-function coefficients.

In that report, `A ⪰ 0` tests **every** vector over the stated scalar field;
positivity on a smaller probe field always names that field. Its two-scale
measure criterion uses the scalar Jordan parts `ν_u⁺`, `ν_u⁻` of
`ν_u = u* M₁ u` and the ordinary vector total variation `|σ_u|` of
`σ_u = M₁ u`. Neither is an entrywise positive part of a matrix measure.
The null conditions quantify over every ordinary `u` and every measurable
null set; the resulting matrix positivity quantifies over all Hahn vectors.

In [bounded-support transcendence](surreal/transcendence-over-bounded-support/article.tex),
`𝓑_G(K)` is the ring of `K`-coefficient Hahn series whose support is bounded
above **in G**, and `𝓕_G(K) = Frac(𝓑_G(K))`. These are distinct from the
full real Hahn field `F_Γ` and the tail-span report's full coefficient fields
`B`, `B₀`. An unbounded geometric series may already lie in `𝓕_G(K)`.
When `G` has no order unit, `𝓑_G(K)` itself is a field. The rank-one width
used in the unit criterion takes a supremum in `ℝ` after passing to the
highest Archimedean quotient, not a supremum in the original arbitrary group.

For an increasing cofinal support `(a_α)_{α<κ}`, its bounded initial Hahn
truncations have error valuation `a_β` and converge in the named workspace.
If `κ` is uncountable, these truncations are generally infinite series.
In this uncountable case, the net of finite subsums does not reach the neighborhood beyond `a_ω`,
because a finite set omits some earlier coefficient. Thus strong summability
and cofinal support do not alone imply convergence of finite subsums.

The [matrix-scaling report](surreal/matrix-scaling-at-surreal-scales/article.tex)
uses `κ_e = τ_e⁻ − τ` for a spanning-tree deletion gap, with `∞` for a
bridge. The costs are valuations of the normalized base entries, and
“positive-leading” means a positive real leading coefficient even when
higher coefficients are complex. Its `Π_p` projects onto potential differences
and `H_p = I − Π_p` onto weighted conserved flows; neither symbol denotes a
Hermitian form. The general-constraint version requires a real constant matrix
because Hahn-valued minors can contribute their own valuations.

The formal tangent space of the matrix-scaling conservation equations at a
balanced `h` is `ker(B diag(p_e exp(h_e)))`, a vector space over the Hahn field.
The evaluated domain `𝔪^E` is not itself a vector space over that field.
For the trivial value group it is a singleton: formal coefficient sharpness
still makes sense, but optimality over nonzero infinitesimal changes requires
`Γ ≠ {0}`.

## Inner products and operator spectra

The [finite-dimensional spectral report](surcomplex/spectral-theory/article.tex)
uses `⟨x,y⟩ = x* y`, conjugate-linear in the first variable.
[Infinite-dimensional Hahn spectral theory](surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex)
retains different source conventions: Parts I and IV are linear in the first
variable; Part II is conjugate-linear in the first, and Part III uses none.
Conjugate the scalar value, or
exchange the arguments, when translating between them. Positivity and
adjoint identities survive this change, but the linearity of a represented
functional changes.

In that report, `σ_Γ^alg` means failure of bijectivity on `H((t^Γ))` and
`σ_Γ^adj` means failure of inversion in `B(H)((t^Γ))`. Their equality is
proved for constant normal operators and for Part IV's compact-residue
class `T+E`, under their respective hypotheses; Part III also proves it in
the Volterra and increasing-block examples. The Fredholm alternative
separately equates bijectivity and algebra inversion for `I+C` with
nonnegative-valuation trace-class coefficients. Part II's `σ_𝒜` refers to inversion
in the row- and column-finite Hahn algebra on a different vector space.
A prime in `σ_ℂ(T)'` denotes ordinary spectral accumulation, not a derivative.

Part III's `Σ^𝔄_Γ(T)` is the algebra-relative spectrum of a constant element
of a named nonzero unital complex algebra. Its `σ_{D,𝔄}(T)` is the
**finite-index Drazin spectrum**: it excludes precisely those shifts with
an invertible corner and a finite-index nilpotent corner. Generalized Drazin
invertibility, which allows a quasinilpotent corner, is a different notion.
The idempotents `P_nil` and `P_inv` select corners and need not be central
in the whole algebra; each corner uses its own idempotent as identity.
The local resolvent here is `(S − u1)⁻¹`, whose constant Laurent coefficient
is `S^D`; changing to `(u1 − S)⁻¹` changes that coefficient's sign.

Keep the Drazin index `ν` separate from the polynomial ramification index
`e_a = ord_{X=a}(p(X) − p(a))`. The former controls the shifted inverse's
valuation `−ν v(ε)` for `ε ≠ 0` infinitesimal; the latter controls the centered image of a halo:
zero together with nonzero infinitesimals of valuation in `e_a Γ`.
That image is a scalar-root condition, not a change in invertibility of
an old parameter when the exponent workspace grows. `v_𝔄` is the leading
support exponent of an operator series, with `v_𝔄(0)=∞`; multiplication is
only superadditive when the coefficient algebra has zero divisors, while
multiplication by a nonzero scalar has exact additive valuation.

Keep the three size notions distinct: `‖T‖_H` is an ordinary real operator
norm, `‖x‖` is a positive Hahn scalar, and `ρ(x) = exp(−v(x))` is the real
valuation size when `Γ ⊆ ℝ`. A field-valued operator bound need not have a
least possible value. The vector norm and scalar modulus exist without
divisibility because their squared values have even leading exponents;
arbitrary positive Hahn scalars have a square root exactly when their
leading exponent lies in `2Γ`.

Part IV uses `𝒯_Γ = S₁(H)((t^Γ))` for trace-class coefficients and
`𝒯_Γ⁺ = {C ∈ 𝒯_Γ : v(C) ≥ 0}`. The trace `Tr_Γ` is defined on all of
`𝒯_Γ`; `Det_Γ(I+C)` is defined only for `C ∈ 𝒯_Γ⁺`. The determinant and
its Fredholm alternative allow arbitrary complex Hilbert `H` and ordered
set-sized `Γ`, including zero; the compact-spectrum classification retains
its stronger hypotheses. Ordinary coefficient trace norms justify the
Taylor derivatives; Hahn summability uses finite support contributions,
without a uniform norm bound across coefficients. A zero standard part
of the determinant does not imply that the Hahn determinant is zero.

Adjunction `C*` is canonical. Operator conjugation `𝒥C𝒥` uses a fixed
antilinear isometric involution `𝒥` of `H`; the bar on its determinant
conjugates scalar coefficients only. The Riesz convention `(ζI−T)⁻¹`
in Part IV has the opposite sign to Part III's local resolvent above.
In the finite reduction, `F=ικ` has bounded ordinary factors,
`M_F=I+C+F`, `R_F=M_F⁻¹ι`, and `L_F=I_m−κR_F`; the inverse of `L_F`
may have negative valuation although each determinant argument lies in
the declared nonnegative domain. Cokernels and the Fredholm index are
algebraic over the Hahn field, not quotients by topological closures.

The coupling variable `z` and spectral variable `λ` satisfy `λ=z⁻¹`
only for `z ≠ 0`. Finite coupling detects reciprocal eigenvalues when
`A` has trace-class coefficients; it does not evaluate the determinant at
infinite coupling to detect the spectral monad. Ordinary entire coefficient
functions alone do not license evaluation at negative-valuation inputs.

The projection calculus in Part II is additive on disjoint label sets
after applying each projection to a vector and taking a **strong Hahn sum**.
This is distinct from the classical **strong operator topology**, which
tests topological convergence on each vector. Even for `Γ = ℚ`, the vector
`Σₙ t^{1−1/(n+1)} eₙ` is a valid Hahn sum whose coordinate partial sums do
not converge in valuation. The failure of an operator-valued Hahn sum alone
does not decide whether a projection-valued set function is a spectral
measure; specify the intended additivity and topology.

In [Hahn–Tate uniformization](surcomplex/hahn-tate-uniformization/article.tex),
the positive period value is `α = v(q)`. Its two convex subgroups have
different roles:

| Subgroup | Definition and role |
|---|---|
| `H_α` | Values bounded in absolute value by some ordinary integer multiple of `α`. The quotient valuation `w = v mod H_α` on `K_Γ` has residue field `K_{H_α}`. |
| `H_α^-` | Values `γ ∈ H_α` with `n\|γ\| < α` for every `n ≥ 1`. Quotienting `H_α` by this subgroup gives the rank-one valuation on `K_{H_α}` used for classical Tate uniformization. |

The period is a unit for the first coarsening, but has positive rank-one
valuation for the second. Arbitrary formal coefficients in `K_{H_α}`
can be evaluated at inputs with `w(z) > 0`; fine positivity `v(z) > 0`
alone is insufficient. These Part I coarsenings require no divisibility;
Part II retains its separate hypothesis for halves of period exponents.
Over the lexicographic group `ℤ ⊕ ℤ` with
`H = {0} ⊕ ℤ`, substituting `z = t^(0,1)` into
`Σₙ t^(0,−n) Zⁿ` makes every term `1` and fails strong summability.

Distinguish the circularly ordered quotient `H_α/ℤα` from its rank-one
quotient `(H_α/H_α^-)/ℤᾱ`: the kernel of the map between them is `H_α^-`.
Even if `H_α/H_α^-` is the real line, the full quotient can retain
infinitesimal directions. A classical real circle describes the last
quotient in that case. It describes the full value quotient when
`H_α^- = 0` and the embedded value group is all of `ℝ`.

In the same report's node chart, the vector valuation is
`𝐯(x,y) = min{v(x),v(y)}`, with `v(0) = ∞`. The word “isometry” means equality
of these ordered-group values for differences in the chosen coordinates;
it does not introduce a real-valued metric. Both coordinates are needed
because their leading terms can cancel separately. Passing to a rank-one
quotient can erase a strict increase in vector valuation, as the
`ℤ ⊕ ℤ` example in Section 9.3 shows.

Part II of Hahn–Tate uses `Π` for the matrix of period exponents,
`π(n) = ½ nᵀΠn` for its quadratic energy, and `β_j = v(z_j)` for argument
values. In a finite lexicographic coordinate model, `𝓑_j` are real bilinear
forms and `V_j` are their successive restricted radicals. “Rational”
means `span_ℝ(L ∩ V_j) = V_j`; the form coefficients may be irrational.
The lattice rank `g`, number of coordinate levels `r`, and number of strict
radical drops `s` have different roles: `s ≤ min(g,r)`. Under the flag
criterion, `ω^s` is the order type of the exponent set before cancellation.
It is the actual support length at positive monomial arguments; it is
not a surreal birthday. Well-ordering of that exponent set and finiteness
of every exponent fibre are separate requirements for strong summability.

In Hahn–Tate's coupled theta example, `ξ` is the full Hahn solution and
`ξ₀` is its reduction retaining only first-coordinate-zero terms. The
zero-row equation is an equation for `ξ₀`. Its coefficients determine the
displayed expansion of `ξ` below higher first-coordinate rows.

## Finite elements, standard part, and reduction

Use `O_F = {v ≥ 0}` and `m_F = {v > 0}` for the finite valuation ring and
its infinitesimal ideal in a specified field `F`. Zero belongs to both.
For the full classes, subscripts `ℝ` and `ℂ` distinguish the real and complex
versions. Finiteness means bounded magnitude by an ordinary integer;
infinitesimality means magnitude below every positive ordinary real number.
Neither says anything about finite birthday or finite support.

These identifications use ordinary real or complex coefficients. For a general
coefficient field `k`, the Hahn ring `{v ≥ 0}` still has residue map to `k`,
but its elements need not be bounded by ordinary integers. The
[computer-algebra report](foundations-and-computation/computer-algebra/article.tex)
(`cas:thm-core`) separates this general residue from ordinary standard part.

Scalar standard part is the ring map `st : O_F → ℝ` or `ℂ`. For finite
`z`, it is the coefficient at exponent zero, and `z − st(z)` is
infinitesimal. Some reports call this map `red` or `res`; these names are
aliases **on that domain**. Coefficient extraction at zero extends to
infinite elements as an additive operation, but is not a ring homomorphism
there: the zero coefficients of `ω` and `ω⁻¹` both vanish, while that of
their product is one. The differential-equations report calls this extended
operation `ct` (`diff:warn:ct`).

For a nonnegative-support family of holomorphic coefficients, **reduction**
means `red(Σγ fγ t^γ) = f₀`, whose output is an ordinary **function**.
This is distinct in type from scalar standard part. The
[global-divisor report](surcomplex/global-divisors/article.tex)
(`global:sub:conventions`) intentionally reserves `red` and `st` for these
two maps. Neither operation is a contour or local residue.

The [finite-probability report](surreal/finite-surreal-probability/article.tex)
uses **limited** for this same bounded-magnitude notion. Its finite-range
random variables have finitely many values, which may themselves be infinite.
Their expectations are finite sums in the scalar field. A point-weight vector
presupposes the full event algebra; for a smaller finite algebra, use its
measurable atoms. Regularity means positive mass on every nonempty measurable
event. Conditional identities are pointwise on positive-mass atoms and hold
up to arbitrary constant versions on null atoms; scalar expectations remain
independent of those choices.

Conditional shadows retain the order of leading atom scales and normalized
leading coefficients, while real-payoff comparisons can also depend on signed
higher coefficient rows. Neither representation determines arbitrary surreal
payoff comparisons. For conditioning precision, `β` and `λ` belong to the
ordered value group: `v(error) > β + λ` is a sufficient uniform contract,
with `β` the event valuation and `λ ≥ 0` the requested output precision.
It need not hold when particular numerator and denominator errors cancel.
Finite likelihood updates require a positive joint normalizer to commute;
a neutral likelihood ratio of one leaves a binary law unchanged.

The probability report's softmax “limit” is a standard-part identity for
one finite list of separated surreal scales. Its local `O(η²)` means an
error bounded by a real constant times `|η|²`. No sequence convergence is
asserted. Finite-alphabet entropy is limited and commutes with standard part;
relative entropy may be positive infinite as an actual surreal. Its formal
`+∞` value for a support mismatch, and formal endpoint logits, lie outside
the field. Logarithmic loss over strictly positive predictions attains its
truthful minimum only for an interior true law; boundary truths have an
unattained entropy infimum in that prediction domain. Brier loss permits
the full simplex, including its boundary.

For smoothing at an arbitrary positive infinitesimal scale `t`, an unseen
category satisfies `st(p_i/t) = a_i/N`. In Hahn coordinates its leading
coefficient is `(a_i/N) lc(t)`, which reduces to `a_i/N` for a monomial with
unit coefficient. A regular prior need not give a regular posterior: zero
likelihoods remove categories. Sample sizes and path horizons in the finite
probability results are ordinary integers. A bounded stopping time takes
values in one such finite horizon; martingale values may be infinite scalars.
The stopping-time symbol `T` is local to that subsection and is distinct from
the preceding transition matrix.

In the rare-latent-regime model, `H` is the binary latent label, `X_i` uses
positive integer coordinates, `F_n` records the first `n` observations
(`F_0` is trivial), and `F_∞` is the sigma-algebra generated by all of them.
It does not introduce a surreal time index. The likelihood ratio
`r_n = 2^(2K_n−n)` is real at every ordinary time, even on paths where it
has no real bound over time. Standard-part limits, real limits of each Hahn
coefficient and order convergence of the Hahn values are different notions:
on typical common-regime paths the posterior tends coefficientwise to zero,
yet its consecutive differences always exceed the fixed order tolerance `t²`.

In the Loeb bridge, `I` is the ordinary index set of finite experiments,
`𝓘` is their internal event algebra, `ν` is the internal hyperreal probability,
and `ν_L` is its completed real Loeb measure. The algebra `𝓘` need not be
closed under ordinary countable unions. The Poisson count `S` is internal;
the union of its ordinary fixed-count events is Loeb measurable and has
measure one. Defining the ordinary count `Z` on the remaining null set
completes an ordinary measurable random variable. Here `H` denotes the
internal sample size, distinct from the binary latent label used earlier.
An ordered embedding fixing `ℝ` preserves standard parts but supplies no
internal events or preservation of exponential operations.

The word **finite** has several other explicit uses: a finite-dimensional
algebra, a finite map, finitely many terms, and finite birthday. The
[graph report](surreal/canonical-forms-need-not-be-subgraphs/surreal_graphs.tex)
(`sec:definitions`) uses “finite value” for **finite birthday**. When quoting
it outside that report, write “value of finite birthday.” The
[broadcast report](surreal/broadcast-sum-of-surreal-sequences/article.tex)
(`sec:background`) calls these numbers **short**, and distinguishes them
from bounded-magnitude finite surreals.

## Topologies and strong summation

| Structure | Neighborhoods or criterion | What must stay explicit |
|---|---|---|
| Full surreal **fine topology** | Ordered-modulus balls of every positive surreal radius. | On a set-sized subset its subspace topology is discrete; this does not say the full class is discrete. |
| **Intrinsic valuation topology** of `K_Γ` | Bounds `v(x−a) > ρ` with `ρ ∈ Γ`. | It uses the workspace's thresholds. At arbitrary rank, increasing valuations need not be cofinal in `Γ`. |
| **Rank-one valuation metric** | For the report's `Γ = ℝ`, `|x|_v = exp(−v(x))`, with `|0|_v = 0`. | This real-valued non-Archimedean norm gives the intrinsic topology, not the fine subspace topology. |
| **Standard-part topology** on finite elements | Inverse images of ordinary open sets under `st`. | Points with the same standard part cannot be separated. On the zero monad the restricted topology is indiscrete. |

“Reduction,” “residue,” and “shadow” topology are local names for the last
row when defined by this pullback. Prefer **standard-part topology** in
cross-report prose. The analytic-geometry report records “reduction topology”
as an earlier synonym and states explicitly that the zero-monad restriction
is indiscrete.
See [contours](surcomplex/contours-and-stokes/article.tex)
(`contours:subsec:conventions` and its topology subsections),
[analysis](surcomplex/analysis/article.tex) (`a:def:fine`, `a:thm:discrete`),
and [rank-one Berkovich theory](surcomplex/rank-one-berkovich/article.tex)
(`eq:mainfield`, `prop:topologies`).

The [genetic-gap report](surreal/genetic-gaps-and-primitives/article.tex)
also uses the original paper's **restricted set-union convention**: global
open classes must be set-sized unions of intervals with surreal or end-gap
endpoints. This is stricter than pointwise local order-field openness.
Its gap indicator is locally constant and has zero local derivative, yet
fails global continuity for that restricted convention. Its order-automorphism
primitive is continuous in both senses. State this convention explicitly;
“fine” or “continuous” alone does not identify the intended assertion.

**Strong Hahn summability** is not another name for convergence in any of
these topologies. It requires a well-ordered union of supports and finitely
many contributions at every exponent; the sum is coefficientwise. Thus
`Σn≥0 t^n = (1−t)⁻¹` is a strong identity. In `ℂ((t^ℝ))` its finite partial
sums also converge intrinsically, whereas in `ℂ((t^(ℚ+ℚω)))` their error
valuations never exceed `ω`. In the full fine topology they do not converge
to that sum. “There is no topological convergence” must therefore name the
full fine setting and the relevant set-indexed convergence assertion.

In the [tail-span report](surreal/tail-spans-and-differential-transcendence/article.tex),
a **cofinite tail** removes finitely many coefficient indices. It need not be
the complement of an ordinal initial segment. By contrast, a **valuation
truncation** through a threshold retains all exponents below that threshold,
which can be infinitely many even in a rational-exponent workspace. The
algebraic-approximation criterion tests the field generated by that whole
prefix, not just finitely many observed coefficients.

In the [three-duals report](surcomplex/three-duals-of-hahn-vector-spaces/article.tex),
a **strong map** preserves admissibility of every strong family and commutes
with its sum; it is linear over the whole Hahn field. Its operator coefficients
have one common well-ordered support, which is stronger than pointwise support
or a common lower valuation bound. `E_Γ(V)` has finite total coefficient rank;
`C_Γ(V)` has finite coefficient rank below every cut. The latter is a completion
for the induced valuation uniformity, with nets of truncations at arbitrary
rank. An order unit implies `E ⊊ C` in infinite coefficient dimension; strict
inclusion `C ⊊ V_Γ` additionally requires a noncyclic nonzero group. Neither
completion nor strong closure means completion in a coefficient norm. The
restriction space `P_Γ(V)` requires a common lower valuation bound on constants;
its supports need not have a well-ordered union. The invisible continuous
functionals vanish on `C_Γ(V)`, and their common kernel equals that completion.
For Hilbert coefficients, **order-bounded** means a positive real-Hahn bound.
When comparing least bounds with the spectral report, allow nonnegative bounds:
the zero operator has least nonnegative bound `0` but no least positive one.
A subspace with zero orthogonal complement can have an algebraic direct-sum
complement while admitting no orthogonal direct-sum complement. Under exponent-group
inclusion `Γ ⊆ Δ`, the induced topology on `V_Γ` agrees with its intrinsic
topology when `Γ` is cofinal; otherwise it is discrete. Strong operator series
extend uniquely as strong operators. For Hilbert coefficient spaces, norms
and scalar-valued functionals take values in the scalar field; general operator
outputs remain vectors. Allowing all positive surreal norm tolerances isolates
those vectors without identifying them with surcomplex scalars.

A **coefficientwise Hahn sum** in the
[measure report](surreal/hahn-valued-measures-and-probability/article.tex)
uses one common well-ordered support and ordinary absolutely convergent
sums at each exponent; infinitely many members may contribute there
(`meas:lem:coefpositive`). A **strong Hahn measure** requires strong
summability for every disjoint event sequence. A **coefficientwise Hahn
measure** instead has finite signed or complex coefficient measures on one
common support. Only the strong axiom forces finite point support at every
coefficient on a countably separated space. Positivity of the full Hahn value
does not mean positivity of every coefficient measure: later signed
coefficients may be negative while the leading nonzero coefficient is positive.

For normalized probability hierarchies, **coefficientwise convergence** means
ordinary real convergence at each fixed exponent; it need not imply intrinsic
valuation or fine convergence. Bounds for the real-observable expectation use
a uniform real bound (or a bound valid almost everywhere for every component),
not an essential bound for the leading real shadow alone. Countable common
support and integrable coefficients preserve positivity when integrating a
Hahn-valued function against an ordinary positive finite measure; uncountable
common support alone does not. Finite-hierarchy posterior coefficients are
measurable on a common well-ordered support, but need not be integrable until
the observation density is multiplied in and cancels the denominator.

In probability extension arguments, a **fine ultrafilter** contains the cone
of snapshots containing each prescribed point; “fine” here is a filter property,
not the full surreal fine topology. The snapshot size `H = [|s|]` is a scalar
in an ultrapower, and its image after an ordered-field embedding is a surreal;
it is not an ordinary set cardinality or an induction index. Such embeddings
preserve order and field operations, but need not preserve chosen exponential
structures or Hahn coefficientwise summation. Equal singleton masses imply
invariance under permutations with finite support, not arbitrary permutations.

The [Hahn–Herglotz report](surcomplex/hahn-herglotz-positivity/article.tex)
uses real coefficientwise measures on the ordinary circle. Its moments are
Fourier moments `c_n = ∫ ζ^(−n) dμ` and its Toeplitz convention is
`T_N = (c_(j−k))_(0≤j,k≤N)`, a matrix of size `N+1`.
These differ from interval power moments and Prony's finite power sums.
Coefficientwise and strong measure classes overlap: the finite atomic
quadratures satisfy both, while diffuse Haar leading coefficients exclude
strong additivity. The distinction is in the summation axiom, not in whether
the article calls its object a measure.

## Coefficient rings and functions

State both the coefficient category and the ordinary base. The common
conventions of [analytic geometry](surcomplex/analytic-geometry/article.tex)
(`analytic:def:ringA` and its ring comparison),
[finite deformations](surcomplex/finite-deformations/article.tex), and
[trigonometry](surcomplex/trigonometry/article.tex)
(`trigonometry:sec:rings`) distinguish:

| Ring | Required coefficient data |
|---|---|
| `O(U)((t^Γ))` | One well-ordered Hahn support; all coefficient functions holomorphic on the **fixed** ordinary domain `U`. |
| Common-domain Hahn germs `𝓡_n` | Germs represented by such a family on **some one common** ordinary neighborhood of the center. |
| Radius-free germs `A_n = ℂ{z₁,…,zₙ}((t^Γ))` | Each coefficient is a convergent germ; no common neighborhood is required. |
| Formal-coefficient ring `ℂ[[z₁,…,zₙ]]((t^Γ))` | Formal coefficient power series with one well-ordered Hahn support. |
| `K_Γ[[Z]]` | Formal power series in an ordinary integer-indexed variable with Hahn coefficients; no common support bound is implicit. |
| `ℂ[Z]((t^Γ))` | Polynomial coefficients at each Hahn exponent; no common bound on their polynomial degrees is implicit. |

The order of the two series constructions matters. For example,
`Σn≥0 t^(−n) Z^n` belongs to `K_Γ[[Z]]` when `1 ∈ Γ`, but its combined
Hahn support is not well ordered, so it is not a formal-coefficient Hahn
series in `ℂ[[Z]]((t^Γ))`. Conversely, analytic versus formal coefficient
conditions are about ordinary coefficient functions, not about the valuation
of a single scalar.

Keep the script letter in `𝓡_n`: analytic geometry reserves `R_n` for the
ordinary convergent-germ ring `ℂ{z₁,…,zₙ}` (`analytic:def:ringA`), while
`𝓡_n` is the common-domain Hahn germ ring (`analytic:def:ringR`).

For a Hahn ring `A((t^Γ))`, distinguish its nonnegative-support subring from
the positive-support **ideal of that subring**. The latter lacks `1`; when
`Γ` is nontrivial it is not an ideal of the full Hahn ring, where positive
monomials are invertible. Taylor evaluation of holomorphic coefficients at `c + ε` requires
`c` in their common ordinary domain and an infinitesimal displacement `ε`.

Do not use the local symbol `A` as a category name: it denotes radius-free
germs in analytic geometry, polynomial-coefficient Hahn series in the
[entire-functions report](surcomplex/entire-functions-at-arbitrary-rank/article.tex)
(`ent:subsec:chain`), and a particular ordinal-support subring in the
[product-birthday report](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex)
(`eq:ring-intro`). Likewise `O` may mean a valuation ring or ordinary
holomorphic functions; include a subscript or the domain when both occur.

A **coherent section** on a fixed ordinary domain, a **canonical lift** of one
ordinary function, a **germ-analytic** function, and a merely **fine
differentiable** function name distinct hypotheses. Lifts form a proper
subclass of coherent sections, and coherent sections a proper subclass of
germ-analytic functions. Germ analyticity implies fine differentiability;
the analysis report does not prove strictness of that last inclusion
(`a:def:classnames`, `b:def-classes`). “Entire” in the
arbitrary-rank report means its stated strong evaluation condition at every
point of one fixed Hahn field; it does not mean coherence at every scale of
the full surreal class. In the genetic-gap report, “entire” means a genetic
function defined at every surreal input, without asserting analytic
holomorphy. “Uniform support” should always state the ordinary
domain or family over which one support is required.

For coherent sections on the finite plane, **ordinary-real boundedness**
and **coefficientwise boundedness** are incomparable. The section `tZ` has
real-bounded values but an unbounded coefficient; the constant `ω` has
bounded coefficients but no ordinary-real value bound. A single surreal
value bound is weaker than either. State which bound a Liouville or Cauchy
claim uses. Likewise, injectivity of formal-series evaluation as a
**function germ** does not imply injectivity at one fixed point: `X−h`
evaluates to zero at `h`.

## Computability and names

The [computable-surreals report](foundations-and-computation/computable-surreals/article.tex)
(`sec:conventions`, `def:structural`, `def:elf`, `def:puiseux`) distinguishes
three representations. “Computable surreal” should name which one is meant.

| Notation | Information carried by a name |
|---|---|
| `S_str` | A program hereditarily enumerating a separated, well-founded system of Conway cuts. Validity is a semantic condition, not termination of the enumerating program. |
| `P_c` | Uniformly computable real coefficients on one lower-bounded rational lattice, with one ramification denominator supplied by the name. |
| `L_c` | Uniformly computable real coefficients at rational addresses, a rational lower bound, and computable finite candidate covers containing every nonzero exponent below each rational threshold. |

Here `ℝ_c` denotes ordinary computable reals with fast Cauchy names:
`|A(k)−a| ≤ 2^(−k)`. For a coefficient family, one algorithm `A(q,k)` must
work jointly in the rational address and precision; the statement that
each coefficient separately is computable is weaker. A candidate cover may
include zero coefficients. It supplies a finite complete search domain,
not an exact nonzero-support list or a zero test. Likewise, **left-finite**
means finitely many support exponents below each rational bound; merely
well-ordered support does not imply this property.

Distinguish an **extensional closure** assertion (every result has some
name) from a **uniform algorithm** transforming all valid input names into
output names under stated promises. Algebraic closure or field closure does
not by itself supply a branch selector, inverse algorithm, equality test,
or a converter between structural and numerical names.

A **valuation stabilization modulus** is supplied computational data:
`n,m ≥ μ(B)` implies `v(x_n−x_m) ≥ B`, so coefficients below `B` agree
exactly (`eq:modulus`). This use of “modulus” differs from `|z|` or `|z|_v`.
An exact finite jet contains names for its real coefficients, not merely
finite-precision rational approximations. Ordinary coefficient precision,
exact valuation truncation, and full surreal fine neighborhoods remain
separate. Finally, the computability report uses `K` for a halting set;
it is not the Hahn field denoted `K` in neighboring reports.

## Derivatives, exponentials, phases, and residues

| Operation | Convention to state when using it |
|---|---|
| Fine derivative `f′(x)` | Difference quotients with all positive surreal tolerances and surreal increments. It differentiates a **function at an argument**. |
| Coefficientwise derivative `D_z` or `∂_μ` | Differentiate ordinary coefficient functions; hold the Hahn monomials constant. |
| Formal derivative `d/dZ` | Differentiate the integer powers of an indeterminate; the coefficient field is constant. |
| Scalar derivation `∂` or `D` | A specified derivation of the surreal field, such as the normalized Berarducci–Mantova derivation with `∂ω = 1`. It acts on scalar coefficients. |
| Parameter derivative `d/dε` | A specified parameter calculus, for example `d(ε^q)/dε = q ε^(q−1)`; do not substitute another variable while holding it constant. |

Identifying two of these requires a proved compatibility statement. The
[genetic-gap report](surreal/genetic-gaps-and-primitives/article.tex)
(`eq:derivative`) and [gamma-function report](surreal/gamma-functions/article.tex)
(“Fine coordinate derivatives versus a scalar derivation”) use this
distinction to explain nonconstant zero-derivative functions. The
[physics report](physics/surreal-scalars-and-spacetime/article.tex)
(`phys:tab:derivatives`) states explicitly which operation is used for its
fields on ordinary spacetime.

The [omnific Diophantine report](surreal/omnific-diophantine-geometry/article.tex)
(`odg:eq:euler`) instead uses freely chosen local Euler derivations
`∂_λ(ω^h) = λ(h)ω^h`, where `λ : H → ℝ` is rational linear and `H` is a
set-sized divisible exponent group. They kill the scalar coefficient field.
In the `t = ω⁻¹` convention this becomes `∂_λ(t^γ) = −λ(γ)t^γ`.
One fixed `λ` can kill nonconstant monomials; detecting a given nonconstant
requires choosing a suitable functional. This construction does not specify
a derivation of the full surreal field.

In that report's constant-discriminant section (`odg:disc:sub:disc`), the
Euler family uses rational-valued functionals on `Γ_ℚ` and acts on the
Hahn field with algebraically closed coefficients. The bar in `P̄ = ct P`
applies the exponent-zero map to every coefficient; it is neither complex
conjugation nor extraction of the constant coefficient in `X`. Squarefree
for `P̄ ∈ 𝔬[X]` means squarefree over the coefficient field `𝕜`, or no
repeated root over its algebraic closure. A nonzero discriminant in `𝔬`
need not be a unit of `𝔬`. The unique translation `h = −(a₁ − ct a₁)/n`
requires positive degree, but does not require `1/n ∈ 𝔬`, since the purely
infinite ideal is a `𝕜`-vector space.

The empty-product discriminant is `1` in degrees zero and one. A unit
discriminant makes the finite free trace pairing perfect (its matrix is
invertible), a stronger condition than a nonzero determinant over a domain.
In the critical-point application, gaps lie in `𝕜̄`, not necessarily `𝕜`;
simple critical points can have repeated critical values. In the matrix
application `M*` is the conjugate transpose, while `ct M` extracts exponent
zero entrywise; the size must satisfy `n ≥ 1` for the trace divided by `n`.
For the two-translation normal form `f(X) = f̄(X − h) + β`, the shifts
`h, β` are purely infinite. Affine conjugacy means `g = L⁻¹ ∘ f ∘ L` with
`L(X) = aX + b`, `a ≠ 0`, in the Hahn splitting field. For degree at least
two, such a `g` has ordinary algebraic-closure coefficients for some `L`
exactly when `β = h`; then one can take `L(X) = X + h` and `g = f̄`.

For a finite étale `𝒜_𝕜(Γ)`-algebra `𝖡`, its constants `𝖢_𝖡` are the elements
algebraic over `𝕜`. The reduction is `𝖡₀ = 𝖡 / Π_𝕜(Γ)𝖡`; it need not be
identified with `𝕜`. The report proves that `𝖢_𝖡 → 𝖡₀` is injective, not
that every fiber element lifts to a constant. The generic algebra is a
product of finite separable fields. Each individual map to the Hahn
splitting field selects one factor and may have a kernel on that product;
all generic maps together give an injection. The characteristic-polynomial
argument uses finite projectivity and local bases, with no global basis
assumption on `𝖡`.

In the regular-singular part of the differential-equations report,
`t = ω⁻¹` and `τ = log t = −log ω` denote actual surreal numbers.
The Euler derivation `∂_τ = −ω∂` satisfies `∂_τ(t^γ) = γt^γ`
for ordinary real `γ`. It preserves every `K_Γ` with `Γ ⊆ ℝ`,
whereas `∂ = −t∂_τ` preserves that field exactly when `Γ = {0}`
or `1 ∈ Γ`. Multiplying an Euler gauge identity by `−t` always gives
an identity in `No[i]`; interpreting both systems over the same smaller
field also requires that their coefficients and derivations stay there.

The regular-singular residual matrix `A₀` is the exponent-zero coefficient
of the Euler coefficient `A`; the corresponding `∂`-coefficient is `−tA`
and its exponent-one coefficient is `−A₀`. A Levelt resonance is a
positive real eigenvalue difference of `A₀`. Its block projection retains
the entire space of maps between the corresponding generalized eigenspaces,
not just the kernel of the homological operator. These resonances differ
from integer relations among differential phases and from the scalar
resonant coefficient at `t¹` discussed earlier in that report.

For a regular-singular system, the gauge `F` gives the constant Euler
coefficient `iD + N`, where `D` records residual frequencies and `N`
is nilpotent and commutes with `D`. The gauge `G_τ = F exp(τN)`
removes `N` after adjoining `τ`. Thus `K_ℝ`-classification retains
the nilpotent Jordan partitions at each frequency, while classification
over `No[i]` retains only frequency multiplicities. Constant intertwiners
refer to the reduced frame; morphisms of the original systems are
`F C (F′)⁻¹`. The tensor differential system of coefficients `A,A′`
has coefficient `A ⊗ I + I ⊗ A′`, rather than the matrix product
`A ⊗ A′` alone.

For smaller Euler-stable workspaces, `K_Γ(t^{a₁}, …, t^{a_k})`
means the field of rational expressions in the added monomials over
`K_Γ`; it does not denote the full Hahn field on the enlarged exponent
group. Two constant rank-one Euler coefficients `λ, μ ∈ ℂ` are
gauge equivalent over `K_Γ` exactly when `λ − μ ∈ Γ`. In particular,
their imaginary parts agree and their real parts agree modulo `Γ`.

The autonomous part of the differential-equations report uses `ð` for
an arbitrary normalized derivation with `ðω = 1`, not for the rescaled
Euler derivation. A local parameter `σ` on an ordinary complex curve
evaluates to an infinitesimal at any point reducing to its center. Formal
maps acting within these infinitesimal tuples have zero constant term;
their invertible ordinary linear part gives an inverse on the same
monad. For a simple zero, `ξ(σ) = λσ + O(σ²)`, the coefficient `λ`
is unchanged by a change of local parameter. The normalized linearizer
has `h_p(σ) = σ + O(σ²)`; its formal derivative is distinct from `ð`,
with the evaluation chain rule connecting them.

At a multiple zero of order `m+1`, `x_m = ω^(−1/m)` and
`y_ω = (log ω)/ω` are actual infinitesimals; `X,Y` are formal
variables before evaluation. The series `w_{β,C}(X,Y)` has constant
term one, and `u_{β,C} = β x_m w_{β,C}(x_m,y_ω)` is the solution.
Here `β^m = −1/(m c_{m+1})` and `C ∈ ℂ` is the ordinary constant
in the time primitive `𝔱(u) = ω+C`, after choosing `log β`.
Replacing `log β` by `log β + 2πik` relabels the same solution by
`C + 2πik ϱ`, where `ϱ` is the coefficient of `σ⁻¹` in `1/f(σ)`.
Changing the local parameter to `aσ + O(σ²)` rescales `β` to `aβ`.
Neither constant is an invariant independent of these choices.

For a real branch use the real primitive with `log |u|` and
`log |β|`; its time constant is real. On a negative branch, choosing instead
`log β = log |β| + iπ` in the complex primitive changes the constant to
`C_ℂ = C_ℝ + iπϱ`. Thus “real solution” does not mean “real complex time
constant” without fixing the logarithm convention. A simple-zero amplitude
is the ordinary coefficient multiplying `exp(λω)` in the normalized
linearizer, a different parameter from this additive time constant.

In the autonomous localization theorem, `𝔊_ξ` is the multiplicative
monomial group generated by finitely many specified scales, whereas
`K_ξ = ℂ((𝔊_ξ))` contains every series with reverse well-ordered support
in that group. Finite generation of `𝔊_ξ` does not assert finite generation
or finite transcendence degree of the Hahn field over `ℂ`. The common
normalized derivative on this field shifts each input monomial by one of
`1`, `ω⁻¹`, `(ω log ω)⁻¹`; collisions may cancel coefficients.
For every `F ∈ ℂ[Y,Z]`, normalized derivations have the same solution
collection for `F(y,ðy)=0`. Pointwise equality of their derivatives on that
collection and a uniform set-sized Hahn field bound require `F ≠ 0`.

An ordinary formal time variable `s` with formal derivative `ds/ds=1`
is not an arbitrary infinitesimal surcomplex input for the intrinsic
normalized derivation `ð`: finite surcomplex elements have infinitesimal
intrinsic derivatives. Thus formal flow identities, fine derivatives of
evaluated series, and intrinsic differential equations require their
respective compatibility statements. Current Lean formal evaluation and
fine-differentiation results do not by themselves identify these operators.

For a constant abelian variety `𝐀/ℂ`, the formal logarithm
`log_𝓕` maps its identity monad to `Lie(𝐀)(𝔪_ℂ)`; its inverse
`exp_𝓕` is evaluated only at infinitesimal Lie coordinates. It is distinct
from the scalar exponential and from an analytic uniformization by a period
lattice. The logarithmic derivative `dlog_ð` is a Lie-valued group
homomorphism with image `Lie(𝐀)(ð𝔪_ℂ)` and kernel `𝐀(ℂ)`.
The complex primitive obstruction `Obs^ℂ_ð` tests both real and imaginary
coordinates, unlike the multiplicative phase obstruction `Φ`. Defining it
on every input requires surjectivity of `ð`. The abelian image theorem and
the explicit speed threshold for `ω^(−p)v`, `p > 1`, do not.

In the critical-potential part, `ℓ_α = ω^(ω^(−α))` uses the Conway
monomial map at both levels. Each ordinal-indexed sum stops below one
fixed ordinal, so its index is a set. The monomial product `ℓ_{<α}` is
defined by summing its exponents; its logarithm agrees with the sum of
logarithms by the stated imported theorem, including limit stages.
The real powers `ℓ_α^r` use the ordered real exponential. These formulas
do not extend the Conway map to exponents in `ℂ \ ℝ`, or define complex
powers of infinite scales. A surreal exponent outside `ℝ`, such as
`−2−2ω⁻¹`, is still a valid Conway exponent; distinguish that case from
a non-real complex exponent. A critical potential is the strong sum of its increments, not
the generally nonsummable family of its partial potentials.

An exact Hahn normal form specifies every coefficient, including zeros
outside the displayed support. Prescribing coefficients only at an earlier
hierarchy of scales allows smaller remainder terms. The critical-potential
invisibility theorem concerns that latter data; it does not give two
values for one exact strong sum.

For the three limit-stage fields, distinguish inner support in the Conway
normal form of an exponent from outer support in the Hahn series itself.
`Δ₀` is a finite real span of prefix sums. Full Hahn summation allows
well-ordered outer supports in `Δ₀`, but does not add new exponents to
`Δ₀`. The first two real fields are closed under the ambient logarithm;
the third contains `ℓ_λ` but omits its logarithm `ℓ_{λ+1}`. Algebraic
closure, derivative stability, logarithm closure and solving a particular
equation are separate properties.

For the limit-stage Picard–Vessiot basis, use the right-matrix convention
`ψ(Y) = Y M_ψ`. Composition applies the right-hand automorphism first and
satisfies `M_{ψ∘φ} = M_ψ M_φ`. The action parameters `(a,b)` have law
`(a,b)·(a′,b′) = (aa′,a′⁻²b+b′)`; the upper-right matrix entry is `ab`.
In Schwarzian reconstruction, `v² ∂s = 1` is an algebraic square-root
choice. Möbius matrices lie in `GL₂(ℂ)` and act on a nonconstant solution
ratio, which ensures their denominators are nonzero. These constructions
do not require a complex logarithm or a global composition operation.

For a scale `s` with `∂s ≠ 0`, the field derivation
`∂_s = (∂s)⁻¹∂` has the same constants as `∂`; writing `s∂_s = ∂_{log s}`
when `s > 0` asserts an operator identity, not a global substitution map.
The Liouville gauge formula is algebraic for arbitrary coefficients in the
field. Its Euler kernel classification additionally requires an ordinary
real coefficient. Membership of a potential in the power-Hahn field
`ℂ((t^ℝ))` is determined by its surviving Conway exponents: the critical
family's stage `α = 1, c = 0` is still in that field.

Distinguish the ordered real surreal exponential, the strongly summed
infinitesimal Hahn exponential, finite-angle `cis`, and a chosen global
surcomplex exponential or global phase. A finite angle has ordinary period
ambiguity `2πℤ`; the canonical global phase construction uses an omnific
integer part and has a different period class. A theorem about one domain
or kernel does not define the others. See
[trigonometry](surcomplex/trigonometry/article.tex)
(`trigonometry:thm:stripexp`, `trigonometry:thm:globalexp`) and
[differential equations](surcomplex/differential-equations/article.tex).
The [automorphism-rigidity report](surreal/exponential-automorphism-rigidity/article.tex)
uses `log √(z z̄)` for `z ≠ 0`; this logarithmic modulus takes values in
`No`, not a choice of complex logarithm.

In the differential-equations report, `Obs(b)` is the purely infinite part
of a primitive of the real surreal coefficient `b`, and `Φ(a+ib) = Obs(b)`.
Thus `Obs(1) = Φ(i) = ω` but `Φ(1) = 0`. The normalized primitive `I₀`
has zero ordinary constant term; it may retain an infinitesimal part and is
not in general purely infinite. The phase multiset `Ph(A)` classifies finite
systems over `SC` up to differential gauge equivalence. Computing it from
instantaneous eigenvalues needs additional hypotheses; its existence alone
does not provide that formula or an algorithm.

Use “residue” with its definition: formal Laurent coefficient, actual local
residue at a surcomplex point, residue of an ordinary-centered cluster, or
the multivariable series/contour functional. In analytic geometry the
functionals `Res_F` and `Λ_F` agree only through the stated comparison
(`analytic:prop:residues-agree`). A coefficientwise contour integral should
retain its `H` decoration and its ordinary parameter path; it is not defined
by fine-topological Riemann-sum convergence.

## Automorphism structures

The [field-automorphism report](surcomplex/surcomplex-field-automorphisms/article.tex)
uses `K = No(i)` and the proper-class exponent group `Γ = (No,+,<)`;
every individual normal-form support remains a set. Its `Aut(K)` is a
collection of class maps, not an NBG class containing their graphs.
Factorizations describe individual maps and composition. A finite action
is encoded by one class relation with a finite index set; fixed-field
identities for all class automorphisms are interpreted pointwise.

| Preserved structure | Meaning |
|---|---|
| Real axis | Setwise preservation of `No`; fixing it pointwise is stronger. |
| Valuation ring | `α(𝒪)=𝒪`, allowing an ordered reindexing `v(αz)=τ(vz)`. |
| Individual values | `v(αz)=v(z)` for every nonzero input. |
| Leading terms | `v(αz−z)>v(z)`, the report's `1`-automorphism condition. |
| Norm or modulus | Exact preservation forces identity or conjugation; equivariance `|αz|=σ(|z|)` allows other real-axis automorphisms. |

Strong additivity preserves summable families and their Hahn sums; a strong
automorphism requires this for both directions. It is separate from
coefficient linearity and fine continuity. A strong field map is determined
by its coefficient and monomial images. Monomial images alone determine it
when coefficients are fixed; the Taylor motions `Φ_d` show why that condition
matters. Residue action `ρ` also need not be the restriction to the embedded
coefficient field, which can move by infinitesimals.

The decomposition `α=u D_χ M_{ρ,τ}` applies the rightmost map first and uses
`χ(g)=lc(α(t^{τ⁻¹g}))`. This character is indexed after undoing the value
action. The additive-group decomposition one level deeper permits arbitrary
order permutations of exponents, while a field monomial map needs an
**additive** order automorphism. The coefficient functional `ℓ(g)=[g]₀`
is defined even for infinite exponents and is not a standard-part map there.

The fine derivative can take any value in `K`; “no `K`-valued derivative”
excludes infinite values too. It is tested by punctured neighborhoods,
not by a set-indexed cofinal sequence in the full surreal topology.
Generic exponential rigidity acts on the actual valuation image `w(Fˣ)`;
surjectivity onto a larger written codomain must be stated separately.

## Radii, modulus, and order-theoretic terminology

An **ordinary radius** `R > 0` specifies a domain for complex coefficient
functions: increasing `R` enlarges that domain. A **valuation threshold**
`ρ ∈ Γ` specifies `v(z−a) > ρ` or `≥ ρ`: increasing `ρ` shrinks that ball.
In a rank-one norm one may convert by `R_v = exp(−ρ)`. An
**ordered-modulus radius** `r ∈ No_{>0}` specifies `|z−a| < r` and is yet
another type of datum. The ordinary modulus, the surreal-valued modulus, and
`|·|_v` must not be silently substituted for one another. A valuation shell
`v(z−a) = ρ` is not asserted to be the topological boundary of a valuation
ball. See [dynamics](surcomplex/dynamics-and-normal-forms/article.tex)
(`dyn:subsec:radius`) and
[polynomial algebra](surcomplex/polynomial-algebra/article.tex)
(`polynomial:subsec:conventions`).

The computer-algebra convention `O_v(β)` means an error with valuation at least
the **exponent** `β`. Thus for `v(t) = 1`, write `O_v(7)`, not `O_v(t^7)`.
The [Markov report](surreal/markov-generators-at-every-scale/article.tex) also
allows `β = +∞`: with `v(0) = +∞`, the bound `O_v(+∞)` means exactly zero,
entrywise for matrices.
Other reports may instead define an ordinary asymptotic `O(t^7)`; quote its
local definition before translating the notation.

In [expanding polynomial dynamics](surcomplex/expanding-polynomial-dynamics/article.tex),
`σ` is the one-sided symbolic shift and `κ = v(q) > 0` is the valuation
gain of an inverse branch. Its error ideal `I_κ` consists of values with
`v(h) > nκ` for every ordinary `n`. This contrasts with the small-divisor
rate `σ(λ)` and the divisor thresholds in local normal-form dynamics.
An order unit can exist in a group of rank greater than one; the Cantor
description concerns the itinerary space and does not identify the ambient
valuation as rank one.

The dynamics report's ordinary small-divisor growth rates measure complex
coefficient sizes, even when every nonzero divisor has Hahn valuation zero
(`dyn:rem:invisible`). Its local letters `σ`, `τ`, and `log Θ` apply one rate
construction to different divisor families; they are not equal numbers by
notation. “Cofinality” in the entire-functions report is cofinality of the
ordered value group, and an **order unit** has cofinal integer multiples.
Countable cofinality does not by itself assert the existence of an order unit
(`ent:rem:one-name`).

For an exact diagonal unitary multiplier in the dynamics report, the
**angular rank** is `r_ang = dim_ℚ span(1,θ₁,…,θ_d) − 1`, where
`λ_j = exp(2πiθ_j)`. It is unchanged by changing the angle representatives
and is independent of the ordered rank of the Hahn exponent group `Γ`.
Under nonresonance and finite divisor rate `τ`, the universal coefficient
radius lies between `R exp(−r_ang τ)` and `R exp(−τ)`. It equals `R` when
`τ = 0` at every angular rank; the unresolved higher-rank optimum concerns
`0 < τ < ∞`. These are ordinary coefficient radii, not valuation thresholds.
In the colored-tree proof, `η_v ∈ S` denotes a vertex's Hahn input label,
whereas `s_v` is its positive integer subtree weight; they live in different
groups. The fixed complexity `m` may depend on the coefficient exponent,
and its finite prefactor is not bounded uniformly in `m`.

A sequence whose **range is cofinal** need not tend cofinally to infinity:
it can keep returning to one small value. An eventual growth estimate must
state the latter condition. The entire-functions growth barrier
(`ent:lem:growth-barrier`) requires eventual cofinal growth and gives a
counterexample to the weaker range condition.

Finally, distinguish ordinary ordinal arithmetic from Hessenberg natural
operations `⊕`, `⊗` and from surreal field operations. On embedded ordinals,
the field operations agree with the natural operations, while ordinal
concatenation still uses ordinary ordinal addition. Birthday `b(x)` is the
canonical sign length of a **value**, not the rank of an arbitrary form
representing it. These conventions are spelled out in both
[birthday](surreal/gonshor-product-birthdays/surreal_product_birthdays.tex)
[reports](surreal/gonshor-laurent-birthdays/article.tex) and in the graph report.
In [nonabelian support](surcomplex/nonabelian-support/article.tex), “positive”
means positive Hahn exponents, not positive-definite matrices; in spectral
and quaternion algebra those order notions have their separately stated
meanings. The [computer-algebra report](foundations-and-computation/computer-algebra/article.tex)
(`cas:sec-objects`) treats these distinctions as representation requirements,
not interchangeable spellings for software constructors.
