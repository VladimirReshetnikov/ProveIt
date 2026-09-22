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

Use “residue” with its definition: formal Laurent coefficient, actual local
residue at a surcomplex point, residue of an ordinary-centered cluster, or
the multivariable series/contour functional. In analytic geometry the
functionals `Res_F` and `Λ_F` agree only through the stated comparison
(`analytic:prop:residues-agree`). A coefficientwise contour integral should
retain its `H` decoration and its ordinary parameter path; it is not defined
by fine-topological Riemann-sum convergence.

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
Other reports may instead define an ordinary asymptotic `O(t^7)`; quote its
local definition before translating the notation.

The dynamics report's ordinary small-divisor growth rates measure complex
coefficient sizes, even when every nonzero divisor has Hahn valuation zero
(`dyn:rem:invisible`). Its local letters `σ`, `τ`, and `log Θ` apply one rate
construction to different divisor families; they are not equal numbers by
notation. “Cofinality” in the entire-functions report is cofinality of the
ordered value group, and an **order unit** has cofinal integer multiples.
Countable cofinality does not by itself assert the existence of an order unit
(`ent:rem:one-name`).

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
