# Differential Algebra and Differential Equations over the Surreal and Surcomplex Numbers

**The finite-primitive criterion, the phase obstruction, and support-certified
coordinate systems**

A merged research report, 189 pages, built from eleven manuscripts. Everything
in this directory other than `article.tex`, `article.pdf` and this README is
preserved source material.

```
article.tex                        the merged report, standalone LaTeX with an internal bibliography
article.pdf                        the compiled 189-page report
README.md                          this guide
11-autonomous-dynamics-sources.md  member 11's literature and repository-review log, unmodified
code/                              the verification programs and build scripts of the eleven
                                   source packages (19 files), unmodified
data/                              their recorded verification, build and requirement
                                   records, and member 13's manifest (31 files), unmodified
```

Every label in `article.tex` carries the prefix `diff:`; the labels added with
members 11, 12 and 13 carry the sub-prefixes `diff:aut:`, `diff:rs:` and
`diff:cp:`. The current text has 763 valid label definitions, all preserved
from the merged upstream text. The earlier count included the malformed
placeholder described in the correction record below.

The current proof review covers the earlier scalar, matrix, workspace and
coordinate chains and all of the regular-singular main text, Sections
23–28: the Euler frame, support and resonance arguments, classification,
logarithmic repair, forcing, examples, workspaces and finite procedure.
The revisions expand the proof steps, distinguish the derivative frames
and field extensions, illustrate the normalizations, and prove the forced
degree bound sharp. The finite procedure now states its effective
coefficient requirements; complex algebraic coefficients suffice.
The autonomous review now covers Sections 29–30: normalized derivations,
formal evaluation, projective reduction, simple and multiple zeros, and
completeness of the curve-realization list. It expands the support,
local uniqueness and forced-scale arguments, makes the properness
comparison set-sized, and gives explicit quadratic and pure monomial
formulas. Branch choices and the time parameter's first differing scale
are stated explicitly. Uniform localization, derivation independence,
later autonomous proofs, remaining imports and source reconciliation
are still pending; scope and validation are recorded in the collection's
[review record](../../REVIEW.md).

## What the report is

Eleven independently written manuscripts developed the theory of the
Berarducci–Mantova derivation `∂` on the surreal class field `No`, normalized
by `∂ω = 1`, and of its unique extension to the surcomplex field `No[i]`.
This report is their **union**, not a selection from them. Seven of them share
a twelve-item spine of scalar and workspace theory; the eighth joined later and
carries the finite **matrix** stratum — Part III; the ninth and tenth joined
next, together: member 12 carries the **regular-singular** stratum — Part V —
and member 11 a **first-order autonomous** nonlinear stratum — Part VI; the
eleventh, member 13, joined last and carries a **second-order** stratum along
the transfinite log-atomic tower — Part VII.

| Part | Content |
|---|---|
| I | Foundations: conventions, the imported derivation, smallness, the vocabulary discipline |
| II | The scalar theory over `No[i]` |
| III | Finite matrix systems and the differential phase spectrum |
| IV | Workspaces: Laurent, rational, Hahn, set-sized |
| V | Regular-singular systems over real-exponent Hahn workspaces (member 12) |
| VI | Autonomous first-order equations: curves, derivation independence, abelian logarithmic derivatives (member 11) |
| VII | Transfinite critical potentials: second-order equations at every logarithmic depth (member 13) |
| VIII | Coordinate differential equations in common-domain Hahn rings |
| IX | Computation, formalization, and the register of non-claims |
| X (App. A–E) | Positive-support calculus, notation and concordance, provenance, verification records, build |

Part VII was inserted after Part VI, not beside the missing oscillator in
Part II, so that Parts I–VI and Sections 1–34 keep their numbers: other reports
of the collection cite Parts V and VI of this one by number. The former Parts
VII–IX are now VIII–X, and Sections 35–44 are now 43–52.

The organizing identity is exact:

```
{ ∂y/y : y ∈ No[i]ˣ }  =  No + i·A ,      A := ∂m = ∂O
```

where `O` is the class of finite surreals and `m` its ideal of infinitesimals.
So `∂y = (a + ib)y` has a nonzero surcomplex solution exactly when `b` has a
**finite** surreal primitive. Two things about that identity carry the whole
subject:

* the two printed forms `No + i·∂m` and `No + i·∂O` agree **only through a
  proved lemma** (`∂O = ∂m`), never as notational variants; and
* `A` is a **strict** subclass of `m`. The coefficient `ω⁻¹` is infinitesimal
  while its primitive `log ω` is infinite, so `∂y = i·ω⁻¹·y` has only the zero
  solution. Collapsing `∂O` to `O` would turn the criterion into "`b`
  infinitesimal" and make that equation solvable; the first eight sources all
  refute exactly that, and Proposition 16.9 shows the strictness is *sharp*: `A` is
  exactly the class of scalar perturbations that preserve every phase.

From the criterion the report derives: the purely infinite part of the
accumulated phase as an `R`-linear surjection onto the purely infinite
surreals, a complete gauge invariant and the middle term of a four-term exact
sequence; a sharp support threshold over real-exponent Hahn fields with a
counterexample proving it does not globalize by valuation; power and
iterated-logarithm thresholds at `p > 1` at every finite depth; a decision
procedure for rational coefficients (`deg Q − deg P ≥ 2`); the pointwise
maximality of the strip `No + i·O` as the domain of any derivation-compatible
exponential, hence no global one; nonexistence of a nonzero solution of
`∂y = iy` or `∂²y + y = 0`, by three independent proofs; the complete
constant-coefficient and constant-matrix classification, in which only *real*
characteristic roots contribute; a triangular fundamental-matrix criterion with
its insufficient trace test; exact resolvents with factorially divergent Hahn
solutions and exact residual certificates; two different differentially stable
set-sized workspace constructions; and five Picard–Vessiot extensions with
differential Galois tori — at the cost, in the real form, of the `H`-field
ordering rule.

### The matrix stratum (Part III)

Every `∂y = Ay` with `A` an ordinary finite matrix over `No[i]` is gauge
equivalent to `i·diag(∂P₁, …, ∂Pₙ)` with each `Pⱼ` purely infinite, and the
**multiset** `Ph(A) = {Pⱼ}` is a complete invariant of differential
equivalence (Theorem 15.9). The trace test of Proposition 14.2 sees only its
**sum**, which is exactly why it is insufficient.

For a Hermitian `H` the multiset is computed from ordinary algebra
(Theorem 16.5):

```
Ph(iH) = { Obs(λ₁(H)), …, Obs(λₙ(H)) }
```

— integrate the algebraic eigenvalues, keep the purely infinite parts of the
primitives. **No commutation and no spectral gap is assumed.** The proof does
*not* claim that diagonalization commutes with differentiation: the connection
term `W*∂W` is still there, but a unitary gauge is entrywise finite, so that
term lands in `Mat(A + iA)`, which is precisely the kernel `Obs` annihilates.

Consequences: gap-free finite-primitive perturbation invariance; the exact
kernel count `dim_C ker = #{ j : λⱼ(H) ∈ A }`; existence for *every* forcing;
normalized non-Abelian integration (`∂W = AW` has a unique unitary solution
with `st(W) = I` when `A* = −A` and every entry has a finite primitive); the
complete cone of positive invariant metrics; the real rotation-block descent;
a positive Ermakov–Pinney existence/uniqueness dichotomy; an exact Hahn
expansion for the oscillatory Airy equation; polynomial and rational first
integrals from phase resonance; and the phase-lattice Picard–Vessiot torus of
an arbitrary finite system, which is the diagonal Theorem 21.12 applied through
the normal form rather than new Galois theory.

**Classification and explicit computation have different scopes.** The phase
multiset classifies every finite system over `SC`, including non-Hermitian
ones. The formula from instantaneous algebraic eigenvalues is proved for
coefficients `iH` with `H` Hermitian; Example 16.10 refutes its unrestricted
extension. Its nonnormal `A` has eigenvalues `±i` but a fundamental matrix
already in the base field, hence phase multiset `{0, 0}` rather than the
incorrect `{ω, −ω}`. Part V supplies another explicit formula for the
power-Hahn regular-singular class. Part III's general normal form and
inhomogeneous existence use an **additional imported input**: splitting monic
scalar operators into first-order factors and surjectivity of nonzero scalar
operators, transferred from the transseries field. The first seven manuscripts
do not use this import. Every inhomogeneous existence statement in
Part III comes from that import and not from the rank-one criterion; the
register of non-claims says so at items N22, N24 and N53.

### The regular-singular stratum (Part V, member 12)

Write `t = ω⁻¹`, `τ = log t = −log ω`, and `∂_τ = −ω∂` — the rescaled
derivation `∂_s` at `s = τ`, which acts on real-exponent Hahn series by
`t^a ↦ a t^a` and *reverses* the `H`-field sign rule (Warning 23.4). Part V
treats `∂_τ y = A y`, that is `∂y = −tAy`, with `A = A₀ + A₊`, an ordinary
complex residual matrix `A₀` and a perturbation `A₊` of positive order in
`K_R = C((t^R))`, with arbitrary well-ordered real support (Definition 23.5).
The unknown ranges over all of `No[i]ⁿ`.

* **Normal form and finite resonance data** (Theorems 24.5, 24.7). A unique
  support-controlled Hahn–Levelt gauge brings `A` to `A₀° + finitely many
  resonant terms`, supported on the Levelt resonances `λ − μ ∈ R_{>0}`. Only
  the finitely many coefficients lying on ordered words that sum to a
  resonance matter — even when the support accumulates below a resonance —
  and the resonant terms are polynomials of bounded degree in them.
* **Spectral selection** (Theorem 25.3). There is an explicit
  `G_τ ∈ GL_n(K_R[τ])` with `∂_τ G_τ = A G_τ − G_τ iD`, `D` the imaginary parts
  of the eigenvalues of `A₀`. Every surcomplex solution is `G_τ c` with
  `c ∈ ker D`, so the solution space has dimension equal to the algebraic
  multiplicity of the **real** eigenvalues of `A₀`, and every solution already
  lies in `K_R[log t]ⁿ`.
* **Two classifications** (Theorems 25.7, 25.9). Over `K_R`: residual
  frequencies plus nilpotent Jordan partitions. Over `No[i]`: the multiset of
  residual frequencies alone; morphism and tensor dimensions exactly.
* **The phase spectrum** (Proposition 25.12). `Ph(−tA) = {(Im λⱼ)·log t}` —
  one explicit **non-Hermitian** sector of Part III's phase spectrum, with an
  explicit gauge, reached **without** the imported splitting/surjectivity
  theorem of Part III and without the surjectivity clause of the derivation.
  Remark 25.13 records, as an observation of this merge that neither source
  states, that in this class the naive eigenvalue recipe also gives the right
  answer; Example 16.10 lies outside the class.
* **Logarithms and forcing** (Theorems 26.1, 26.3, 26.5). The Hahn solution
  space is `F ker N₀`; one actual logarithm repairs every nilpotent resonance,
  with Galois group `(C,+)`; an exact finite-dimensional Hahn obstruction
  sequence, and a solution in `K_R[log t]ⁿ` for every forcing in `K_Rⁿ`.
* **Workspaces and the boundary** (Theorem 28.1, Proposition 28.4). Finitely
  many real monomials and one logarithm suffice over any `K_Γ`, `Γ ⊆ R` (no
  `1 ∈ Γ` needed, since `∂_τ` preserves every `K_Γ`); in rank one this is
  exactly the resonant normal form of Theorem 19.3 (Remark 28.2). The
  infinitesimal coefficient `i/log ω` has no solution, so the power-Hahn
  hypothesis cannot be dropped.
* **An exact finite procedure** for finite rational supports and complex
  algebraic matrix entries (§28.3), or another coefficient presentation
  supplying the stated exact operations. Its reduced set of weights is
  closed under the recursion's dependencies. This is not an oracle algorithm
  for indirectly described supports or arbitrary named complex constants.

### The autonomous stratum (Part VI, member 11)

Part VI is the only part stated for a **class of derivations**: every
*normalized* derivation `ð` — the Berarducci–Mantova clauses without
surjectivity (Definition 29.1). Everything else in the report remains relative
to the one fixed `∂`.

* **Realization classification** (Theorem 30.1). For a constant meromorphic
  vector field on a smooth projective complex curve, every nonconstant
  surcomplex solution reduces to a zero of the field. A simple zero
  contributes solutions exactly when its eigenvalue is a **negative real**
  number — nonreal eigenvalues are excluded even with negative real part —
  and a zero of order `m+1 ≥ 2` contributes exactly `m` one-parameter families,
  explicit series in `ω^(−1/m)` and `(log ω)/ω`, with no hidden
  beyond-all-orders parameter.
* **One finite-scale field; derivation independence** (Theorems 31.1, 31.4).
  All solutions lie in one set-sized Hahn field with a finitely generated
  monomial group; for every `F ∈ C[Y,Z]` the solution set of `F(y, ðy) = 0` is
  the same for every normalized derivation, and on it all of them agree. This
  reproves the first-order parts of Corollaries 8.8 and 8.11 for every
  normalized derivation (Corollary 31.7), and nothing more.
* **Projective obstructions** (Theorem 33.3). `(ðy)² = Q(y)` with `Q`
  squarefree of degree `≥ 3` has only the constant roots of `Q`; both
  hypotheses are needed.
* **Abelian varieties** (Proposition 33.7, Theorem 33.8, Corollaries 33.10,
  33.11). For a constant abelian variety, the formal logarithm splits the
  identity monad, and the logarithmic-derivative image is exactly
  `Lie(A)(ð𝔪_C)` — for `ð = ∂`, the *whole* Lie coordinate must have finite
  primitives, unlike the multiplicative group, where only the imaginary part
  is constrained. With surjectivity: a finite-primitive criterion and the
  speed threshold `p > 1`.

These lift, for this class only, the report's former non-claims N21 and N25
and the remark after Corollary 8.11 that it "is not a general nonlinear
solvability theorem"; the old wording is kept, amended in place.

### The transfinite critical-potential stratum (Part VII, member 13)

Write `ℓ_α = ω^(ω^(−α))` for the ordinal log-atomic tower (`ℓ_0 = ω`,
`ℓ_{n+1} = log ℓ_n`, continued through every ordinal; its derivative formulas,
limit stages included, are **imported** from Aschenbrenner–van den Dries–van der
Hoeven, Proposition 35.3), `ℓ† = ∂ℓ/ℓ`, and

```
Q_α = ¼ Σ_{β<α} (ℓ_β†)² ,      Q_{α,c} = Q_α + c (ℓ_α†)² .
```

* **Transfinite classification** (Theorem 38.1). For every ordinal `α` and
  real `c`, `∂²y + Q_{α,c} y = 0` has a two-dimensional solution space in `No`
  (over `R`) and in `No[i]` (over `C`) when `c ≤ ¼`, and only `y = 0` when
  `c > ¼`. The bases are single Conway monomials, `Q_{α,¼} = Q_{α+1}`, and the
  proof at a limit ordinal is one summable triangular calculation (Lemma 36.1,
  Theorem 36.2), not a skipped induction step.
* **The missing oscillator** (Remark 37.5, an observation of this merge with
  its proof). One gauge identity (Lemma 37.2) reduces the family to the Euler
  operator `s∂_s` at the scale `s = ℓ_α`; the same identity at the scale
  `s = e^ω` turns Corollary 8.8's `∂²y + b²y = 0` into the same Euler problem
  with `c = ¼ + b²`. In every supercritical case the obstruction is an infinite
  accumulated phase — `|b|·ω` for the oscillator, `√(c−¼)·ℓ_{α+1}` at stage `α`
  (Corollary 37.1). That is the precise sense in which the `c > ¼` side
  generalizes the missing oscillator; the oscillator is not a member of the
  family, and the family is not a corollary of the oscillator.
* **Invisibility** (Theorem 39.2). For every *set* of ordinals, two positive
  potentials agree beyond all those scales while their solution dimensions are
  2 and 0; there is no all-ordinal potential (Proposition 39.5).
* **Limit-stage field jump** (Theorem 40.4, Proposition 40.5). At every
  nonzero limit ordinal `λ`, three nested, `∂`-stable, real closed Hahn fields
  `H_{Δ_0} ⊂ H_{Δ_1} ⊂ H_{Δ_2}` contain `Q_λ` and have solution dimensions
  0, 1, 2; the first two are closed under `log`, and what is missing is first an
  exponential, then a primitive.
* **Borel Galois group** (Theorem 41.2). Over `K_{Δ_0}` the solution field
  `K_{Δ_0}(u_λ, ℓ_λ)` has differential Galois group the upper triangular Borel
  subgroup of `SL_2(C)` — the only non-commutative differential Galois group in
  the report; over `K_{Δ_1}` what remains is `(C,+)` (Corollary 41.3).
* Also: a Riccati form, an exact Schwarzian reformulation (Corollary 42.2), the
  first limit stage `λ = ω` in normal form (Example 42.3), and, as observations
  of this merge, the Euler operator as a constant-coefficient operator at the
  scale `log s` (Remark 37.4), stage 0 as a regular-singular system of Part V
  (Remark 38.4), and the explicit unique Pinney amplitude and canonical phase of
  a supercritical member (Remark 38.5; its uniqueness and phase statements use
  Part III and that part's import).

Part VII uses neither surjectivity of `∂` (except in one flagged Riccati
remark) nor Part III's imported splitting theorem. It is relative to the one
fixed `∂`; nothing is claimed for Part VI's class of normalized derivations.

A **deliberately separate** half treats *coordinate* differential equations in
fixed-common-domain Hahn rings `Hol(U)((t^Γ))`: existence, uniqueness, support
certificates, variation of constants, a Liouville determinant identity,
monodromy valued in `GL_d(K_Γ)`, and a polynomially nonlinear initial-value
theorem, all on strong summability and an **ordered**-word support lemma that
Appendix A proves in full. The two halves share notation and almost nothing
else; several theorems are true for one operator and false for the other on the
same printed equation, and the report keeps their types apart rather than
flattening them.

### The objects called "phase"

The single most important thing to carry away from the merge. The sources use
the word "phase" for several different objects, one of which is not an angle at
all. The report fixes one name and one symbol per object and uses them without
exception (Convention 5.1, Table 2):

| Name | Symbol | Lives in | What it is |
|---|---|---|---|
| finite angle | `θ` | `O` | the argument of `cis`; the *whole* angle of a unit, finite by theorem |
| infinitesimal phase residue | `η` | `m` | what remains after factoring out the constant ordinary unit complex number `c` |
| accumulated phase | `B` | `No` | a primitive of the imaginary coefficient; **not** an angle; obstructed exactly when its purely infinite part is nonzero |
| differential phase spectrum | `Ph(A)` | multisets in `P` | the `n` accumulated obstructions of a finite matrix system, as a multiset; the complete gauge invariant |

`Φ(i) = ω` and `Φ(i/ω) = log ω` are purely infinite surreals, not arguments
of anything. "The phase of the solution is `log ω`" is meaningless; "the
accumulated phase of the coefficient `i/ω` is `log ω`, which is infinite, so
there is no solution" is the theorem.

Here `Obs` acts on real surreal coefficients, and `Φ(a+ib) = Obs(b)`.
In particular `Φ` vanishes on `No`, whereas `Obs(1) = ω`. The normalized
primitive `I₀` has zero ordinary constant term and takes values in `P ⊕ m`;
only its purely infinite part is the obstruction.

The eighth manuscript writes `Ψ` for the map `b ↦ pp(B)` with `∂B = b`. That is
**exactly** the report's `Obs`, so no fourth symbol was introduced; what is new
is the multiset. (Adopting `Ψ` would have collided anyway: the letter already
appears once here, in Corollary 11.4, as a placeholder for a putative
derivation-compatible exponential that is proved not to exist.) The word **"spectrum"** is itself a hazard: `Ph(A)` is a
multiset of purely infinite *surreals* — not the algebraic eigenvalue list that
`docs/surcomplex/spectral-theory/` calls a spectrum, not a set of angles
(`cis` is defined on `O` only, and a nonzero member of `P` is infinite), and
not a prime spectrum of a ring. Warning 5.2 states all three separations.

The report also uses **no symbol `J`** (the sources use that letter for three
unrelated objects, the eighth uses it for the rotation generator, written
`R` here, and member 12 for a Jordan form, written `A₀°` here), and reserves
`U` for an ordinary complex domain, writing `T` for a transcendental
differential generator and `W` for a unitary matrix. Convention 15.5 fixes the
rest of Part III's alphabet: `H` Hermitian, `G` a gauge matrix, `M` a
horizontal metric, `Π` the additive phase lattice in `P` (because `Λ` is
already the integer relation lattice).

Members 11 and 12 brought three further hazards, each resolved by renaming in
the new material (Conventions 23.6 and 29.3, Warnings 23.7, 23.8 and B.1):

* member 12's **"phase labels"** `b = Im λ` are ordinary real numbers, none of
  the phase senses above; they are called **residual frequencies**, and the
  frequency `b` corresponds to the phase `b·log t`;
* **"resonance"** now has three senses — Levelt resonance `λ − μ > 0`
  (Part V only), phase resonance (integer relations among phases, Theorem
  17.8), and the single resonant coefficient `[t¹]f` (Theorem 19.2) — and
  every use is qualified;
* member 11's derivation `D` ranges over a *class*; it is written `ð` so that
  every `∂`-statement elsewhere stays visibly about the one fixed derivation,
  and its curve parameter `t` is written `σ` so that `t` stays the number
  `ω⁻¹`. Member 12's `δ = −ω∂` and `ℓ = log t` are written `∂_τ` and `τ`.

Member 13 brought one more hazard and several letter collisions, resolved in
the new material (Convention 35.1, Warning 35.2, Warning B.1). Its `𝔪(x)` is
the Conway monomial map `ω^x`, while `𝔪` here is the ideal of infinitesimals;
its `θ` for an infinitesimal primitive of an angular rate is sense (b), `η`
here; its potentials `q` are `Q` (here `q` is the rank-one coefficient); its
`U`, `W`, `Φ`, `B(C)`, `σ` and `𝒮` are `u`, `Wr`, `Y`, `Bor_2(C)`, `ψ` and `Sch`;
its coordinate `T` is a scale `s`, with the existing rescaled derivation `∂_s`
and no new operator symbol; and "Borel" there means the algebraic subgroup of
`SL_2`, unrelated to the Borel summation that item N37 disclaims.

The concordance (Warning B.1) previously said that `D` is used for no operator
on `No` or `No[i]`; that was inaccurate — Proposition 18.1 abbreviates
`∂|_{C((t))}` as `D` — and it now lists every use truthfully. No label or
statement changed with that correction.

## Where it came from

Eleven source archives. Among the first seven, three pairs of archive filenames
collided, differing only by a trailing marker, so the mapping from archive name
to manuscript is recorded here because it is not recoverable from the
filenames.

| id | original archive | manuscript |
|---|---|---|
| 01 | `surcomplex_differential_equations` | `01-thresholds-and-galois-tori.tex` |
| 02 | `surcomplex_differential_equations` (second) | `02-word-lemma-and-nonlinear-ivp.tex` |
| 05 | `surreal_differential_algebra` | `05-logarithmic-derivative-image.tex` |
| 06 | `surreal_differential_algebra` (second) | `06-finite-primitive-and-oscillation.tex` |
| 07 | `surreal_differential_algebra` (third) | `07-exact-sequence-and-rational-exponents.tex` |
| 08 | `surreal_differential_equations` | `08-coherent-ivp-and-general-resolvent.tex` |
| 09 | `surreal_intrinsic_differential_calculus` | `09-bm-bridge-and-derived-smallness.tex` |
| 10 | `surcomplex_phase_spectrum` | `10-hermitian-phase-spectral-integral.tex` |
| 11 | `surreal_autonomous_dynamics` | autonomous dynamics (Part VI) |
| 12 | `surcomplex_regular_singular` | regular-singular spectral selection (Part V) |
| 13 | `surreal_transfinite_critical_potentials` | transfinite critical potentials (Part VII) |

Members 01–09 are pinned to `VladimirReshetnikov/Surreal` at commit
`e260237db9b71da8b74a0c13c8e6355119091100`; member 10 joined later and is
pinned to the later revision
`aa846271b4dcae2c055b216126a87210292ec19b`; members 11 and 12 joined next,
together, and are pinned to `a3124af79f66b8b9c196d76b4cbc5ac3938907c4`;
member 13 joined last and is pinned to
`048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`, at which this report's
`article.tex` was byte-identical to the one it was merged into. The
archive name of member 11 is misleading on two counts: its field is `No[i]`
(with real corollaries), and its "dynamics" are flows of autonomous
differential equations, not iteration of maps — it is unrelated to
`docs/surcomplex/dynamics-and-normal-forms/`. The first seven share a
twelve-item
spine: unique complexification, smallness, infinitesimal exp/log, polar
decomposition, the normalized primitive, the rank-one criterion, the
obstruction sequence and gauge form, no oscillator, no global exponential, the
constant-coefficient classification, set-sized localization, an oscillatory
Picard–Vessiot extension.

All seven prove the first six and the eighth and ninth. The rest are proved by
most but not all: the gauge normal form is absent from three members and the
exact sequence from a fourth; the constant-coefficient classification is absent
from one, which explicitly declines it, and its matrix corollary from two
others; and at least five prove each of the last two. Whatever is shared is
printed **once**, and nothing in the article rests on a member that does not
prove what it is cited for — the provenance appendix records this member by
member.

Member 10 is different in kind. It does not reprove the spine; it cites it,
names the gap this report's own scope ledger had recorded — no classification
of arbitrary nontriangular matrix systems — and closes the Hermitian half of
it. Where it reproves something already here (the convexity and strictness of
`A`, the exact logarithmic-derivative image, the saturation of the relation
lattice), the report records the agreement and cites, rather than printing the
statement twice.

### What each contributed uniquely

* **01 — thresholds and Galois tori.** The boxed exact image; the gauge
  *uniqueness* theorem and the rank-one tensor corollary; the sharp support
  threshold `min supp(b) > 1` with strictness at exponent 1 and the
  valuation-insufficiency pair `i/(ω log ω)` against `i/(ω (log ω)²)`; the
  upper-triangular criterion with its descending recursion, the Jacobi trace
  test and the `diag(i,−i)` counterexample; the diagonal phase torus with the
  saturated integer lattice and the `(i, 2i)` / `(i, √2 i)` separation; the
  formal oscillator in complex and real rational form; the non-summability of
  the exponential series at `ω`; the phase-independent no-global-exponential
  corollary; the "at most one, not none" warning; the NBG class hygiene; the
  coefficient-domain tiering contract.
* **02 — word lemma and nonlinear IVP.** The entire coordinate half: the
  common-domain ring with its explicit disowning of both the shrinking-radius
  germ ring and the full formal ring; the linear fundamental-matrix theorem
  with uniqueness among *all* Hahn-coherent matrices; the Liouville identity;
  the negative-leading-exponent proposition and the nilpotent counterexample
  bounding it; the nonlinear theorem with no common degree bound; monodromy in
  `GL_d(K_Γ)` and the residue invisible to ordinary monodromy; the two-scale
  noncommuting computation `X₁₁ = z³(NM/6 + MN/3)` refuting the naive
  exponential; `y = t/(1−tz)`, coherent on all of `C` yet poled at `z = ω`;
  the cross-category pair (`ε = ω⁻¹` permitted for `D_z`, prohibited for `∂`);
  the three-promise separation; the strong Laurent resolvent; the
  four-category table; and the from-scratch proof of the ordered-word lemma.
* **05 — logarithmic-derivative image.** The rational decision criterion and
  its raising-rather-than-reporting contract; the order-theoretic structure and
  convexity of the bounded-primitive ideal; the countable-stage differential
  Hahn hull with the monomial criterion, the real-group criterion, the `Q√2`
  counterexample, and "differentiation closure is not integration closure";
  the analytic coefficient interface with coefficientwise linear naturality and
  the total-derivative chain rule.
* **06 — finite primitive and oscillation.** The base skeleton; the strip
  theorem with *pointwise* maximality; the character-independent differential
  defect; products, duals and no finite-order obstruction; the direct-sum
  decomposition; the summary table of distinguishable situations; the
  factorially divergent forced oscillator with its closed residual and
  anti-topological disclaimer; and the theorem that oscillation cannot retain
  the `H`-field rule.
* **07 — exact sequence and rational exponents.** The explicit `C((t^Q))`
  workspace chapter with the exact derivative and logarithmic-derivative
  images, the single resonant coefficient, the resonant normal form, and the
  workspace-versus-ambient discussion; the derivative taxonomy including the
  fine order-field derivative and the `fin`/`pp` proof that a fine derivative
  does not determine an intrinsic one; the change-of-scale observation; the
  two-derivative chain rule with *derived* summability; the Rota–Baxter
  correction to integration by parts; the `ω`-series composition bridge; the
  terminating finite inverse of `∂ − i` on `C[ω]`; the union-of-fields
  anti-lemma; "return a reason, not just a failure flag".
* **08 — coherent IVP and general resolvent.** The resolvent over a general
  real-exponent `K_Γ` with its substantive hypothesis; the beyond-all-orders
  ambiguity of the factorial solution; the valuation test for finite phase; the
  negative-valued coefficient that destroys coherence, and the rescaling that
  resolves it; "the same printed equation under different derivatives"; the
  Riccati example with an entire coefficient family; the oscillatory extension
  proved Picard–Vessiot via the absence of proper differential ideals in the
  Laurent ring; the anti-Banach disclaimer; the certificate table; and the rule
  that a truncation must record the *type* of omitted information.
* **10 — Hermitian phase spectral integral.** The whole of Part III: matrix
  gauge equivalence and the complete phase normal form, with the differential
  phase spectrum as its complete invariant; the imported splitting and
  first-order surjectivity input with its transfer; existence for every forcing
  and the exact kernel dimension; the canonical phase projectors and the
  refined trace identity `Φ(tr A) = Σ m_P · P`; the complete horizontal metric
  cone with its anti-Lyapunov example (a positive invariant metric of scale
  `e^(−2ω)` for printed coefficients whose ordinary solutions grow) and the
  unitary normal form; the attained min–max, the entrywise Weyl bound and the
  bounded-gauge estimate; the spectral–integral theorem with gap-free
  perturbation invariance and its sharpness; the two deliberate boundary
  counterexamples (the nonnormal `±i` system, and `0 ↦ ω⁻¹` moving the phase
  from `0` to `log ω`) and the coupled unitary example with phases `ω²/2` and
  `log ω`; normalized non-Abelian integration with its cocycle law
  `A ⋆ B = A + W_A B W_A*` and the exact noncommuting Hahn recurrence; the real
  rotation-block descent and the real metric cone with its parity; the positive
  Ermakov–Pinney dichotomy and the canonical amplitude–phase reduction; the
  exact Airy Hahn expansion with Wronskian `−2i`, amplitude jet and truncation
  residual; the resonance algebra with Dickson finiteness and the singular
  three-phase invariant algebra `C[U,V,W]/(UW − V²)`; the phase lattice as a
  Galois torus with its group algebra and real form; and the set-sized
  witness-closed reading of the proper-class arguments.
* **09 — BM bridge and derived smallness.** The derivation of smallness and of
  strict order reversal on the infinitesimals from the `H`-field positivity
  axiom — the provenance this report uses; the theorem that intrinsic
  differentiation preserves common-domain coherence, with the total intrinsic
  derivative and the fixed-contour and moving-pole discussion; the
  bounded-primitive ideal as a named object with its full structure theory,
  including the cut description; the resolvent support certificate and the
  whole-prefix coefficient recurrence; the `Σ ω^(n²) X^n` support
  counterexample; the derivation-aware representation interface.
* **11 — autonomous dynamics.** The whole of Part VI: the class of normalized
  derivations; multivariable formal evaluation, formal implicit uniqueness in
  a monad and strip logarithms for every normalized derivation; projective
  reduction; the realization classification on curves with its simple-zero and
  power–logarithm families; the finite-scale Hahn field with the three-shift
  formula; the continuum of algebraically independent solutions of
  `ðu = u³ − u²` inside two scales (Rosenlicht's theorem imported); derivation
  independence with its scalar, real and uniform-bound corollaries; the real
  branch count and worked equations; the infinitesimal-contraction and
  hyperelliptic obstructions with their counterexamples; the formal-group
  logarithm, identity-monad splitting, abelian logarithmic-derivative image,
  abelian finite-primitive criterion and speed threshold; the finite
  geometric decision criterion; and the review log
  `11-autonomous-dynamics-sources.md`.
* **12 — regular-singular spectral selection.** The whole of Part V: the Euler
  derivation on arbitrary real-exponent Hahn fields; the power-Hahn
  regular-singular class; resonance-reaching supports and finite dependence;
  the support-controlled Hahn–Levelt form and the finite resonance theorem with
  its degree bound; the real-monomial shear; spectral selection, perturbation
  invariance and real descent; the classifications over `K_R` and over `No[i]`
  with morphism and tensor dimensions; the Hahn solution space, the
  transcendence of `log t`, minimal logarithmic repair with group `(C,+)`, and
  the exact Hahn obstruction sequence; six worked examples; the
  finite-monomial, one-logarithm envelope; the power-Hahn boundary; and the
  exact finite procedure with its limits.
* **13 — transfinite critical potentials.** The whole of Part VII: the
  imported ordinal log-atomic tower and scale separation; the summable
  triangular differentiation and the exact critical solutions at every
  ordinal; the Wronskian spanning lemma, the Liouville gauge identity and the
  Euler classification at a positive infinite scale; the transfinite
  classification with Conway normal forms, Wronskians and a Riccati form; the
  earlier-stage asymptotics, the invisibility theorem, the first infinite stage
  and the absence of an all-ordinal potential; the three Hahn fields at a limit
  ordinal with the `0, 1, 2` jump and the exponential-then-primitive gap; the
  Borel Picard–Vessiot group and its additive remainder; the Schwarzian form;
  the first limit stage `λ = ω` worked out; its boundaries, inputs and
  formalization interface. The code and data are placed as
  `code/13-critical-potentials-verify.py`,
  `data/13-critical-potentials-verification.txt` and
  `data/13-critical-potentials-manifest.json`.

### How conflicts were resolved

* **Smallness** is *derived* (from `H`-field positivity, with strict order
  reversal as a bonus), not imported. The square-root route used by two sources
  is kept as a remark. `∂m ⊆ m` is recorded as **strict**.
* **The word-counting lemma** is both cited (Neumann, Higman) and proved in
  full in Appendix A, in its **ordered**-word form, which is what noncommuting
  matrix products require.
* **The nonlinear IVP uniqueness class** is printed with the qualifier its
  proof supports and nothing wider: uniqueness among positive-support coherent
  solutions with the specified ordinary reduction, the support containment
  stated as a *conclusion*. The stronger linear statement — uniqueness among
  all Hahn-coherent matrices — is kept separately.
* **"The resolvent theorem"** named four different coefficient rings across the
  batch. It is stated once over `C((t^Γ))` for `Γ ⊆ R` with `1 ∈ Γ`, the
  hypothesis its valuation-shift proof actually needs, with an explicit note
  that the real-exponent restriction is substantive at higher rank; the sharper
  rational-exponent images are kept as the separate statements they are; and
  the sharp threshold theorem is kept separately restricted to real-exponent
  coefficients, with its counterexample, and is **not** merged into the
  resolvent.
* **Where member 10 strengthened a hedge**, the hedge was amended rather than
  removed and the new hypothesis was named. Item N22 now records that
  first-order inhomogeneous existence holds, but only through the imported
  splitting/surjectivity theorem and not through the rank-one criterion — the
  "at most one, not none" witnesses are untouched, and what changed is that
  their uniqueness is now known to be accompanied by existence. Item N24 now
  separates the general finite-system normal form from the explicit Hermitian
  eigenvalue formula, keeping the counterexample to extending that formula to
  arbitrary coefficients. Part V adds a computable regular-singular class.
  These statements concern different scopes.
* **Members 11 and 12 were integrated by the same rules.** Their reproofs of
  results already here — smallness, the missing oscillator, the ordered-word
  lemma, strip logarithms, the logarithmic separator, the missing logarithmic
  primitive, and the `√2` monomial example (printed only as a row of Table 5)
  — are recorded as agreements and cited; where a reproof holds under weaker
  hypotheses (every normalized derivation; no surjectivity; no import) it is
  kept, with that scope, in its new part, and no older statement is widened.
  Part V keeps member 12's **import-free** proofs rather than routing its
  `No[i]`-level results through Part III, which would silently add Part III's
  imported theorem.
* **The one-derivation rule was amended, not deleted.** Warnings 3.2 and 3.3
  and items N2–N3 now say that every part except Part VI is relative to the
  one fixed `∂`, and that Part VI proves one sector the same for all
  normalized derivations without classifying them. Items N21, N22, N23, N24,
  N25, N48 and N57, the remark after Corollary 8.11, Warnings 16.11 and 17.13,
  and three open continuations are amended in place with the original wording
  kept; items N24 and N57 and two continuations are answered **in part** and
  stay open beyond the regular-singular class. Item N41 (coordinate irregular
  singularities) is untouched: Part V is about the intrinsic derivation.
* **Member 13 was integrated by the same rules.** Its proof that nonreal
  powers of an infinite scale do not exist (through an infinitesimal primitive
  of the angular rate) is this report's criterion and is recorded as agreement
  (Corollary 37.1); its derivative-stability argument is cited as an instance
  of the monomial criterion (Proposition 40.3); its stage 0 agrees with Part V
  (Remark 38.4). Its own proofs are kept, since they use neither surjectivity
  nor Part III's import. Three connections it does not state are recorded as
  observations of this merge, with proofs (Remarks 37.4, 37.5, 38.5). Items
  N13, N21, N23 and N48, the remark after Corollary 10.3, Remark 28.5, the
  opening of Section 21, the remark after Theorem 17.6, Warning 5.3 and one
  open continuation are amended in place, with the original wording kept.
  One omission in the member's repository comparison is recorded with its pin
  (item N104): the article it read already contained the first-order
  counterpart, Corollary 10.3.
* **Two things are recorded rather than claimed.** Remark 25.13 is an
  observation of this merge, with its proof, that neither source states; and
  the open continuations record, unaudited, that member 12's hypotheses are all
  clauses of the normalized-derivation definition, without upgrading Part V.
* **Two pre-existing rendering defects were repaired.** Every cross-reference
  used to print "Theorem" whatever the environment (a shared-counter problem
  with `cleveref` under the current LaTeX kernel); alias counters now make it
  print "Corollary 11.4", "Warning 5.2" and so on, with unchanged numbering. A
  stray `\label` without braces that printed the text "iff:placeholderX" in
  Example 18.2 was removed; it defined no `diff:` label.

## What is NOT claimed

Section 51 of the report is the consolidated register: 106 numbered items
covering the 181 explicit non-claims that the eleven manuscripts state between
them (118 from the first seven, 12 from the eighth, 15 each from members
11 and 12 and 21 from member 13, by this merge's count), together with the
audit findings on the source packages. It is part of the result. Items N1–N52
come from the first seven, N53–N64 from the eighth, N65–N79 from member 12,
N80–N94 from member 11 and N95–N106 from member 13. In outline:

* **Provenance.** The Berarducci–Mantova derivation is imported, not
  constructed and not reproved; no uniqueness of it is claimed and no other
  surreal derivation is classified; every intrinsic statement outside Part VI
  is relative to this one `∂` with `∂ω = 1` and none is derivation-agnostic.
  Part VI is stated for the class of normalized derivations, proves one sector
  the same for all of them, does not classify them and does not assert that
  two of them agree on `No[i]`; Part V is stated for `∂` only. The Neumann
  support lemma, Gonshor's normal forms, the `ω`-series composition and
  incompatibility results, the universal `H`-field results and, for Part VII,
  the ordinal log-atomic formulas are separately imported with their
  hypotheses intact, and none is strengthened. One source
  records that the Neumann paper was not retrieved in full, which is why
  Appendix A proves the lemma.
* **Novelty and verification.** No priority claim, no solution of a named
  published open problem, no independent refereeing, no proof-assistant
  verification, no Lean source. The literature search was targeted. The seven
  repository audits were targeted, revision-specific and read-only; none
  asserts that any keyword is absent from the repository, and empty or
  truncated search responses were not used as evidence of absence. The
  repository's existing phase decomposition and chosen-exponential obstruction
  are prior coverage, acknowledged as such.
* **Effectivity.** The normalized primitive, the obstruction map and the
  workflow are exact *semantic* operations, not algorithms. A well-ordered
  support is a semantic certificate, not an effective presentation. Only the
  first three of the four result outcomes are decidable, and only for the
  finite exact core; the rational classifier is restricted to `Q(X)` and
  *raises* on unsupported input rather than reporting nonexistence.
* **Scalar scope.** Part II is scalar homogeneous first-order equations only.
  (Part VI now classifies first-order *autonomous* equations with constant
  coefficients; variable coefficients, higher order, systems and
  higher-dimensional autonomous systems remain unclassified, and the finite
  decision criterion there needs exact algebraic coefficients. Part VII
  classifies one explicit family of second-order linear equations with
  variable coefficients; every other higher-order operator, and every
  perturbation of that family, remains unclassified — item N21, amended.)
  No differential closedness; no general inhomogeneous existence theorem there
  (outside the admissible locus its claim is *uniqueness* only); no higher-rank
  differential modules; and the constant-coefficient results concern ordinary
  complex constant coefficients only. All nonexistence results are about surcomplex *number* solutions under
  `∂`; they do not deny ordinary oscillatory functions or algebraically defined
  global surcomplex phases, and the Ehrlich–Kaplan constructions should not be
  described as nonexistent.
* **Matrix scope.** Part III classifies every ordinary finite system over `SC`.
  The Hermitian hypothesis belongs to its eigenvalue formula; Example 16.10
  shows why that formula does not apply to arbitrary coefficients. Part V
  computes phases for the power-Hahn regular-singular class by an explicit
  route without the matrix import. General inhomogeneous existence and the
  abstract normal form rest on the imported splitting/surjectivity theorem,
  which is not a consequence of the scalar criterion. Effective computation
  of phases and normalizing gauges on specified input languages remains a
  separate question. The general classification over `SC` also does not settle
  gauge equivalence over a prescribed smaller field or systems of infinite
  dimension. `Obs` and the normalizing gauges are exact semantic operations;
  their existence alone gives no algorithm on arbitrary input descriptions.
  The spectral theorem does **not** remove the connection term `W*∂W`; that
  term is present and merely invisible in the quotient by `A`. The metric
  theorems make no Lyapunov or uniform-equivalence claim. Member 10's novelty
  assessment is provisional, narrowed to three statements, and based on a
  targeted search; no named published open problem is claimed solved, and in
  particular no new solution of the Boshernitzan conjecture. All of Part III is
  relative to the one fixed `∂` with `∂ω = 1` and to no other derivation.
* **Regular-singular scope (N65–N79).** Ordinary complex residual matrix and
  power-Hahn real-exponent perturbation only (the `i/log ω` counterexample,
  which does not refute a classification by richer logarithmic data); no
  higher-rank exponent groups; no global exponential, trigonometry at infinite
  arguments, fine-topological IVP or extension of ordinary local solutions;
  existence only for forcing in `K_Rⁿ`, and "Fredholm" only in an algebraic
  sense; the critical set is sufficient, not minimal, a finite certificate is
  not a finite listing of the gauge, and finite dependence is not an oracle
  algorithm; the `K_R`-classification must not be transferred to `K_Q`;
  invariance is under positive Hahn order, not numerical smallness; `N`'s
  entries are not canonical; `∂_τ` is not a coordinate derivative; classical
  Levelt theory and the report's scalar obstruction are antecedents; no
  refereeing, no Lean, provisional priority, a scoped repository comparison.
* **Autonomous scope (N80–N94).** No equality of normalized derivations on
  `No[i]` and no uniqueness claim; first-order equations on curves only —
  variable coefficients, higher order, systems and higher-dimensional
  autonomous systems are outside, and which higher-order sectors distinguish
  derivations is open; differential-algebraic only; finite monomial generation
  is not finite transcendence degree; the strip logarithm is pointwise; local
  normal forms and Rosenlicht's theorem are imported (from Noordman–van der
  Put–Top, numbered by its arXiv v1); parametrizations are not canonical;
  constant commutative abelian varieties only, with no uniformization or
  global exponential; surjectivity only in two flagged corollaries;
  effectivity only with exact algebraic coefficients and decidable signs; no
  trigonometric assertion; no refereeing, no Lean file, no priority
  certificate.
* **Transfinite critical-potential scope (N95–N106).** Scalar unknowns in a
  fixed differential field, not functions on an interval; relative to the one
  fixed `∂`, with the log-atomic formulas imported and not implied by `∂ω = 1`,
  and nothing claimed for other derivations or for Part VI's class; no
  transfinite iteration or composition of `log`, no substitution, and the
  monomial map is not `exp(x log ω)`; only Hahn sums, no fine-topology limits,
  no proper-class sums, no all-ordinal potential; this family only — no
  classification of arbitrary potentials and no stability of the threshold
  under smaller perturbations; invisibility concerns the named hierarchy only
  and is not a fine-topology discontinuity; finite spans of exponents, no
  closure claims for the largest Hahn field and no minimality of the
  intermediate ones; the classical Kneser–Weber–Hartman–Hille hierarchy, the
  derivation, the tower, Hahn real closedness, the gauge and Schwarzian
  mechanisms are antecedents or imports; priority provisional, no refereeing,
  no Lean; a bounded repository comparison at its pin; 70 finite checks that
  certify no transfinite statement; and the package audit (N106).
* **Workspace scope.** Neither localization gives closure under all summable
  families; no Hahn completeness, no birthday bound, no enumeration, no
  termination claim. The hull's minimality holds only among full Hahn fields
  indexed by divisible exponent groups. The support threshold provably does not
  globalize by valuation.
* **Coordinate scope.** Positive support is sufficient, not necessary (the
  nilpotent example). The nonlinear theorem needs a *supplied* ordinary
  background solution on a simply connected `U`, does not continue it past its
  singularities, and does not cover negative-valued perturbations. Monodromy is
  an ordinary-domain construction; monodromy for the nonlinear problem on
  non-simply-connected domains remains future work. No Stokes theory, no
  irregular-singularity classification, no Riemann–Hilbert correspondence.
* **The checks.** The eleven suites check finite exact symbolic identities and
  finite jets: 1,395 + 115 + 149 + 258 + 291 + 150 + 259 + 62 recorded passing
  checks for the first eight, 10 (member 11, at the default truncation
  degree 4), 8 (member 12) and 70 (member 13). The first seven ran under
  Python 3.13.5 (six of them with SymPy 1.14.0); the eighth records SymPy 1.14.0
  and a status of PASS but no Python version; members 11 and 13 record Python
  3.13.5 and SymPy 1.14.0; member 12 records SymPy 1.14.0, and its README says
  only "Python 3". Member 13's program was rerun once on a copy during this
  merge (Python 3.14.4, SymPy 1.14.0): 70 passed, output identical to the record
  apart from the version line. They do not construct the surreal numbers, do not verify Hahn
  summability, class-size arguments, Higman's lemma, transfinite recursion, or
  any general nonexistence theorem; the eighth adds that it verifies none of
  the arbitrary-support Hahn arguments, none of the published model-theoretic
  inputs, and no existence of a gauge for an arbitrary surreal matrix. Declared
  cutoffs are part of the claim, including a matrix cutoff by *total degree* 6
  that is explicitly **not** a valuation cutoff. The eighth suite's deliberate
  counterexamples are asserted **as** counterexamples, so a run that passed
  while those assertions failed would report the opposite of what it appears to
  report. Member 12's program handles finite rational supports only and is not
  a parser or decision procedure; its record's `ambient_dimension: 1` is a
  label written by the script, not a computed quantity, and its tail-invariance
  check compares coefficients only through weight 4. Member 11's tests do not
  establish the support lemma, the algebraic-geometric reduction or the
  completeness of the solution list. Member 13's checks model the log-atomic
  derivatives by a finite derivation on generators and the Euler scale by an
  ordinary variable; they do not prove the imported derivative formula,
  transfinite summability or field membership. Appendix D reproduces each
  record.

## Relation to the neighbouring reports

* **`docs/surcomplex/trigonometry/`** supplies the finite-angle phase group and
  explicitly declines to choose a derivation. This report reproves the part it
  needs and adds the derivative identity `∂ cis θ = i(∂θ) cis θ`; it states
  precisely what its no-go theorems do and do not say about that report's
  global phase extensions. Those constructions need not be renamed as false;
  their contracts need only be distinguished from the intrinsic differential
  one. **Cross-link both ways.**
* **`docs/surcomplex/analysis/`** already proves a derivation obstruction for
  *one chosen* canonical global surcomplex exponential. **That is prior
  coverage.** This report's Corollary 11.4 — there is no map
  `Ψ : No[i] → No[i]ˣ` with `∂Ψ(z) = Ψ(z)∂z` for every `z`, with no
  homomorphism, continuity, analyticity or normalization hypothesis —
  **strengthens that theorem in phase-independence and does not contradict
  it.** The two are compatible. The coordinate half also reuses that report's
  common-domain coherent-section language and refines its
  germ/common-domain/formal distinction into an explicit table with named
  witnesses.
* **`docs/surcomplex/spectral-theory/`** supplies the finite algebraic spectral
  vocabulary Part III uses, and its "spectrum" is the **algebraic eigenvalue
  and singular-value list**. That is *not* the differential phase spectrum;
  Theorem 16.5 is the bridge between them for Hermitian coefficients, and
  Example 16.10 shows there is no bridge in general. Each report should name
  its own sense of the word on first use. **Cross-link both ways.**
* **`docs/foundations-and-computation/computer-algebra/`** poses the capability
  taxonomy and the subsection "Differential equations must name their
  category"; **`.../foundations/`** poses the four-interface discipline. The
  operator table, the result contracts, the certificate table and the tiering
  contract in this report answer both directly, and the separation chapter
  sharpens the derivative distinctions. **Cross-link both ways.**
* **`docs/surcomplex/hahn-tate-uniformization/`** records among its
  limitations that curves with nonnegative valuation of `j` need formal groups
  around a good-reduction model, and it makes no assertion about the
  Berarducci–Mantova derivation. Part VI's identity-monad splitting does this
  for **constant** abelian varieties over `No[i]`, reducing by standard part —
  a cross-link, not an answer to that report's question over Hahn fields with
  a coarse valuation — and is the collection's first contact between surreal
  derivations and abelian varieties. **Cross-link both ways.**
* **`docs/surreal/tail-spans-and-differential-transcendence/`** uses the Euler
  derivation that Part V writes `∂_τ`. Part VI's continuum of independent
  solutions concerns algebraic independence of differentially *algebraic*
  solutions, a different notion from that report's differential
  transcendence; there is no conflict.
* **`docs/surcomplex/dynamics-and-normal-forms/`**: its "autonomous flow" is the
  embedding of near-identity maps into formal flows; Part VI's autonomous
  equations are a different subject, and member 11's archive name
  ("dynamics") should not suggest otherwise.
* **`docs/surcomplex/nonabelian-support/`**: its Frobenius theory is for the
  *coordinate* derivative `d/dz` with positive-support residue; Part V is for
  the intrinsic Euler derivation, and the two are not merged.
* **`docs/physics/surreal-scalars-and-spacetime/`** cites the oscillator
  corollary (Corollary 8.8, number unchanged) and adopts the three phase
  symbols. Part VII keeps both and adds that the corollary's second-order
  statement is the Euler threshold at the scale `e^ω` (Remark 37.5); nothing
  there needs to change.
* A keyword search of `docs/` at this merge found the log-atomic tower,
  Kneser-type critical potentials and the Schwarzian nowhere outside this
  directory, so Part VII has no neighbour to cross-link beyond this report's
  own Parts II, III, IV and V.

## Build

`article.tex` is standalone: internal bibliography, no external `.bib`, no
graphics, no font files, no shell escape, no network access.

```sh
latexmk -pdf -interaction=nonstopmode article.tex
```

If `latexmk` is unavailable, run `pdflatex -interaction=nonstopmode` three
times so that the table of contents, the cross-references and the `cleveref`
labels settle. The delivered build (188 pages) has zero LaTeX errors, zero
warnings, zero undefined references or citations, zero multiply-defined
labels, zero duplicate destinations, and zero overfull or underfull boxes.

The review of Sections 23–24 rebuilt the current report in three passes
at 166 pages without warnings or box issues, and the changed pages were
visually inspected. Member 12's unchanged verifier passed all eight suites
on a temporary copy using Python 3.13.14 and SymPy 1.14.0; every JSON field
matches the delivered record. A separate exact matrix calculation checked
the new whole-block example. All 48 historical code, data and source-log
files remain byte-identical. The full Lean build and its 5,371-declaration
axiom audit also pass; these documentation changes add no Lean coverage.
The later regular-singular and autonomous arguments remain for review.

The subsequent review of Sections 25–26 rebuilt the report at 167 pages
in three passes, again without warnings or box issues; the revised pages
were inspected. All eight member-12 suites passed on a temporary copy and
matched the historical JSON. Additional exact checks covered the new
two-dimensional classification example and Jordan blocks of sizes one
through six in the logarithmic-repair and sharp forced-degree formulas.
The 48 historical files remain byte-identical, and the full Lean build
and 5,371-declaration axiom audit pass. The review now includes spectral
selection, both classifications, logarithmic repair and all solutions of
the forced equation; later sections and formalization remain separate.

The final regular-singular pass reviewed Sections 27–28 and rebuilt the
report in three passes at 168 pages without warnings or box issues.
The workspace, rank-one classification, logarithmic boundary, procedure
and dependency-table pages were inspected. Member 12's unchanged verifier
again passed all eight suites on a copy, matching every historical JSON
field. A separate finite calculation checked the reduced-weight example:
deleting the noncritical input at weight `3/2` changes the gauge but
preserves the normalized resonant coefficients. All 48 historical files
remain byte-identical. The full Lean build passed 3,872 jobs and the
5,880-declaration axiom audit. The main-text review now covers all of
Part V; the autonomous part and remaining imports and source reconciliation
are still pending.

The first autonomous pass reviewed Section 29 and Sections 30.1–30.3,
through simple zeros, and rebuilt the report in three passes at 169 pages
without warnings or box issues. The formal-evaluation, divided-difference,
projective-reduction and linearization pages were inspected. Member 11's
unchanged verifier passed its ten default-degree checks on a temporary
copy with Python 3.13.14 and SymPy 1.14.0; its output matches the delivered
record apart from the Python version. Separate exact calculations checked
the quadratic linearizer, its inverse and the local divided-difference
example. All 48 historical files remain byte-identical. The full Lean
build passed 3,872 jobs and the 5,880-declaration axiom audit. The primary
comparison checked NPT arXiv v1 Lemma 6.1(i) and Stacks Tag 0BX5;
the multiple-zero classification and later autonomous arguments remain
for review.

The second autonomous pass reviewed the multiple-zero classification and
completeness proof in Section 30.4. The report rebuilt in three passes at
170 pages without warnings or box issues, against a clean 169-page
baseline; the changed proof pages were inspected. The unchanged member-11
verifier again passed ten checks and matched the historical record except
for the Python version. Separate exact checks covered pure monomial zeros
of orders two through six, their parameter-separation coefficients, and
a triple-zero example with nonzero logarithmic residue. All 48 historical
files remain byte-identical. The full Lean build passed 3,872 jobs and
the 5,880-declaration axiom audit. These finite calculations support the
examples; they do not prove the general classification or complete its
Lean formalization. Sections 29–30 are now reviewed; later autonomous
arguments, other imports and source reconciliation remain pending.

After merging batch 19 from `7657737`, the combined report rebuilds in
three passes at 189 pages without warnings or box issues, against a clean
188-page upstream baseline. The multiple-zero proof pages were inspected.
All 51 historical code, data and source-log files match the upstream bytes;
Part VII and subsequent source text are unchanged by this review. The full
Lean build passes 3,872 jobs and its 5,880-declaration axiom audit. This merge
validation does not extend the proof review to the critical-potential part.

## Re-running the source verifiers

The programs in `code/` are the originals. **Run them on a copy.** Several
write their evidence files beside themselves — and member 10's program writes
to a `data/` directory it creates one level *above* its own, overwriting the
delivered `verification.json` — so a byte-identity check performed *after* a
run compares two equally modified copies and tells you nothing. Their recorded outputs are already in `data/`, and Appendix D of the
report reproduces them. Nothing in `code/` or `data/` was modified to
produce this report.

The three latest packages have hazards of their own, and their scripts still
use the packages' original file names rather than the placed ones:

* member 12: `code/12-regular-singular-verify.py` (Python ≥ 3.10, SymPy; see
  `data/12-regular-singular-requirements.txt`) writes its `--output` file,
  by default `verification.json` in the **current directory**, and prints the
  same JSON; the `verify` target of `code/12-regular-singular-Makefile` runs
  `python verify.py --output verification.json > verification.txt`,
  overwriting both records. The delivered records are
  `data/12-regular-singular-verification.json` and
  `data/12-regular-singular-verification.txt` (identical JSON content).
* member 11: `code/11-autonomous-dynamics-verify.py` (SymPy; `--degree N`,
  `2 ≤ N ≤ 7`, default 4) writes only to standard output, but
  `code/11-autonomous-dynamics-build.sh` and the package README redirect it
  onto `verification.txt`; the delivered record is
  `data/11-autonomous-dynamics-verification.txt`.
* member 13: `code/13-critical-potentials-verify.py` (Python ≥ 3.10, SymPy)
  prints its report and writes a file only when given `--output`; the package
  README's `python verify.py --output verification.txt` would overwrite a
  record of that name. The delivered record is
  `data/13-critical-potentials-verification.txt` (70 checks).

Members 11 and 12 have no checksum manifest. Member 13's is kept as
`data/13-critical-potentials-manifest.json`: its five SHA-256 digests match the
delivered package, but three of the files it lists — the package's
`article.tex`, its 21-page `article.pdf` and its `README.md` — are source
material that is not shipped in this directory.
