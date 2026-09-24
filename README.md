# Surreal

Research on surreal numbers, surcomplex numbers and omnific integers: a
collection of research reports in [`docs/`](docs/README.md), and a Lean 4
formalization of their theorems that proceeds from foundational lemmas to
dependent results, reusing mathlib constructions.

## What the repository contains

- **Research reports.** [`docs/`](docs/README.md) holds 63 reports in five
  families: the surreal field `No` (23, including six on Conway's omnific
  integers `Oz`), the surcomplex numbers `No[i]` (28), surquaternions (1),
  physics (2), and foundations and computation (9). Each has a LaTeX source,
  a README stating what it claims and what it does not, and usually finite
  verification code. All 63 reports now have typeset PDFs.
  Start with the [reader's guide](docs/README.md) and the
  [typeset catalogue](docs/manifest.pdf); the [notation guide](docs/NOTATION.md)
  reconciles local conventions, and the [formalization ledger](docs/FORMALIZATION.md)
  maps statements to Lean declarations.
- **Lean library.** [`Surreal/`](Surreal/) constructs the actual surreal field
  as an ordered field of sign sequences, proves it real closed and the
  surcomplex numbers algebraically closed, and formalizes a growing set of
  results from the reports. The default build checks that every declaration
  in its namespaces depends only on the axioms `propext`, `Quot.sound` and
  `Classical.choice`. The [Formalization](#formalization) section below
  records progress.

### Highlights

The reports are AI-assisted, unrefereed research drafts. "Proposed" marks an
answer to a published question whose correctness and priority have not been
independently certified. A result is machine-checked only where the
[ledger](docs/FORMALIZATION.md) maps it to Lean; apart from the last item,
none of the results below is.

- **Ehrlich–Kaplan's initial-subgroup question.** A proposed affirmative
  answer to their question (arXiv:1512.04001v1, Question 2; *J. Symbolic
  Logic* 83 (2018), Question 9.1): every discretely ordered initial subgroup
  of `No` is isomorphic to an initial subgroup of `Oz`. The possible images
  are classified exactly.
  [Report](docs/surreal/discrete-initial-subgroups-and-omnific-normalization/).
- **The universal set-sized quotient of `Oz`.** Every ring homomorphism from
  `Oz` to a set-sized ring factors through the constant term `Oz → ℤ`. For
  five set-sized integer parts, the least ring detecting a purely infinite
  element has exactly the ring's cardinality, in ZFC. The Grothendieck ring
  of the ordinals is not a quotient of `Oz`, a negative answer to the
  addendum of Elliott's MathOverflow question 188430.
  [Report](docs/surreal/set-sized-quotients-of-omnific-integers/).
- **Diophantine geometry over `Oz`.** Hilbert's tenth problem over `Oz` is
  the ordinary one, and Pell and norm-form equations gain no new solutions.
  Single quartic equations define `ℤ` inside `Oz`. Among smooth affine
  curves only the affine line has nonconstant omnific points, so every
  nonsingular `y² = x³ + ax + b` over `ℤ` has only its ordinary integer
  solutions in `Oz`. [Report](docs/surreal/omnific-diophantine-geometry/).
- **Groups seen from a set.** For `n ≥ 3`, `SL_n(ℤ)` is the universal
  set-sized quotient of `E_n(Oz)`; in rank two no universal quotient exists
  ([report](docs/surreal/omnific-groups-and-lattices/)). For compact
  connected groups over `No`, a universal set-sized quotient exists exactly
  in the semisimple case, and it is then standard part
  ([report](docs/surreal/euclidean-three-space/)).
- **Differential rigidity of entire Hahn functions.** Over a fixed Hahn field
  `k((t^Γ))`, entire D-finite series are polynomials. A linear
  `q`-difference equation with polynomial coefficients and `q` of infinite
  multiplicative order has a nonpolynomial entire solution iff `|v(q)|` is
  an order unit of `Γ`. `Γ` has an order unit iff some nonpolynomial entire
  series is differentially algebraic (Theorem H); an explicit theta series
  has differential order three. The later chapters exclude order two for
  every value group, and order three with total jet degree at most three;
  these additions await independent proof review.
  [Report](docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/).
- **Exponential automorphisms of `No`.** Every exponential 1-automorphism of
  `No` is the identity, a proposed negative answer to Question 5.4 of
  Kaplan–Krapp–Serra (arXiv:2509.22374v3).
  [Report](docs/surreal/exponential-automorphism-rigidity/).
- **Gamma and zeta on `No[i]`.** Six independent manuscripts are reconciled
  claim by claim. At finite points the lifts have exactly the classical zeros,
  so their Riemann hypothesis is the classical one. At positive infinite real
  part every formal Dirichlet series is strongly summable and zeta has no
  zeros. Reflection is obstructed at infinite height. No proof of the
  classical Riemann hypothesis is claimed.
  [Report](docs/surcomplex/gamma-and-zeta-functions/).
- **Surreal fields across universes.** For transitive `M ⊆ N` with the same
  ordinals and uncountable `κ`, `No^M` is `κ`-saturated in `N` iff `N` adds
  no ordinal sequence of length below `κ`. Naming conjugation gives real
  forms of one algebraically closed class field that are not conjugate to the
  standard one.
  [Report](docs/foundations-and-computation/surreal-fields-across-universes/).
- **Birthday cutoffs.** The surreals born below an epsilon number `λ`, with
  their birthdays, are bi-interpretable with the hereditary sets
  `(H_κ(λ), ∈, λ)`; already `No_{<ε₀}` recovers every hereditarily countable
  set. [Report](docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/).
- **Published questions of Lipparini and Roughan.** No unital homomorphism
  evaluates increasing Hahn series at `ω`, a negative answer to Lipparini's
  Problem 7.7 ([report](docs/surreal/hahn-evaluation-at-omega/)). His
  sign-truncation game always has a surreal value but is not monotone
  ([report](docs/surreal/broadcast-sum-of-surreal-sequences/)). A canonical
  form need not be a subgraph of another form of the same value, answering
  Roughan negatively ([report](docs/surreal/canonical-forms-need-not-be-subgraphs/)).
- **Gonshor's product-birthday bound** `b(xy) ≤ b(x) ⊗ b(y)` is proved on two
  specified domains, ordinal-support series and `ℝ((ω⁻¹))`, with exact
  formulas; the general conjecture is not claimed
  ([reports](docs/surreal/gonshor-product-birthdays/),
  [Laurent case](docs/surreal/gonshor-laurent-birthdays/)).
- **Physics without overclaiming.** Surreal scalars record every divergence
  of a singular metric exactly but do not regularize it
  ([report](docs/physics/surreal-scalars-and-spacetime/)). Infinitesimal
  scales give exact results on rare quantum branches and gauge holonomy but
  no departure from ordinary quantum theory
  ([report](docs/physics/quantum-and-gauge-scale-reductions/)).
- **Checked foundations.** In Lean, the constructed surreal field is real
  closed and the surcomplex numbers are algebraically closed. The omnific
  ring is constructed inside the surreal field together with its
  constant-term retraction onto `ℤ` ([ledger](docs/FORMALIZATION.md)).

## Build

The project pins Lean and mathlib to version `4.32.0`; `lake-manifest.json`
records the exact dependency commits. With [elan](https://github.com/leanprover/elan)
installed, run:

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build
```

Lean warnings are treated as errors, including warnings for incomplete proofs.
The default build also checks `SurrealAudit.lean`, which rejects transitive
axiom dependencies other than `propext`, `Quot.sound`, and `Classical.choice`.
The numeric-game field and game-graph recursion reuse a pinned subset of
[combinatorial-games](vendor/combinatorial-games/README.md), with three
documented proof-script adjustments for this Lean version. Its source and
Apache license are included in the repository.

## Formalization

The [source inventory](docs/FORMALIZATION.md) covers 63 maintained main texts
and the source manuscripts preserved in Git history. The
[coverage and dependency ledger](docs/FORMALIZATION.md) records their statements,
the proposed Layer A–E implementation order, and the exact scope of each
implemented result.

The central foundation is a constructed ordered field of surreal sign
sequences and its ordered-field identification with small Conway normal
forms. Real closedness of this field and algebraic closedness of its
surcomplexification are proved. This supports results on the actual fields,
including strong summation, surreal-valued valuation and modulus, fine
calculus, polynomial root stability and finite geometry.

The source collection also includes omnific-integer
[Diophantine geometry](docs/surreal/omnific-diophantine-geometry/README.md),
[set-sized quotients](docs/surreal/set-sized-quotients-of-omnific-integers/README.md),
groups, lattices and normalization. The actual omnific ring is now constructed
inside the surreal field: all growth exponents are nonnegative and only the
constant coefficient must be an ordinary integer. Constant extraction is a
surjective ring homomorphism onto `ℤ`; its kernel is the purely infinite
ideal, and the quotient is exactly `ℤ`. The real and complex support rings
likewise retract onto `ℝ` and `ℂ`. The purely infinite real ideal is also
proved to be a vector space over `ℝ`. Degree is identified with the greatest
normal-form exponent and adds under multiplication. The units of the real
and complex support rings are exactly their nonzero ordinary constants;
the omnific units are `1` and `-1`. An omnific integer bounded by an ordinary
real is an ordinary integer, and `1` is the least positive omnific integer.
Every surreal now has a unique omnific floor `a` satisfying `a ≤ x < a+1`.
The proved formula includes the negative-infinitesimal boundary correction;
for example, the floor of a negative infinitesimal is `-1`. A nonzero
ordinary integer polynomial has exactly its ordinary integer roots in the
omnific ring; every infinite omnific integer is transcendental over `ℝ`.
For every nonzero ordinary integer `n`, divisibility and residues modulo `n`
depend only on the constant term: `Oz/nOz ≅ ℤ/nℤ`. The purely infinite ideal
is exactly the intersection of all positive integer multiples, and also of
all positive powers of any one ordinary prime. A divisor of a nonzero
ordinary integer must itself be an ordinary integer divisor. Ordinary primes
remain prime and generate maximal ideals; mixed gcds and finite Chinese
remainder decompositions reduce to ordinary integer arithmetic.

The finite-quotient classification is also proved: every proper ideal
containing a nonzero ordinary integer is `nOz` for a unique `n ≥ 2`, and
every nonzero finite quotient is `ℤ/nℤ`. Every homomorphism to a finite ring
factors uniquely through the constant-term map, so these maps kill the
entire purely infinite ideal. Nonzero monomials therefore prove that the
omnific ring is not residually finite. Constant extraction is also the
unique unital homomorphism to `ℤ`, and every omnific endomorphism preserves
it. For every ordinary prime `p`, the actual omnific ring's `p`-adic
completion is ring-isomorphic and homeomorphic to Mathlib's `ℤ_[p]` with
its usual metric topology. The source has the inverse-limit topology of
discrete prime-power quotients; it is compact, Hausdorff and totally
disconnected. Its canonical map is dense and induces the original omnific
`p`-adic topology. This map takes the integer constant term into `ℤ_[p]`, so its kernel is exactly the purely
infinite ideal. Both the ordinary congruence topology and each `p`-adic
topology are proved non-Hausdorff: the closure of zero is precisely that
ideal, and two omnific integers are topologically indistinguishable exactly
when their integer constant terms agree. Their separation quotients are
ring-isomorphic and homeomorphic to `ℤ` with the corresponding ordinary
congruence or ideal-adic topology. Constant extraction induces each omnific
topology and is the canonical map to its separated quotient.
The profinite ring isomorphism is also proved: the inverse limit over all
positive ordinary moduli is exactly the ordinary profinite integer ring,
and its canonical map again has the purely infinite ideal as its kernel.
The construction satisfies Mathlib's limit universal property, and every
finite-index omnific ideal occurs in the diagram. With the inverse-limit
topology this isomorphism is also a homeomorphism of compact Hausdorff,
totally disconnected topological rings. The canonical map has dense image
and induces exactly the omnific congruence topology. Higher Diophantine
and general set-sized quotient results remain pending in Lean. The quotient
report's elementary proof through the universal theorem has now been reviewed:
the collision uses only a finite product identity and a set-sized Hartogs
family, without transporting an infinite sum through a homomorphism. Its
integer-divisibility shortcut now states the necessary characteristic
condition. The review now also covers representations, small quotients,
completions, localizations, positive existential conservativity, modules and
the finite-side standard-part theorem, support thresholds and fixed-group
lower bounds, followed by the countable-support and regular-cardinal
two-armed models and the controlled-field construction at every infinite
cardinal, both one-arm support models, and the organizing ring/module
theorem across all five constructions. The set-sized homological package
is reviewed as well: the purely infinite ideal is flat and idempotent but
not projective, and the constant quotient has flat dimension one.
Nonzero Ext¹ and Ext² classes first occur with coefficient modules of
size `|A|`. The constant inclusion splits the ring retraction but is not
an `A`-linear section. The finite-support coordinate cores now have
reviewed proofs of their exact flat dimensions: the constant quotient has
dimension d in d coordinate directions and infinite dimension in countable
rank, despite vanishing positive self-Tor. In the integer and Gaussian
cases, their finite quotients and profinite completions agree with the
constant ring; the resolution and its test modules explain what this
finite data misses. The lattice presentations, nonflatness witnesses and
ordered-cone dimension comparisons now have expanded proofs too.
The noncoherence certificate requires `K ≠ Frac(D)`: the coefficient-field
case `K[ℚ≥0]` is coherent, so nonfinite generation of the tail alone
does not establish noncoherence. The tensor normal forms now include
explicit universal-property proofs for the class carriers. Their torsion
is a free module over the ordinary constants, killed by the purely
infinite ideal. Exterior powers of degree at least two retain only
constants, while symmetric powers retain a tail with a coupled scalar action.
The Rees presentation now explains how ordinary polynomial relations give
all nonlinear equations. Algebraic degree d is exactly the first nonlinear
degree, yielding two-generated ideals with arbitrarily late first relations.
Finite generation here is as an ideal of the symmetric algebra; a nonzero
relation ideal is not finitely generated as a module over the omnific ring.
The scalar Hom and dual descriptions now explain how distinct coefficient
lattices can have the same double dual. Ordinary ideal classes survive
multiplication after removing tensor torsion, with an identity different
from the omnific ring when the number-field degree is at least two.
For matrices at one common monomial scale, the image is finitely presented
exactly when the ordinary kernel is defined over ℚ (over ℚ(i) in the
Gaussian case); then the image is free.
The relation-count proofs now distinguish the full class rings, where
ideals from coefficient lattices of rank at least two have no presentation
indexed by sets,
from set-sized lexicographic models, where every finite generating map
has exactly κ relations in the sense of minimal generator cardinality.
At κ = ℵ₀ these modules are countably presented but not finitely
presented; their projective dimension is two and that of the cyclic
quotient is three.
The coefficient-Tor proof now identifies the actual maps: second Tor is
exactly the kernel of ordinary coefficient multiplication, of rank
`rs − rank(MN)`. It is torsion over the omnific ring but torsion free over
D; freeness over arbitrary D is not asserted. The maximal self-Tor rank
detects a field after extending scalars, even when the coefficient lattice
itself is not a ring. A quadratic example also corrects an unnecessary
restriction: `c² ∈ D` suffices for the displayed free kernel, but is not
necessary.
The rank-two ideals now have a reviewed classification by fractional-linear
changes over ℤ or ℤ[i], giving continuum many isomorphism classes.
Their endomorphism rings recover ordinary orders as constant quotients;
the multiplier-field degree divides the coefficient-lattice rank.
Over the full class ring, tensoring with any set-sized module makes these
ideals look free of that coefficient rank, despite their equational
nonflatness. The review separates this restricted test from flatness
over the set-sized models.
The face-quotient resolutions now include an explicit free telescope:
its kernel contracts even when the finite Koszul complexes are not
resolutions. Dualizing gives a concrete product cokernel for the top
Ext group, with every transition and quotient map checked.
The nonvanishing proof now explains why a single finite polynomial would
need infinitely many monomials. It gives exact projective dimensions
`pd D = d + 1` and `pd Π_d = d`, and the lattice syzygies determine
those of the lattice modules and their cyclic quotients. The stronger
global-dimension bounds require `K ≠ Frac D`: for the coefficient-field
case `A₁ = K[ℚ≥0]`, weak global dimension is exactly one even though
`pd K = 2`.
Over the ordered core and the universe-relative class rings, a reviewed
flat differential graded resolution now computes every Tor group of two
lattice quotients. The first Tor retains an interval of exponents and is
always nonzero; the second retains only coefficient multiplication
relations. These two invariants record different information.
For orders, second Tor vanishes exactly when their fields are linearly
disjoint in the chosen common field. The reviewed self-Tor product is the
antisymmetrized tensor of the two coefficient boundaries; the quotient by
these products consists of symmetric multiplication relations. This exact
sequence works integrally, without dividing by two.
The completed reconstruction proof recovers an order's multiplication from
its embedded relation module and distinguished unit. By contrast, derived
constant-term reduction gives only a square-zero algebra: the orders of
discriminants 8, 12 and 5 have isomorphic reductions. The review makes the
lower-universe size restriction explicit when applying the universal
module theorem.
For rational polyhedral cores, reviewed proofs establish the omnific
embeddings, the cone-independent fraction field, and the fact that each
nonzero face ideal is flat of projective dimension one over any unital
coefficient subring `D ⊆ K`.
Radical ideals that admit all coefficients at each chosen exponent are
classified by antichains of nonzero faces. Their quotients have finite
flat resolutions whose summand counts are reduced homology dimensions of
face-join complexes. Face-isolating modules now prove that the last
nonzero degree is the exact ordinary flat dimension, bounded by the cone
dimension. Quotients by nonzero such ideals are nonflat homological ring
epimorphisms: positive Tor vanishes against every quotient module, while
the detecting modules lie outside that class. For a nonzero face F, `A_𝒞/I_F` has
flat dimension one and projective dimension two. A quotient that keeps
the monomials on F has a different description: its flat dimension is
the largest dimension of a face meeting F only at zero. An explicit
cellular resolution independently proves `fd D = d` for every cone.
Flat radical geometric ideals recover the face lattice when the monomial
structure is marked. A cone is simplicial exactly when every facet quotient
has flat dimension one; cube cones show that a facet quotient can instead
have flat dimension `d − 1`. These statements concern the finite-support
cores over which the modules are defined. Squarefree monomial quotients
retain their Betti multiplicities and ordinary projective dimension as
flat dimension in the rational-root core. For a principal ideal domain D
that is not a field, every nonzero module acting through the constant map
has flat dimension one if it is D-torsion, and d otherwise. This holds
without finite generation.
Lattices with two independent constants give cyclic quotients of flat
dimension `d + 1` when `K ≠ Frac D`, a lower bound for weak global
dimension. In dimensions at least two, a concrete two-monomial relation
fails the flatness criterion when the core is enlarged to its total-order
core or realized inside the real or Gaussian omnific ring. An explicit
nonzero tensor in the set-sized case exhibits the failure of injectivity.
The cone-extension question now has a written answer: in a fixed rational
space, inclusion between full-dimensional pointed rational polyhedral
cores with the same coefficients is flat exactly when the cones coincide.
Two old interior monomials detect every strict enlargement; testing only
old ray pairs can miss it, as an explicit three-dimensional example shows.
A large quotient can still have a nonzero small image:
`Oz/(ω)` surjects onto `ℤ`,
whereas `Oz/(1+ω)` has only the zero
set-sized image. More generally, the universal set-sized image of `Oz/(f)`
is `ℤ/(ct(f))`. The reviewed internal-field proofs explain another
consequence: whenever a nonzero purely infinite element becomes a unit,
the nonzero target contains a field copy of all surreal numbers, or all
surcomplex numbers in the Gaussian case. The construction first compresses
the additive exponent group, then substitutes monomials. Its field image
has an exact support description and is a proper subfield of the
compressed Hahn field.
The transfer maps agree on overlapping fields even when different
denominators are inverted. The binomial-kernel and dyadic-tower proofs
are now reviewed too: `Oz/(1+ω^a)` contains an algebraically closed field
with a copy of `No[i]`, finite products over that field, and a Cantor
algebra with explicit refining idempotents. That Cantor algebra is a
proper subalgebra: a three-root indicator lies outside every dyadic stage.
In the Gaussian version, conjugation also permutes the root coordinates,
acting on Cantor functions by `f(z) ↦ conjugate(f(−1−z))`.
The class-residue foundations are now reviewed through maximal-ideal
existence: global choice gives characteristic-zero maximal class quotients
above each binomial. Conversely, maximal-ideal existence for all class
rings implies global choice, already for class domains of characteristic
two. The proof uses finite witnesses and set-valued recursion, with no
class of all class ideals. The monomial cutoff, tail truncation and
scale/branch families are reviewed too. An independent ternary tower gives
continuum many maximal extensions of every fixed dyadic branch, even
after all its binary choices are fixed. This still gives only a continuum
total lower bound at one scale. The remaining class-residue proofs are
now reviewed: characteristic-zero maximal quotients separate points and
embed in `No[i]`, while binomial specializations fail even to preserve
Hahn summability. In characteristic zero, term-closed, strongly sum-closed
primes have an exact convex-subgroup classification. A new consequence removes the second
closure hypothesis when the associated subgroup has a set-sized cofinal
subset, including every principal convex subgroup. These are manuscript
proofs, pending in Lean; full source reconciliation remains pending review.
The normalization proofs before the arithmetic fibres are reviewed.
Lean now proves that one positive monomial clears an entire algebra generated
by a small set into the purely infinite ideal, in both `No` and `No[i]`.
Consequently **every surreal and surcomplex number is almost integral**
over its omnific ring, as are all elements over any intermediate ring.
These rings have the full ambient field as their fraction field and complete
integral closure. Ordinary integral closure is strictly smaller: `1/2` is
almost integral but not integral, since a nonunit cannot gain an integral
reciprocal. For both real and Gaussian omnific integers, Lean also proves
the full actual-field normalization theorem: the integral closure properly
contains the original ring, is a proper dense subring of `No` or `No[i]`,
has zero conductor and has no small set of algebra generators.
Both normalizations also have **no nonzero finite ring images**: every
quotient by a proper ideal is infinite. This is proved even for
noncommutative target rings, using only the real algebraic-integer
constants and the finite-field obstruction to `x^q = x + 1`.
Every valuation of `No` or `No[i]` whose valuation ring contains the
corresponding omnific ring is now proved trivial when its value group
is small in the birthday universe. The nonintegral half has value zero
under every such valuation, so these valuations cannot detect integrality.
The proof uses vanishing of monotone additive maps with small image and
the common-monomial denominator theorem.
The real density proof constructs integral units
`√(H²+1) − H` below every positive surreal radius and uses the omnific floor
to approximate from below. Its generic form applies to any integer part of
an ordered field with nonnegative square roots. Approximating both coordinates
gives Gaussian density in every positive surreal-modulus ball; the modulus
bound of one for nonzero Gaussian omnific integers forces zero conductor.
Every real omnific algebra generated
by a small surreal set is now proved closed and uniformly discrete in the
fine topology, even though the algebra itself need not be small. One positive
monomial denominator separates every pair of distinct elements. Every
Cauchy net inside such an algebra is eventually constant, with no bound on
the size of its index or range. In the countable-support model, exactly `cf(κ)` negative
monomials generate the ambient field over its integer part, proving the
denominator size bound sharp. This leaves the normalization's own generator
count open. Lean now gives an exact integrality test on nonnegative support:
the real or complex constant coefficient must be an ordinary algebraic integer,
while positive-growth coefficients are unrestricted. The real normalization
meets the ordinary rationals exactly in the integers. A least negative support exponent prevents
integrality, giving an exact test on finite supports. The Gaussian
normalization has an explicit basis `1, (√3+i)/2` over the real
normalization `𝒩`; its additive quotient by `𝒩[i]` is exactly `𝒩/2𝒩`.
The fixed-model, least-exponent and Gaussian-basis conclusions remain pending
in Lean.
The arithmetic-fibre review now reaches integral doubling and trace/norm:
modulo the extended purely infinite ideal, the normalization becomes a
ring of finite idempotent partitions with algebraic-integer values.
Its rationalization is exactly its total quotient ring, with inverses
computed on the nonzero components. The real fibre contains a square
root of −1 and splits every monic polynomial; it also has zero divisors.
These are manuscript results;
the fibre's Lean formalization remains pending.
Modulo any ordinary prime, its nilradical is nonzero and idempotent,
and cannot be finitely generated. The Gaussian fibre is a product of two
real fibres even modulo 2. The ordinary quadratic subring maps only to
pairs congruent modulo 2; after reduction, this inclusion acquires an
explicit square-zero kernel. The larger normalization basis explains
why the two Gaussian factors nevertheless remain separate.
The fibre's domain images and class ultrafilters are now reviewed as well.
Each prime ideal of the fibre is determined by one Boolean ultrafilter and
one prime ideal of the algebraic integers. Its prime quotient is either
`Z̄` or `F̄_p`; strict prime chains have at most one inclusion. Under global
choice every nonzero fibre element survives in some `F̄_p`, with the prime
allowed to vary, so the fibre has zero Jacobson radical. These consequences
are stated for individual class ideals and remain pending in Lean.
The support-descent review explains why an integral equation can be restricted
to the exponent group of its element, using a linear support projection.
In the countable-support model, the positive support gap also makes the
extended normalization ideals radical: the small arithmetic fibres themselves
embed in the full fibres. This added consequence remains pending in Lean.
The branching proofs now explain how one new dominant scale supplies
independent Boolean choices over a smaller reduced fibre. Globally, every
set-sized subring admits a simultaneous splitter, giving free Boolean
families of every set size and an atomless proper-class Boolean algebra
with no set-sized order-dense core. The proof uses finite branch-algebra
specializations and set-length recursion; these results still await Lean.
The derivation analysis preserves an arithmetic exception: Gaussian omnific
derivations into a set-sized module correspond to its elements killed by 2;
in particular, a nonzero derivation to `𝔽₂` survives. The coefficient-weighted
derivations of the full surreal field instead have class-sized targets.
Finite-support omnific rings retain the ordinary finite quotients and admit
an augmentation to `ℝ` that detects every monomial. Including countable
supports blocks that map through a finite product identity; no continuity
assumption on target maps is needed. In the reviewed regular-cardinal
two-armed model, the exact ring/module detection threshold is `κ^{<κ}`,
while the purely infinite ideal requires `κ` generators. At `κ = ℵ₁`,
the threshold is `2^{ℵ₀}` whether or not CH holds; an explicit reindexing
identifies this model with the countable-support construction. Field closure
also holds at singular support bounds, but the needed common monomial
divisors can fail there. The controlled-field construction reaches every
infinite `κ` by keeping each element within finitely many exponent
coordinates. Its omnific integer part has a characteristic-zero field
quotient of size `κ` in which the actual `ω` maps to `−1`; that map cannot
extend to all omnific integers. In the reviewed one-arm model of size
`λ = λ^{ℵ₀}` for infinite `λ`, every nonzero purely infinite element becomes
1 in some residue field of size `λ`. The Jacobson radical is zero even
though every finite quotient kills the whole purely infinite ideal. That
ideal needs exactly `ℵ₁` generators, independently of `λ`. Source 11's
model has threshold `κ^{<κ}` and κ generators; its proof allows finite
coefficient fields as well as the real and complex cases. Only the stated
real/integer and Gaussian specializations are embedded in the omnific
rings. These cardinal results remain pending in Lean.

The actual surreal field is also proved to be a field of fractions of its
omnific subring, using Mathlib's `IsFractionRing`. One positive Conway
monomial simultaneously clears every member of a small surreal family into
the purely infinite ideal. Conversely, every small family in that ideal
has a common positive monomial divisor with purely infinite quotients.
Each nonzero purely infinite element therefore factors into two nonzero
purely infinite nonunits. These arguments use bounds on the union of the
actual normal-form supports; the new exponent can leave any previously
chosen Hahn workspace. Smallness is explicit in the carrier's lower universe.
Every surreal projective point now has purely infinite omnific homogeneous
coordinates. A single positive monomial clears an entire small family of
coordinate tuples while preserving all their homogeneous equations. Every
small family of nonzero omnific integers also has a nonzero common multiple
of all ordinary powers simultaneously, with purely infinite quotients.

The purely infinite ideals in both the omnific and Gaussian omnific rings
now have the same parameter-free existential definition:
`∃ y, x² = 2y²`. The general Hahn-ring version and its nonsquare-radicand
extension are proved too. Consequently every unital homomorphism between
two omnific rings, or between two Gaussian omnific rings, preserves the
purely infinite ideal, without injectivity or a condition on the target’s size.
Checked counterexamples show why the hypotheses matter: in `ℤ[ω]`, the
purely infinite element `ω` has no quadratic witness; if the constant ring
contains `√2`, the equation admits the nonzero constant solution `(√2, 1)`.

The purely infinite ideal `Π` satisfies `Π² = Π` and has no small set of
ideal generators; in particular it is not finitely generated. Its cotangent
module `Π/Π²` vanishes even though `Π` is nonzero. Every positive ideal-power
quotient is `ℤ`, and completion at `Π` is the discrete integer ring, with
constant extraction as the canonical map. No finite product of irreducibles
belongs to `Π`. Any homomorphism sending `Π` into a nilpotent ideal of any
target ring kills `Π` entirely.

Constant omnific irreducibles are exactly the ordinary signed primes.
Every nonconstant irreducible has constant coefficient `1` or `-1`, but
`(ω+1)^2` and `ω^2-1` are proved nonconstant and reducible with those respective
coefficients. A positive monomial has no finite irreducible factorization,
even up to a unit. Thus the omnific ring is neither atomic nor a unique
factorization domain.

Ordered division is proved for every positive omnific divisor: the quotient
is the omnific floor of the surreal ratio, and the remainder is uniquely
between zero and the divisor. Yet Euclidean iteration can run forever.
Starting from `√2 ω` and `ω`, the verified quotients are `1`, then always `2`;
the remainders `(√2−1)^n ω` remain positive and infinite at every finite
stage. This explicit descending chain also proves that the positive omnific
order is not well founded. Moreover, every pair consisting of a nonzero
purely infinite omnific integer and its irrational real multiple is proved
to have no greatest common divisor: every common divisor can be strictly
enlarged. Its two-generated ideal is not principal. Thus the omnific ring
is neither a GCD domain nor a Bézout domain.

The principal ideals `(ω) ⊊ (ω^(1/2)) ⊊ (ω^(1/4)) ⊊ …` form a proved
strictly ascending chain. The omnific ring is not Noetherian, not a principal
ideal domain, and not integrally closed in its surreal fraction field.
Both `√2` and `√(ω²+1)` are verified integral elements outside the ring;
more generally, `√(w²+1)` is integral and non-omnific for every nonzero
omnific integer `w`.
Lean now also constructs the positive roots of `T^m = ω^γ + 1` for
every `γ > 0` and ordinary `m ≥ 2`, with exact binomial normal-form
coefficients. Monomial substitution preserves coefficients and is injective.
Every surcomplex root is an ordinary complex root-of-unity multiple of
the positive root. Its nonzero coefficient at `γ/m − γ < 0` excludes
every root from both omnific rings, although the roots are integral over
them. The claimed invisibility in every small ring image still awaits
the universal quotient theorem.
Its support-gap and collision ingredients are now proved: every small
positive surreal family admits arbitrarily smaller scales, and every
positive surreal interval is too large for a small target. A finite
scaled-field identity gives sharp cardinal bounds directly for both ring
maps and module actions, including nonunital maps.

Integer-coefficient polynomial systems have omnific solutions exactly when
they have ordinary integer solutions. Constant extraction retracts the
entire omnific solution set onto the ordinary one; the proof even allows
arbitrary families of equations and variable indices. Positive existential
formulas in Mathlib's ring language also have the same truth at integer
parameters. The separate undecidability and computable-completeness claims
remain pending in Lean. Positive existential definable sets are also proved
closed under constant extraction. This rules out such definitions of
nonvanishing, positivity and nonnegativity with integer parameters. The
explicit equation `(X+1)^2 = 2(Y+1)^2` has a positive omnific solution even
though it has no solution in ordinary natural numbers.
The same obstruction now covers every full Hahn coefficient pullback and
both actual omnific rings: a positive existential definable set containing
a purely infinite element must contain zero, when its parameters are ordinary
coefficients. Consequently neither the nonconstant set nor the purely infinite
ideal with zero removed has such a definition. Allowing a nonconstant parameter
changes the conclusion: a singleton is positively definable using its point.
There is also a separate quantifier-free lower bound: neither the purely
infinite ideal nor the ordinary constants can be defined without quantifiers,
even with arbitrary ring parameters. Unary quantifier-free ring formulas
define finite or cofinite sets, whereas these sets are infinite and have
infinite complements. The explicit constant-definition formula therefore
witnesses failure of quantifier elimination for the complete theories of
both actual omnific rings and their integer and Gaussian Hahn counterparts.
Both actual rings also omit an explicit parameter-free type whose every finite
subset is realized: require the element to be an ordinary constant and to
avoid every nonzero integer polynomial. Finitely many polynomials leave an
ordinary natural witness at most their total degree, but every ordinary
integer or Gaussian integer has an integer annihilator. These statements
are proved for native ring formulas and for intermediate Hahn rings as well.
The full type-membership predicate is proved primitive recursive under a
verified encoding of native formulas, including bound-variable scope checks.
Thus both actual universe-indexed omnific rings, and every integer- or
Gaussian-constant intermediate Hahn ring, **fail recursive saturation**:
a computable collection of requirements can have every finite subset
satisfiable while having no simultaneous solution. This now extends to every
intermediate Hahn ring whose ordinary coefficients form any subring of a
number field, without integrality or finite-generation assumptions. The proof
constructs a parameter-free five-witness guard using a sextic with no root
in that number field but roots modulo every positive integer. Finiteness of
quadratic subfields, Dirichlet's theorem and quadratic reciprocity supply
its primes, with all dependencies formally proved. When the larger coefficient
field contains a root of that sextic, its two-witness equation detects exactly
the nonzero constant terms in the full coefficient pullback. The same
polynomial tests every ideal and identifies the purely infinite ideal as the
largest ideal with a root-free quotient. Native parameter-free formulas also
define the constant-term graph in both existential–universal and
universal–existential form, with a unique output for every input. In fact,
the same root hypothesis gives stronger **purely existential definitions**:
one witness for the purely infinite ideal and six for the constant-term
graph. A factor of the sextic supplies a nonsquare integer radicand in the
number field whose square root lies in the coefficient field. The formulas
use only its numeral, so no square-root parameter is needed. The quadratic
criterion also applies independently whenever such a radicand is available;
if it is already a square in the fraction field of the ordinary coefficient
ring, clearing denominators instead produces a verified false positive.

Finite systems of integer polynomial equations now have a checked enumeration
theorem: their traces on ordinary integer tuples are computably enumerable,
both in the actual omnific ring and in every characteristic-zero Hahn
integer-coefficient pullback. Integer polynomial evaluation is primitive
recursive, and searching integer witnesses suffices by constant-term
transfer. Conversely, every integer Diophantine presentation now lifts to
exactly its standard-supported image by guarding each free coordinate. This
gives an equivalence of Diophantine definability over the integers and in
those ambient rings; ordered rings also admit a single sum-of-squares
equation. The remaining classification step is the reverse integer MRDP
theorem. A verified bridge now reuses Mathlib's existing natural Diophantine
results: it converts polynomial functions to native multivariate polynomials,
removes unused witness variables, and uses four-square certificates to obtain
integer systems. In particular, Mathlib's Matiyasevic theorem now supplies a
finite Diophantine definition of the **ordinary natural power graph** on
standard omnific tuples and in every characteristic-zero Hahn pullback.
The signed-integer reduction is also checked: coordinatewise differences of
two natural tuples cover every integer tuple, preserve computable
enumerability in both directions, and turn a Diophantine definition of the
signed preimage into an integer definition. Thus the remaining MRDP
representation problem can be stated entirely over the naturals.

Explicit formulas in Mathlib's ring language now define the ordinary integer
and natural-number domains inside the omnific ring. A recursive quantifier
translation turns every integer ring formula and every natural arithmetic
formula into an omnific ring formula with the same truth on standard inputs,
including arbitrary alternations of universal and existential quantifiers.
The natural arithmetic translation also works uniformly in every
integer-constant intermediate Hahn ring over an ordered coefficient field;
closure under constant extraction is unnecessary. Each arithmetic sentence
therefore has a proved truth-equivalent ring sentence. Computability on
encoded syntax, the many-one reduction and the undecidability consequences
remain pending.

Given an integer Smith normal form, linear systems over the omnific ring
now have a proved complete solution criterion. Nonzero diagonal entries
impose divisibility conditions on constant coefficients; zero rows require
the full transformed entry to vanish. The proof also describes every
solution: pivot coordinates are fixed quotients and the remaining omnific
coordinates are arbitrary. For ordinary integer right-hand sides, every
solution splits into an ordinary solution and a purely infinite kernel
vector. Any rational basis of the matrix kernel uniquely parametrizes that
purely infinite part. In particular, full column rank forces every solution
to be ordinary.

Products of affine linear forms with complex coefficients now have an exact
omnific fiber theorem at every nonzero constant level. Each solution is an
ordinary integer solution plus a purely infinite vector in the common
**real** kernel of the linear forms. Any real kernel basis gives unique
purely infinite parameters, and each Conway coefficient vector lies in that
same kernel. A zero real kernel forces ordinary solutions. For tuples in
the larger complex support ring, full complex column rank forces all
coordinates to be ordinary complex constants.
The Gaussian omnific ring is now constructed from Mathlib's Gaussian integers:
its two coordinates are precisely real omnific integers. The corresponding
fiber theorem is proved over this ring too, with ordinary Gaussian points,
unique purely infinite complex kernel parameters, and disjoint fibers over
distinct ordinary points. The distinction between the two kernels is explicit:
`X + iY` has zero real kernel and only ordinary real omnific solutions,
but the Gaussian omnific point `(1 + ω, iω)` solves its level-one equation.
The converse is proved in both rings: once an ordinary point exists at a
nonzero level, nonordinary points exist exactly when the relevant real or
complex kernel is nonzero. Multiplying a nonzero kernel direction by the
actual monomial ω supplies the nonordinary solution.
Each nonzero kernel direction also embeds the entire purely infinite ideal
into the fiber over an ordinary point. These fibers are proved not small in
the lower universe, the formalization's version of proper-class size. The
ordinary-point hypothesis is necessary: `X − Y = √2` has a nonzero kernel
but no solution in either omnific ring.

Binary polynomials with two distinct projective linear factors now have
proved rigidity at every nonzero constant level; the proof even allows
nonhomogeneous polynomials with those two divisors. In particular,
`x² − D y² = c` has exactly its ordinary integer solutions for every
nonzero integer `D` and `c`, including negative or square `D`. This rules
out infinite omnific Pell solutions without asserting finiteness of the
ordinary solution set. The classical case `D = 2, c = 1` now has its
complete classification: independently signed coordinates of
`(3 + 2√2)^k` for ordinary natural `k`, using Mathlib’s Pell theory.
The full-surreal contrast is also checked: the usual rational parametrization
with parameter `ω` and `D > 0` solves the nonzero Pell equation, but both coordinates
have negative-exponent terms and are not omnific. Their actual canonical
positive-growth truncations have norm zero, so truncation loses the solution.
Pell rigidity also holds in every intermediate Hahn ring with its prescribed
constant intersection, even without closure under constant extraction or a
square root in the coefficient field. For the ordinary Pell sequence, every
positive modulus `m` divides a positive coordinate `Y_k` at an index
`1 ≤ k ≤ m²`, with `X_k ≡ 1 mod m`; the proof uses a finite permutation.

The fixed polynomial `(T² − 13)(T² − 17)(T² − 221)` now has a checked root
modulo every positive ordinary integer, but no root in `ℚ(i)`, the omnific
integers, or the Gaussian omnific integers. Prime-power lifting and the
Chinese remainder theorem prove the modular assertion. Every nonzero
Gaussian integer divides a value at an ordinary integer; an element with
zero Gaussian constant term has no such certificate, even with omnific witnesses.
The converse is now proved too: the single equation `a·s = Λ(t)` with two
existential witnesses detects exactly a nonzero constant term in both actual
omnific rings and their full Hahn coefficient pullbacks. The underlying
augmentation theorem works even in algebras with zero divisors; only a
nonzero coefficient-field scalar is inverted. The checked example in `ℝ × ℝ`
gives the zero divisor `(1,0)` an explicit certificate.
In both actual omnific rings and the Hahn rings, the explicit witnesses have
proved support bounds:
`t` uses only the input support and zero, while `s` uses sums of at most five
such exponents. For nonconstant input their degrees are exactly the input
degree and five times that degree. The construction uses finite polynomial
operations and works over exponent groups of any rank.
For the actual carriers, these bounds use their canonical Conway supports
and leading exponents; injective normal-form maps justify the transfer.
The printed certificates for `1 + ω` and `2 + ω` are checked with their exact
constant coefficients. The detector accepts the nonunit `1 + ω` and rejects
both `ω` and the actual infinite normal form `∑_{n≥1} ω^(1/n)`, whose positive
reciprocal exponents and zero constant term are proved explicitly.
Polynomial counterexamples now verify both restrictions on this detector.
In `ℤ + Xℚ[X]`, the quotient by `(1 + X)` is `ℚ`, so the detector rejects
`1 + X` despite its constant term being one; the ordinary-integer definition
still works. In `ℤ[X]`, the detector fails even though the ambient real field
contains a root of `Λ`: this subring is smaller than the full coefficient pullback.
Faithful polynomial evaluation now realizes both examples inside the
integer-exponent Hahn rings, with `ω` represented by the monomial `t⁻¹`.
The rational quotient, the integer definition, and the detector obstructions
are all proved directly for these intermediate Hahn rings too.
The same polynomial now classifies every ideal whose quotient has no root:
these are exactly the ideals contained in the constant-term kernel. Thus the
purely infinite ideal is the greatest such ideal, for both actual omnific
rings and the full real and Gaussian Hahn pullbacks. Negating the detector
also gives universal ring formulas for the kernel and equality of constant terms.
The constant-term map itself now has a proved existential graph with six
witnesses: require the output to satisfy the ordinary-constant definition,
then apply the quadratic kernel test to its difference from the input.
Every input has exactly one output, in both actual omnific rings and the
corresponding full Hahn pullbacks.
For the real rings, a single integer polynomial now defines the same graph
with eight witnesses. Its total degree is proved to be exactly ten: it is
the squared quintic definition plus the squared quadratic kernel equation.
Both printed seven-witness improvements are also proved: adding the squared
kernel equation to either quartic integer definition gives a graph polynomial
of total degree exactly four. These work on the actual omnific integers and
the full real Hahn rings over every ordered abelian exponent group.
The six-witness quartic graph using the three-square guard remains pending.
The constant inclusion and kernel now form a proved definable split exact
sequence. Both printed orders of existential and universal quantifiers for
the constant-term graph are also proved equivalent to its existential formula.
Every unital homomorphism between the coefficient-restricted rings is now
proved to respect constant terms: integer constants are fixed, while Gaussian
constants are uniformly fixed or conjugated according to the image of `i`.
This holds between different exponent groups and coefficient fields containing
`√2`, and between the actual omnific carriers at different universes.
The Hahn rings also recover their full support ring as the multipliers of
the purely infinite ideal inside the native fraction field. Coefficient
constants are exactly zero together with the invertible multipliers. The
printed fraction-pair formulas and their invariance under changing
representatives are proved, as is the reconstructed coefficient-map graph.
This reconstruction now accepts any native parameter-free formula defining
the ideal. In particular, the number-field radicand formulas recover the
actual embedded coefficient field and the coefficient map on the full
support ring. Native ring formulas on fraction pairs have verified
satisfaction semantics and descend under changing representatives. When the
exponent group is nontrivial, every coefficient has a representative and
every support-ring input has a unique coefficient value.
The multiplier identities and support-ring fraction-field inclusions now
hold for the actual surreal and surcomplex carriers too. Their proofs use
individual monomials in canonical normal forms; they do not require a
surjective map onto a full Hahn field.
The fraction-pair reconstruction formulas now work on both actual carriers
as well, including a literal ring formula for the full coefficient-map graph.
All formulas are proved invariant under changing fraction representatives.
From the pure omnific ring, the reconstructed real coefficients now give
checked formulas for the actual order, finite elements, infinitesimals,
and standard part. The standard-part graph has exactly the finite inputs
and a unique real output. The examples distinguish `ct(ω + 7) = 7` from
`st(7 + ω⁻¹) = 7`: the first input is not finite.
The natural value group is now constructed as the native quotient of
nonzero actual surreals by finite units. Its ordered group structure and
the test `v(x) ≥ v(y)` exactly when `x/y` is finite are proved, with an
external identification by negative leading exponents.
Every automorphism of the actual omnific ring now extends uniquely to the
surreal field by its fraction formula. The extension preserves order, fixes
each ordinary real number, preserves finite elements and infinitesimals,
and commutes with standard part on finite inputs.
These automorphisms need not be trivial: doubling every Conway exponent
defines an actual omnific automorphism sending `ω` to `ω²`, with exponent
halving as inverse. More generally, every ordered additive automorphism of
the surreal exponent group lifts to an ordered field automorphism fixing
the reals. The lift transports the natural valuation, preserves strong
summability and commutes with every strong sum supported in the birthday
universe. The construction retains small supports throughout.
The Gaussian fraction-field identity is now proved on the actual carrier:
one monomial simultaneously clears both coordinates of any small surcomplex
family into the purely infinite Gaussian omnific ideal. Every Gaussian
omnific automorphism therefore extends uniquely to the surcomplex field
and preserves the ordinary complex coefficient field. Restricting to those
coefficients respects composition and is now proved surjective: every complex
field automorphism lifts coefficientwise and preserves Gaussian omnific
integers. These lifts preserve supports and strong sums and form a
composition-preserving section, with no continuity assumption.
An explicit phase twist now fixes every ordinary complex number and preserves
Gaussian omnific integers, yet sends `ω` to `iω`. Lean verifies that its image
lies outside the actual real axis and that the twist fails to commute with
conjugation. Using Mathlib's first-order semantics, this now proves that
neither the real axis nor conjugation is definable in the surcomplex field
with a Gaussian omnific predicate, even when every ordinary complex number
is named. Likewise, the real omnific subring is not definable in the pure
Gaussian omnific ring with parameters from `ℤ[i]`.

These results now prove a single parameter-free definition of both ordinary
constant rings. The same three equations, of exact degrees `3, 3, 7`, with
five witnesses define `ℤ` in the actual omnific integers and `ℤ[i]` in the
Gaussian omnific integers. The theorem also covers arbitrary intermediate
Hahn rings with those constant intersections, without requiring closure
under constant extraction. The checked examples include a witness for
`1+i` and the absence of any witness for `ω+i`. In the full surreal and
surcomplex fields the predicate holds everywhere, so the ring restriction
is essential.
The real omnific ring now has a proved quartic definition of ordinary integers
with six witnesses: a Pell pair and four squares. The same six witnesses
define ordinary integer vectors of any finite length, and every coordinate
of every solution is proved ordinary. The polynomial has total degree exactly
four; Pell growth and Mathlib's four-square theorem construct its witnesses.
The alternative quartic that uses the square of the Pell coordinate is also
proved for every integer-constant intermediate ordered Hahn ring, with no
constant-extraction closure assumption. Its Gaussian failure is complete:
explicit witnesses make the formula accept every Gaussian omnific integer.
The five-witness version using the three-square theorem remains pending.
The real omnific ring also has the proved single quintic definition with
seven witnesses, with total degree exactly five. Its Gaussian failure is
checked on the actual nonconstant element `ω`. Any definition of the
integer constants yields a definition of the natural constants, including
zero, by adjoining four-square witnesses; those witnesses may range over
the whole omnific ring.

The zero level has a different, now proved classification: for positive
nonsquare integer `D`, its omnific solutions are exactly `(±√D t, t)`
with `t` purely infinite. Taking `t = ω` gives an infinite solution.
The three-variable equation `(x + z)² − 2y² = 1` also has a proved exact
parametrization: `(a + u, b, d − u)` over ordinary solutions
`(a + d)² − 2b² = 1`, with `u` purely infinite. Its common kernel permits
nonordinary solutions such as `(3 − ω, 2, ω)` even at this nonzero level.
Nonsingular central conics with nonzero value at their center now have
proved rigidity too: their real support-ring solutions are constants, and
their integer-coefficient omnific solutions have ordinary integer coordinates.
Power differences `x^m − y^n = c ≠ 0` are also proved to have exactly their
ordinary integer solutions when both exponents are positive and their gcd
is greater than one. A checked counterexample, `ω^0 − 0² = 1`, shows why
the positive-exponent condition is necessary; the source remark now includes
it and restricts its pointer to the separated theorem to exponents at least two.

Number-field norm equations now have a complete rigidity proof for every
rational basis: a nonzero rational norm level forces all omnific coordinates
to be ordinary integers. A basis of algebraic integers also gives an integer
norm polynomial, whose omnific and ordinary integer solution sets agree.
The explicit cubic `x³ + 2y³ + 4z³ − 6xyz` now has a checked norm identity
and factorization. At every nonzero ordinary level, its omnific solutions
are ordinary integer triples; its Gaussian omnific solutions are ordinary
Gaussian integer triples. Both statements identify the exact solution sets.
The norm rigidity theorem also extends to finite products of number fields
in arbitrary bases, even when the factors have different degrees. The
Gaussian theorem covers finite products of extensions of ℚ or ℚ(i), and
identifies their Gaussian omnific fibers with the ordinary Gaussian fibers.
The general Hahn-ring theorem is proved for arbitrary characteristic-zero
coefficient fields and ordered abelian exponent groups: at a nonzero
constant norm level,
every solution in an intermediate ring lies in its prescribed ring of
constants. Closure under constant extraction is unnecessary. The proof
extends coefficients to an algebraic closure and descends constancy; it
requires neither divisible exponents nor a least positive exponent.
Over any coefficient field, including positive characteristic, every
nonconstant element of the support ring is now proved transcendental over
that field. Polynomial evaluation multiplies its degree by the polynomial
degree, and roots in an intermediate ring are exactly its constant roots.

The [independent-copies report](docs/surreal/independent-surreal-copies/article.tex)
proposes strong surreal self-embeddings with prescribed common Hahn cores,
and transcendental gaps in arithmetic intersections and ordinary composita.
Its class constructions and proofs remain pending in Lean. Its second
manuscript adds rank tests and differential-transcendence obstructions to
ordinary composita. Its third manuscript studies maximal transcendence in
Hahn joins, mixed-support independence and prime omnific witnesses; these
new proofs await independent review. The latest
dynamics, surcomplex real-form and Hahn–Hilbert additions likewise remain
outside the earlier review scopes recorded in the ledger.

The expanded [critical-point-defects report](docs/foundations-and-computation/large-cardinal-embeddings-and-normal-forms/)
compares two actions of a large-cardinal embedding on surreal normal forms.
Its four manuscripts describe an exact support threshold for their agreement,
measure recovery from a defect coefficient, and criteria for the transformed
series to belong to the target model. These are conditional research claims;
independent proof review and Lean formalization remain pending.

Two recent reports connect omnific arithmetic with other classical
questions. [Continued fractions](docs/surreal/omnific-continued-fractions/)
describes exactly which errors preserve every ordinary finite digit, with
realization and uniqueness criteria in full Hahn fields. [Exponential relations](docs/foundations-and-computation/exponential-relations-over-omnific-integers/)
proposes a decidable language of finite exponential equalities with algebraic
coefficients and slopes, and locates its boundary when multiplication is
admitted. These reports have written proofs and finite checks; independent
proof review and Lean coverage remain pending.
The expanded [dilation report](docs/surcomplex/autonomous-dilation-relations/)
connects a finite-support number's rational support rank with the least order
of an algebraic relation among its exponent dilates. Its two added manuscripts
also treat infinite supports and relative independence; these additions await
independent proof review and Lean formalization.

The [research collection](docs/README.md) also includes work still awaiting
Lean proofs. The [omnific Diophantine report](docs/surreal/omnific-diophantine-geometry/)
exhibits dense arithmetic fibers with opposite denominator behavior and
computes the failure of flatness when finer monomial scales are added.
Its fraction section now has a full manuscript proof review, including
a correction to the agreement locus of standard part and rational residue.
The Gaussian-fiber and étale-norm proofs now spell out their support and
splitting arguments, with boundary examples explaining the hypotheses.
The review now covers squarefree and Weierstrass rigidity and the abstract
two-ring differential principle, including tangent detection and inheritance.
It corrects differential normalization and hypotheses and makes the
geometric pullback argument explicit. The smooth-curve classification now also
has a manuscript proof review: over any characteristic-zero coefficient field,
only the affine and projective lines admit nonconstant points in the nonnegative
Hahn support ring when the exponent group is nonzero. The proof explains descent
and the role of geometric punctures. The arithmetic review shows that an
integer polynomial parametrization covers each entire exceptional fiber,
including infinite-support points; a finite-support witness can always be
chosen in the same fiber. The projective review makes the coordinate-ideal
obstruction explicit and separates rational points from rational specialization.
The singular-curve criterion now has a manuscript proof review as well:
over a characteristic-zero field and a nonzero exponent group, a geometrically
integral affine curve has nonconstant points exactly when its normalization
is the affine line. A conductor and a discrete boundary valuation supply
a finite derivative-order obstruction. This classifies existence without
assuming that every point lifts to the normalization. The review corrects
the ambient-field normality comparison and the zero-group boundary case. The
application review restores the irreducibility assumption in the repeated-root
superelliptic test and expands the singular elliptic certificate and Gaussian
arithmetic existence proof. The group and coefficient-algebra review makes
semiabelian rigidity and the exact unipotent kernel explicit. Rigidity extends
to reduced coefficient algebras. For dual-number coefficients, the quotient
by the ordinary dual-number points is `Lie(A) ⊗ Π_k(Γ)` for an abelian variety `A`.
The logarithmic review extends the differential argument to complements of
simple normal-crossings boundaries, spells out arithmetic descent, and
corrects the distinction between ring retractions and common-field inclusions.
The scope review makes the workspace restrictions and two kinds of smooth
curve fibers explicit, and updates the formalization route to the proved
arithmetic and linear-algebra prerequisites. The subsequent comparison
review distinguishes an affine-line real fiber from an affine-line model
over the integers, and retains the unresolved arithmetic existence case
for singular real curves. It also explains why one nonconstant unit
suffices for curve rigidity through the dimension-one argument.
These geometric and coefficient-algebra results remain pending in Lean.
The same report classifies positive-degree monic polynomials with nonzero
constant discriminant as translates of their constant-term polynomials.
Its elementary lemmas and root-velocity proof have now been reviewed: for
omnific coefficients, each integer root of the constant-term polynomial
lifts uniquely by the same purely infinite translation. The review makes
positive degree and squarefreeness over the coefficient field explicit,
and corrects the example showing why monicity matters. The next review
covers factors, Galois groups, coherent translations and units of finite
étale algebras: every such unit is algebraic over the coefficient field.
It explains the generic field factors and why the constant subalgebra
injects into the reduction fiber, while full descent still requires an
additional hypothesis. The review now covers monogenic and arithmetic
descent and the critical-point and normal-matrix applications. In particular,
a normal matrix over the one-sided complex Hahn ring with nonzero constant
characteristic discriminant differs from its constant matrix by a scalar
purely infinite matrix; its eigenspaces remain ordinary. The boundary
examples and splitting-algebra second proof are also reviewed. These C17
theorems remain pending in Lean, beyond the shared support-ring prerequisites.
The question/status review now separates full faithfulness from existence
of étale descent and supplies an exact affine-conjugacy test: within the
two-translation polynomial normal form, the source and target shifts must
coincide. Full parallel-source reconciliation remains pending review.
The expanded [omnific-automorphism report](docs/surreal/omnific-preserving-automorphisms/)
now assembles fifteen manuscripts. Its latest parts propose formal orbit
fields, actions of set-sized left-orderable groups with prescribed fixed
fields, and formal integration of all omnific derivations. These additions
await independent proof review and Lean formalization; the surcomplex
group classification requires compatibility with conjugation. A further
chapter treats universal symmetries and exact difference equations. The
quotient report adds class residue fields, semialgebraic preservers,
polyhedral-cone cores and henselian branching;
these new claims also await independent proof review.
The [review record](docs/REVIEW.md) distinguishes these written proofs
from formal verification and records the remaining review scope.
Recent manuscript additions cover curve and differential rigidity, theta
descent, support cuts and convex factors, plus a new
[quantum and gauge report](docs/physics/quantum-and-gauge-scale-reductions/).
These additions and the newly delivered companions still need proof review
and source reconciliation.

The complex cosine fold now has its exact infinitesimal root classification,
real and imaginary branch behavior, half-valuation law, and complete strong
inverse-sine expansion. The displayed cubic factor has an exact finite
fourth-order remainder. The exact local angular strong series has order one at separated roots and
order two at collision. Euler's identity identifies the manuscript's
exponential coordinate, and the native polynomial multiplicities agree
with those local orders, completing the cosine fold theorem.

The coupled two-angle collision now has a bijection with two independent
quadratic root sets, the exact arcsine branches, and the complete counts of
distinct complex and real solutions. Its intersection algebra represents the
two diagonal equations in every commutative target algebra and has basis
`1, X, Y, XY` at every parameter. Actual fine partial derivatives verify the
Jacobian and its discriminant locus. The algebra now decomposes into four
field factors, two local dual-number factors, or one local rank-four factor
on the respective collision strata. The local dimensions sum to four.
The verified centered sine series now induces a formal coordinate automorphism
at every infinitesimal root. Together with linear diagonalization and removal
of unit factors, it identifies each angular formal quotient with `(X^m,Y^n)`,
where each exponent is one or two on the corresponding collision stratum.
A coefficient basis proves these formal quotients are finite-dimensional.
Their native local dimensions are one, two and four, agreeing with the
algebraic local factors. The finite sum of angular multiplicities over all
actual infinitesimal solutions is four, completing the coupled collision
assertions.

Conditioned inverse cosine now has its second-order expansion at every
actual interior angle, including angles with infinitesimal sine. The proof
controls the endpoint margin and gives all three valuation bounds under
`v(ε)>2v(sin θ)`. At equality, explicit infinitesimal-angle examples reach
the endpoint or move the target above one, proving the strict threshold
is necessary for a uniform guarantee.

Finite Laurent sums now have a verified polynomial algebraization and the
`2N` root bound on finite real angles modulo ordinary periods. Over an
algebraically closed field, the cleared polynomial has exactly `2N` nonzero
roots counted with multiplicity when both endpoint coefficients are nonzero.
Ordinary-angle values determine all actual surcomplex Fourier coefficients;
real-valuedness is equivalent to conjugate symmetry. Every native Laurent
polynomial now has an exact local angular strong series, even with infinite
coefficients. Its native series order equals the cleared polynomial root
multiplicity, so the `2N` bound also counts actual angular multiplicities.
For every positive ordinary `n`, `sin(nθ)` attains the bound: its roots
have exactly the `2n` classes represented by `jπ/n`, all with angular order
one. Angular differentiation preserves the frequency bound and annihilates
exactly the constants. Consequently every nonconstant real trigonometric
polynomial of degree at most `N` has at most `2N` stationary finite-angle
classes, also when counted with derivative-germ multiplicities. Stationarity
uses the native fine derivative. The global strip exponential and its
root-class correspondence remain pending.

Every everywhere-nonnegative actual surreal polynomial now factors as a
surcomplex polynomial times its coefficientwise conjugate, with exactly
half the original degree. At every real input its value is the squared
modulus of the factor. The proof removes even real-root factors and
strictly positive conjugate-root quadratics, preserving nonnegativity at
each step. It uses the proved square roots and algebraic closedness of the
actual fields. Mathlib homogenization now gives the explicit Fejér–Riesz
polynomial factor of degree at most `N` on the entire actual unit circle.
A top-coefficient identity extends the affine Cayley construction to `-1`.
Nonnegativity at every finite surreal angle is therefore equivalent to
this squared-modulus factorization, including infinite coefficients and
infinitesimal angles. Reflecting every interior root now constructs a factor
with no zeros in the open unit disk, and multiplication by a unit scalar
makes its value at zero positive real. The normalized factor is now proved
unique: equal boundary moduli give equal polynomial norm encodings, which
recover every root multiplicity and hence determine the factor up to a unit
scalar. Positivity at zero removes that scalar. This completes the
Fejér–Riesz theorem on the actual fields, without a compactness or
Hilbert-space assumption. The
factor coefficients now give the exact Fourier autocorrelations: the constant
coefficient is their squared energy, is positive for nonzero input, and bounds
the modulus of every Fourier coefficient. At the highest positive frequency,
twice the coefficient modulus is bounded by the same energy.

The first modules establish size obstructions and reusable finite algebra.
Complexification uses mathlib's `QuadraticAlgebra`, with its cross-term
multiplication, conjugation, and field construction. The modulus takes values
in the ordered base field. Polynomial results reuse mathlib's splitting,
algebraic-closedness, and integrality theorems.
The rational circle chart is an equivalence from the ordered base field to
the norm-square-one points other than `-1`, with inverse `im / (1 + re)`.
It extends to Mathlib's projective line, with the homogeneous direction
product law and an explicit treatment of the point at infinity.
Finite geometry includes Heron's area identity, Ptolemy's inequality and the
positive-quotient criterion for equality in the triangle inequality. Formal
polynomial derivatives give multiplicity, finite Taylor expansion and the
divisibility criterion for equal jets.
Polynomial algebra also includes unique division and factorization, monic
Bézout gcds, principal ideals, and the exact gcd-with-derivative formula.
Finite Hermite interpolation realizes prescribed derivative jets at distinct
nodes by a unique polynomial below the total multiplicity degree bound.
The polynomial CRT identifies the quotient with the product of local jet
rings and provides orthogonal idempotents summing to one. Explicit truncated
inverse jets construct their polynomial representatives, with coefficients
computed by repeated formal differentiation of the reciprocal. The simple-root
case gives the Lagrange formula, with nonzero derivative denominators.
The finite inverse-jet weighted sum gives an explicit Hermite interpolant
after taking its polynomial remainder.
Viète's formula and both Newton recurrences use finite root multisets.
Resultants have their Sylvester determinant and root-product formulas,
with common-root and finite Bézout-kernel criteria.
The native discriminant has its signed-resultant and squared-root-difference
formulas, with squarefree and repeated-root criteria. Strict upper and lower
Cauchy bounds and the radial coefficient bound use the base-field modulus,
including non-Archimedean scales and zero-radius cases.
Gauss–Lucas uses positive convex weights in that same ordered base field;
its barycentric formula retains root multiplicities. Higher-derivative
inclusion keeps the required intermediate splitting hypotheses explicit.
For monic quotients over any commutative coefficient ring, finite remainder
coordinates give multiplication matrices, trace and norm. The top-remainder
coefficient defines a perfect residue pairing with an explicit dual basis,
and multiplication trace equals the residue of the derivative times the class.
These identities also hold with zero divisors, repeated roots and positive
characteristic.
The residue Gram determinant is the fixed reversal sign and its inverse is
the coefficient matrix of the finite bivariate Bézout kernel. The trace Gram
matrix factors as the residue Gram matrix times multiplication by the derivative.
The quotient norm equals the polynomial resultant over every commutative
ring, so the trace Gram determinant equals the native discriminant even
in positive characteristic. A verified formal Laurent inverse also identifies
the residue functional with the coefficient at infinity.

The Hahn layer uses mathlib's `SummableFamily` and proves the full Neumann
support lemma, including finiteness across all word lengths. It distinguishes
Hahn summation from ordinary summation of constant coefficients and exposes
evaluation in finitely many variables with positive-order proofs. Its support
stays in the additive monoid generated by the input supports, with finite
contributions at every exponent. Geometric-series
identities and exact finite remainders are formal Hahn identities.
Evaluation commutes with finite-variable formal composition when every inner
series has zero constant coefficient; a jointly summable double family
justifies the coefficient interchange.
Admissible binomial expansions satisfy exponent addition and give the unique
natural-degree root near one over a characteristic-zero coefficient field.
Over ordered coefficients, the half-power is the unique nonnegative square
root of a positive-order perturbation of one.
Arbitrary regrouping and double-sum interchange preserve jointly summable
families. Coefficient-zero extraction gives standard part on the nonnegative-order
subring, with residue field and a unique constant-plus-infinitesimal decomposition.
Strictly increasing additive exponent embeddings preserve Hahn sums, formal
evaluation in one or finitely many variables, valuations and standard part.
Infinitesimal exponential and logarithm have explicit strongly summable
families and are mutually inverse, by proved formal substitution identities.
Jointly summable products prove the exponential addition law and give a group
isomorphism from positive-order series to units differing from one by positive
order. Coefficient maps preserve strong sums and evaluation; in particular,
exp/log commute with complex conjugation. Near-one series satisfying
`z * conj(z) = 1` have logarithms with purely imaginary coefficients.
For divisible exponent groups, complex Hahn series have a modulus valued in
the ordered real Hahn field. Its unit circle is exactly that algebraic locus,
so the logarithm conclusion also holds under the literal modulus-one condition.
The modulus preserves Hahn order and takes the standard part of a finite
series to the ordinary norm of its standard part. Finite exponentiation
combines ordinary complex exponentiation with the infinitesimal exponential:
it maps onto all units of the nonnegative-order ring and has exactly the
ordinary integral multiples of `2πi` as its kernel.
Every nonzero complex Hahn series is its positive modulus times the finite
exponential of an imaginary finite real angle. These angles are unique modulo
ordinary integral multiples of `2π`.
Each has exactly one representative in the actual ordered interval `(-π, π]`,
and every negative real Hahn input has principal polar angle `π`.
Roots of monic polynomials over this subring stay in it; for split polynomials,
standard part preserves the root multiset with multiplicities.
Resultant and nodal-derivative valuations are finite sums of root-separation
valuations, with infinity retained when a product vanishes.
Discriminant valuations give twice the pairwise separation sum with the
leading-coefficient term; in the monic case they also equal the sum of
derivative valuations at the roots.
The weighted Gauss valuation is the finite minimum of weighted Taylor
coefficient valuations at any center and scale. Its initial polynomial is
nonzero for nonzero input, is multiplicative, and equals coefficientwise
standard part after monomial normalization.
Its support consists exactly of the active indices attaining the weighted
minimum, with degree and trailing degree giving their extrema.
For explicitly split polynomials, the initial factorization counts roots in
closed balls, open balls, shells and individual residue directions, preserving
multiplicities even when their residues coincide.
The resulting Newton profile counts roots at each finite valuation and identifies
its finite set of breakpoints. Perturbations of strictly higher weighted
valuation preserve the entire initial polynomial and these local root counts,
even when the polynomial degree changes. In residue characteristic zero,
differentiating through the initial polynomial's degree lowers the weighted
value by the expected multiple of the scale and differentiates the initial
polynomial exactly. Occupied open and closed valuation balls consequently
contain exactly `k-r` roots of the `r`th derivative in the permitted range,
with explicit splitting assumptions and multiplicities retained.
For squarefree split polynomials of degree at least two whose derivatives
split, each root has a critical point at exactly its nearest-neighbour
valuation, and no critical point is closer in valuation.
Coefficientwise real and imaginary parts identify Hahn series over `R[i]`
with the quadratic extension of Hahn series over `R`. This identification
also uses Mathlib's native real and complex coefficients; conjugation fixes
exactly the embedded real Hahn series and preserves support and valuation.

The independent foundational track now constructs ordinal-length sign
sequences with the numerical first-disagreement order, well-founded prefix
simplicity and an ordinal order embedding. Birthday-bounded fragments are
small, while the full carrier is not small at the same universe level.
Every small separated cut now has a canonical simplest separator with a proved
birthday bound. The cut operation reconstructs canonical sign options, respects
reindexing and satisfies Conway's negation rule. It gives upper, lower and
positive lower bounds for small families. Small sets with no greatest member
have no supremum; embedded finite ordinals give a concrete bounded example.
Conway addition is now constructed by well-founded recursion with proved
option separation. Its zero, commutativity, associativity, inverse and order
laws make the sign carrier an ordered additive commutative group. The addition
cut equation also holds for arbitrary small presentations of the summands.
Native natural-number casts agree with finite all-plus sequences, and integer
casts form an additive order embedding. Subtracting one from any upper bound
of the naturals proves directly that they have no supremum.
The ordered field extends these casts to rationals and ordinary reals.
Halving any upper bound of the naturals gives another strictly smaller upper
bound. The all-plus sequence of length omega exceeds every embedded real;
its reciprocal is positive and smaller than every positive embedded real.
Ordinal signs use Hessenberg natural addition and multiplication, with an
explicit counterexample to preservation of ordinary ordinal addition.
In its native order topology and compatible additive uniformity, every small
subset is closed and discrete, convergent small-index nets are eventually
equal to their limits, and small-index Cauchy nets are eventually constant.
The whole carrier has no isolated points. Neighborhoods and entourages use
absolute differences valued in the sign carrier itself.
The net of all positive radii, directed by reverse order, converges to zero
and is Cauchy but is never eventually constant. Its index type is proved
not small at the lower universe level.
Canonical sign options also define a small, well-founded game graph. Its
recursive game construction preserves and reflects comparison, proves the
image games numeric, and gives an explicit order isomorphism with the reused
numeric-game surreal field. Every small cut is preserved, and induction on
numeric-game options proves surjectivity. The bridge preserves the original
Conway addition, sign reversal, zero and one. Transporting the proved game
multiplication and inverse then makes the sign carrier an ordered field,
retaining its original additive structure and numerical order.
This product satisfies Conway's four-family simplest-cut equation, with
small option indices and proved separation.
The equation also holds for arbitrary small presentations of both factors.
The empty and one-plus sequences map literally to the raw games zero and one.
The numeric-game quotient also satisfies the indexed small-cut interface and
its comparison rule, including reconstruction from a numeric game's moves.
The canonical raw-game birthday equals sign length and is minimal among
all numeric games representing the same number.
The birthday of a sum is bounded by the Hessenberg natural sum of the input
birthdays, with the corresponding finite-sum bound. This natural sum also
strictly decreases under either canonical option replacement.
Finite birthdays characterize exactly the embedded dyadic rationals. They form
a subring, but the reciprocal of three has birthday omega, so this fragment
is not a subfield. Every embedded ordinary real has birthday at most omega;
the non-dyadic reals have birthday exactly omega.
For a dyadic value with reduced denominator `2^k`, the exact birthday is
the ceiling of its absolute value plus `k`. Its standard dyadic game attains
this same minimum birthday.
For all embedded ordinary reals, the product birthday is bounded by the
Hessenberg natural product of the factor birthdays.
Every nonnegative sign number now has a unique nonnegative square root,
constructed by simplicity induction and a countable closure of small
algebraic option families. The resulting `sqrt` takes zero on negative inputs.
The concrete surcomplex field is now the quadratic extension of that sign
field. It has the coordinate product, conjugation and inverse formulas, a
positive surreal-valued norm square away from zero, and dimension two over
its real subfield. Its carrier is also not small at the birthday universe.
Its native topology and uniformity are the product of those on the two surreal
coordinates. Balls defined by `normSq (z - a) < r²`, for positive surreal `r`,
give the neighborhood and entourage bases without requiring square roots.
Small subsets are closed and discrete; convergent small-index nets are
eventually equal to their limits, and small-index Cauchy nets are eventually
constant. The full surcomplex carrier has no isolated points.
Multiplication is jointly continuous, inversion is continuous away from zero,
and conjugation is a uniform equivalence. The real-axis positive-radius net
converges to zero and is Cauchy without becoming constant; both its index
type and range are proved not small at the permitted universe level.
The proved square roots also instantiate the actual surreal-valued modulus,
its multiplicativity, triangle inequality, coordinate bounds and inverse
formula. Its balls give exactly the existing fine topology and uniformity.
Heron's area formula, Ptolemy's inequality and the positive-quotient
triangle-equality criterion now apply to the concrete surcomplex field.
Both strict Cauchy root bounds also apply to actual surcomplex polynomials.
Ordinary complex numbers embed coordinatewise into this field, preserving
conjugation and identifying their real norm with the surreal modulus.
Fine-continuous maps with small range are constant on preconnected domains;
in particular, ordinary real intervals admit no nonconstant fine-continuous paths.
Gauss–Lucas and its multiplicity-weighted barycentric formula are instantiated
with explicit splitting hypotheses; higher derivatives retain the required
splitting of each preceding derivative.
The actual finite surreal and surcomplex valuation rings have standard-part
homomorphisms onto ordinary real and complex numbers. Their kernels are
exactly the infinitesimals, their residue quotients are the ordinary fields,
and each finite element has a unique constant-plus-infinitesimal decomposition.
These predicates agree with natural-number absolute-value and modulus bounds.
On the sign field, finite and infinitesimal sets and their nonzero affine
images are clopen; scaled monads separate points in the native order topology.
The coprime binary product linearization is an isomorphism on bounded-degree
polynomials over any commutative ring, providing unique finite corrections
for the support-controlled factor lift. Recursing on a formal parameter now
gives unique binary lifts, packaged as actual polynomials over a power-series
ring with preserved monicity, degrees, constant specializations and coprimeness.
The same construction now handles arbitrary families of formal parameters by
recursion on total degree. A universal finite-parameter polynomial represents
every lower-degree coefficient perturbation. Coprime reductions also determine
any finite family of monic factors uniquely, both in Hahn valuation rings
and in the actual finite surcomplex ring. Evaluating the universal formal
factors now proves full finite-family Hensel lifting in Hahn valuation rings:
the lower-degree corrections have positive supports inside the monoid generated
by the original errors. Every simple residue root lifts uniquely with the
same support control.
Simple-root existence and uniqueness now also hold directly in the actual
finite surreal and surcomplex rings, without a monicity assumption. The
proof places the coefficients in one small Hahn workspace and compares
all actual candidates by divided differences. In particular, a real
polynomial reducing to `Y+b₀` has a unique finite root with standard part
`-b₀` and native multiplicity one, supplying the trigonometric stability
lemma. The actual complex lift is a unique infinitesimal correction;
transfer of the Hahn support and first-coefficient bounds remains pending.
For actual real polynomials, the stability normalization now gives a unique
simple root throughout `v(h)>κ` when `v(A)=κ≥0`, the constant and linear
errors have valuation at least `σ>2κ`, and higher coefficients are finite.
It proves both `v(h)≥σ−κ` and `v(h+P(0)/A)≥2σ−3κ` for actual surreal
exponents. Mathlib Laurent polynomials now have exact real numerators in
Cayley coordinates, with a positive denominator and coefficient valuation
bounds. Applying the polynomial theorem proves both bounds and uniqueness
for the exact trigonometric pullback in `x=2 tan(h/2)`. The inverse chart
preserves valuation and has a finite cubic remainder, transferring both bounds
to the actual angle `h`. The formal Fourier derivative is the native fine
derivative, and the perturbed angular root is simple and unique throughout
`v(h)>κ`. The sine-square witnesses also prove sharpness: for every positive
surreal `κ` and every `σ>2κ`, constant perturbations attain both error bounds
exactly. At `σ=2κ`, cancelling the constant term leaves no root in the original
neighborhood. These complete the angular stability theorem and its sharpness
proposition.
In the Hahn theorem, the first correction coefficient is the negative error coefficient evaluated
at the residue root, divided by the residue derivative; cancellation is allowed.
The distinct complex residue roots also index unique cluster factors, with
the prescribed multiplicities and a characterization of every existing Hahn
root by its standard part.
For divisible ordered exponent groups, weighted monomial scaling and the
Hensel lift now support induction on polynomial degree. Hahn fields over
algebraically closed characteristic-zero coefficients are proved algebraically
closed. Hahn fields over ordered real closed coefficients are proved real
closed: nonnegative square roots are constructed from the leading monomial
and the binomial series, and odd-degree roots follow by degree induction.
Thus complex Hahn polynomials split in their original workspace, with unchanged
root multiplicities in every field extension.
The rational span of a small set of actual surreal exponents together with
one supplies a small, nonzero divisible exponent group. Its real and complex
Hahn fields are small and inherit those closedness results. Small families
of exponent sets admit a common such enlargement, while no single small
exponent workspace contains all actual surreal exponents.
Conway monomials and leading exponents now act on the actual sign field.
Finite monomial expressions form an injective ring map into that field for
every strictly increasing additive exponent map. Their valuation, leading
coefficient and positivity agree with their finitely supported Hahn series.
Full order comparison is decided by the first coefficient that differs,
and evaluation gives an ordered ring isomorphism onto its actual range.
Finite complex coefficient forms likewise embed in the actual surcomplex
field, preserving valuation and the complex leading coefficient.
The monoid algebra also embeds into Hahn series with image exactly the
finite-support series, giving unique finite coefficient representations.
A maximum of finitely many weighted exponents gives a positive scale making
all coefficients finite while preserving at least one nonzero real residue.
The full finite-family coprime-factor linearization is proved over arbitrary
commutative rings, including empty families and constant factors.
On the actual surcomplex field, the finite ring, infinitesimal monads and their
nonzero affine images are clopen, and the fine topology is totally separated.
Halos are finite standard-part preimages; puncturing removes a whole monad.
The explicit point `1 - omega⁻¹` distinguishes the halo of the ordinary disk
from the full fine unit ball. No point has a countable neighborhood basis,
so no ordinary real-valued metric or pseudometric induces the fine topology.
Leading-coefficient normalization, translation to depressed form, and
monomial change of variable now preserve polynomial degree and give explicit
root pullbacks. Standard-part reduction preserves monicity and supplies
a nontrivial depressed real polynomial; its coprime monic factorization
has a proper positive odd-degree factor. The actual sign and surcomplex
fields also carry additive valuations with surreal exponents and infinity
at zero. Their finite rings agree with the existing modulus-bounded rings,
and valuation lower bounds give the documented monomial modulus estimate.
Actual surcomplex leading coefficients are multiplicative. Each nonzero element
is its leading monomial times (a nonzero complex constant plus an infinitesimal);
its modulus has the ordinary norm as leading coefficient. Removing the leading
term strictly raises valuation. A root of a monic surcomplex polynomial with
finite coefficients is finite. For explicitly split monic polynomials,
standard part preserves the linear factorization and root multiplicities.
The surreal field is not algebraically closed, and no linear order is
compatible with surcomplex multiplication.
Real closedness of the actual sign field is now proved, and small strong
real and complex sums are constructed through canonical normal forms.
The bridge now has an explicit formal carrier of small reverse-well-ordered
supports, reusing the pinned upstream ordinal truncation APIs. Recursion on
support length constructs a canonical actual surreal candidate: the simplest
point meeting all recursive truncation bounds. Its leading exponent and
coefficient agree with the formal form; zero, positivity and nonnegativity
are preserved and reflected, and negating the form negates the candidate.
Truncations evaluate to prefixes. The first differing coefficient gives full
order comparison and injectivity. Ordinary real constants and unit-coefficient
Conway monomials evaluate exactly. Birthday bounds make all partial approximations to a fixed target
small. Unions of their initial-segment chains and a residual-extension lemma
then give surjectivity by Zorn's lemma. Evaluation and canonical extraction
therefore form an order isomorphism with proved inverse laws.
Every real multiple of a Conway monomial evaluates exactly. Mutual prefix
comparisons prove addition by support-length induction and multiplication by
actual-birthday induction. The latter uses the formal product's support and
the leading term of each remaining product of tails. Evaluation is now an
ordered field isomorphism, including inverses, quotients, powers and rational
casts, and agrees with the independently constructed finite evaluation.
Every small real Hahn workspace embeds into the formal field and the actual
sign field through its strictly increasing additive exponent map, preserving
coefficients and lexicographic order. Any small family of formal forms lies
in one small divisible workspace. In particular, polynomial coefficients
descend to such a workspace, whose odd-degree root theorem transfers back
through the injective embedding. Together with the independently constructed
nonnegative square roots this proves real closedness of both fields.
Normal-form extraction puts every small family of actual surreals inside
one small Hahn subfield and preserves degree when descending polynomials.
Localizing both coordinates of a surcomplex polynomial's coefficients in
one complex Hahn workspace proves actual algebraic closedness, linear
factorization, and equality of root multiplicity count with degree.
The real Hahn embedding preserves valuation and leading coefficient for
arbitrary supports. Finite values have nonnegative Hahn order, infinitesimal
values have positive order, and standard part extracts the zero coefficient.
The complex embedding also preserves valuation, leading coefficient,
finiteness, infinitesimality, and standard part. Its leading-term and modulus
decompositions retain the native coefficient and exponent. Every small actual
complex family lies in a common small complex Hahn subfield. Both embeddings
commute with exponent-workspace enlargement.
Actual strong real and complex sums use the two native Hahn summability conditions:
well-ordered joint support and finite coefficient fibers. Small index types
give small sum support, and workspace evaluation commutes with these sums.
Strong sums respect addition, negation, jointly summable products, and arbitrary
fixed scalars. Small real and complex families can be reindexed and regrouped
along any index map, with Fubini for jointly summable double families. Strong
sums agree with finite field sums. Constant families are strongly summable exactly when finitely many
are nonzero, so the ordinary geometric constant family is not a strong sum.
Every real or complex formal power series evaluates at actual infinitesimals,
including zero, with no coefficient-growth restriction. Evaluation is a ring
homomorphism, equals the displayed strong sum, preserves the constant standard
part, and commutes with formal composition with zero inner constant term.
These results also hold for arbitrary formal series in finitely many actual
infinitesimal variables, including zero inputs and an empty variable type.
Infinitesimal geometric strong sums equal `(1 - x)⁻¹`, with exact finite
remainders and valuations. For nonzero inputs their partial sums have no
limit in the fine topology. At `x = t`, the remainder exceeds the named
radius `t^ω` for every finite partial sum.
Actual infinitesimal exponentials and logarithms are mutually inverse,
respect their group laws, and commute with conjugation. The logarithm of
a modulus-one element near one has zero real part. Ordinary real and complex
binomial exponents give unique roots near one; the real half-power agrees
with the constructed square root.
Formal-variable images under homomorphisms into ordered fields must be
infinitesimal. Every actual surreal infinitesimal occurs as such an image,
and actual real or complex evaluation is injective exactly at nonzero inputs.
Its valuation is the first nonzero formal degree times the input valuation,
with explicit leading coefficient and growth exponent. Evaluation preserves
source-summable families and their small strong sums; coefficient fixing,
strong additivity and the variable image uniquely determine it.
The actual finite exponential maps onto the finite units with exact kernel
`2πiℤ`. Every nonzero surcomplex has a finite-angle polar representation,
and two finite angles give the same phase exactly modulo ordinary `2πℤ`.
Each has a unique principal angle in `(-π, π]`, with angle `π` for every
negative real input, including infinite and infinitesimal scales.
The finite-angle quotient by ordinary full turns is isomorphic to the full
actual unit circle. Each direction splits canonically into its ordinary
standard-part direction and an additive infinitesimal angle, recovered by
the strong logarithm. Positive moduli times these angle classes form the
multiplicative group of all nonzero surcomplex numbers, without any bound
on their size.
Directions have unique representatives in both `[0, 2π)` and `(-π, π]`,
with actual endpoint inequalities deciding infinitesimal corrections.
Every positive surreal has a unique positive natural root. Every nonzero
surcomplex has exactly `n` roots of positive degree `n`, with the explicit
polar formula; roots of unity are exactly the embedded ordinary complex
ones. The regular polygon side formula holds at every positive radius.
The rational Cayley chart covers every actual direction except `-1`, with
inverse half-angle tangent; its projective extension supplies that point and
transports homogeneous addition to direction multiplication. Infinite surreal
parameters give precisely the affine directions infinitesimally close to `-1`,
while never equaling the projective point itself. This includes the explicit
parameter `omega`.
Inverse sine and cosine are defined and uniquely invert their actual closed
angle intervals, including inputs infinitesimally close to either endpoint.
Inverse tangent is an increasing bijection from all surreal slopes onto its
finite open angle interval, with the square-root coordinate formulas and
positive-input reciprocal complement identity. The inverse-sine half-angle
formula holds at both endpoints. Tangent has fine derivative `1+tan^2`.
The inverse functions have their native fine derivatives on their full open
domains: `1/(1+t^2)` even at infinite tangent inputs, and the positive or
negative reciprocal square root for sine and cosine even infinitesimally
close to the endpoints. Their continuity follows from the actual interval
order isomorphisms; a general topological-field inverse rule supplies the
derivatives. Geometric inverse tangent and sine agree with their ordinary
analytic Taylor lifts on the corresponding finite analytic domains. Inverse tangent has the
full alternating odd-power strong series at infinitesimals, with a finite
seventh-order remainder after degree five. Substitution of the reciprocal
gives the expansion at every positive infinite slope, including `omega`,
and proves that its angle is strictly and infinitesimally below `pi/2`.
Inverse sine has the full central-binomial strong series, with an exact finite
ninth-order remainder after degree seven. Both inverse sine and inverse
tangent preserve valuation at infinitesimals: each is its input times a
finite factor of standard part one. At every positive infinitesimal defect,
inverse cosine satisfies the exact square-root half-angle identity and full
central-binomial strong series. Its normalized cubic expansion has a finite
fourth-order remainder, and its valuation is half the defect valuation.
At both inverse-sine endpoints the inward difference quotient eventually
exceeds every fixed surreal bound, including infinite bounds, so no
surreal-valued one-sided or fine derivative exists.
Angular distance on the actual unit circle satisfies the metric axioms and
the exact chord formula, with Jordan comparison bounds and identical
angular/chordal valuation. Directions with equal standard part have a unique
infinitesimal relative angle, given by the strong logarithm; its absolute
value is their angular distance. The normalized chord and cosine-defect
factors have full strong series and exact finite remainders.
Phase differences preserve the exact infinitesimal angular valuation and
have the expected complex linear term with infinitesimal relative error.
Rotation displacement obeys the exact half-angle chord formula at arbitrary
radii. Rotating by `omega^-1` gives displacement equivalent to one at radius
`omega`, and infinite displacement at radius `omega^2`.
For every relatively infinitesimal perturbation of a nonzero surcomplex
number, the geometric direction change is the imaginary local logarithm.
Its quadratic expansion has a bounded cubic remainder, and its valuation
is at least that of the relative perturbation, with equality when the
leading coefficient has nonzero imaginary part.
Noncollinear triangles at arbitrary surreal scales have unique interior
angles in `(0, pi)`, with the normalized dot product and area as cosine
and sine coordinates. Their three angles sum exactly to ordinary pi,
including their infinitesimal parts. The included-angle cosine and area
laws also hold without restrictions on side lengths.
Every such triangle has a unique circumcircle with positive actual radius
`abc/(4*area)`. All three side-to-sine ratios equal twice that radius,
and the tangent law has positive denominators on its prescribed domains.
The least of the three side valuations is attained at least twice.
Right triangles are characterized by Pythagoras. Each acute angle is the
inverse tangent of its opposite-to-adjacent leg ratio, and explicit
triangles realize every positive surreal slope, including infinite slopes.
Positive side lengths determine a noncollinear triangle exactly when all
three strict triangle inequalities hold. Its angles are recovered by
inverse cosine, and equal side data gives an affine isometry preserving
actual surreal distances. Positive finite angles summing to pi and any
positive surreal scale also determine a triangle. Equal angles give an
actual affine similarity; one specified positive side fixes the scale.
The SAS and ASA constructions also have existence and congruence theorems.
Heron's formula gives the positive half-angle square-root identities.
The side-weighted incenter has a unique perpendicular contact with each
side line, strictly inside the side segment, at radius equal to area
divided by semiperimeter. It is the unique interior equidistant center.
The internal bisector divides its opposite side in the prescribed ratio,
has length `2bc*cos(alpha/2)/(b+c)`, and makes two actual equal half-angles.
Euler's center-distance identity gives `|O-I|^2 = R*(R-2r)`.
The radius inequality `2r ≤ R` and the sharp area bound
`area ≤ s^2/(3*sqrt(3))` have equality exactly for equilateral triangles,
at arbitrary positive surreal scales.
Interior cevians satisfy the exact side-weighted sine ratio, which
uniquely characterizes the internal bisector. Trigonometric Ceva gives
an equivalence between concurrence of the three actual affine lines and
the product of their positive split-angle sine ratios being one.
Every positive-radius circle is parametrized by finite actual angles,
with exact signed chord factorization and chord length at every surreal scale.
The directed inscribed angle modulo ordinary pi is half the central angle
modulo ordinary two pi; halving is well-defined on these quotient groups.
Observers on either common open arc see equal actual interior angles,
and every angle subtending a diameter is right.
Four points in finite-lift cyclic order satisfy Ptolemy equality,
including when consecutive arcs are infinitesimal.
Finite regular polygons have distinct vertices and a proved closing edge;
summing their actual edge lengths and center-triangle areas gives the
exact perimeter and area formulas at every positive surreal radius.
Squared side lengths and squared angle sines satisfy the spread, cross,
and triple-spread laws, with rational expressions in the actual coordinates.
An interior angle's sine has the valuation of its distance from the nearer
endpoint of `(0, pi)`. The triangle laws then give exact valuation formulas
for side ratios, area, semiperimeter factors, and both circle radii.
For two infinitesimal interior angles, their ratio is algebraically
equivalent to the opposite side ratio, even when those ratios are infinite.
The triangle-inequality defect has its exact half-angle formula and a
quadratic equivalent with effective length scale `ab/(a+b)`, without
requiring comparable vector lengths. For a largest triangle side, the
opposite angle is infinitesimally close to pi exactly when the side gap
is infinitesimal relative to `bc/(b+c)`. Its full inverse-sine strong
series gives square-root equivalents and exact valuation formulas for
the angle supplement, area, and circumradius at arbitrary surreal scales.
Normalized triangles with vertices `0`, `1`, and `x + i*y` now have exact
arctangent base angles and finite-remainder expansions for their sides,
quadratic slack, circumradius and inradius. Positive leading residues
prove all six height-valuation identities, including the supplement of
the upper angle. The coordinate formulas also hold for arbitrary positive
surreal base length and height before any infinitesimal specialization.
The two symmetric examples are realized by actual triangles. An infinitesimal
height gives an exact infinite circumradius despite uniformly bounded vertices;
its inradius has the stated cubic and quintic corrections. An infinitesimal
side gap gives full strong series for the angle supplement, altitude and
circumradius, with the corresponding square-root valuation scales.
The omega-squared-side example has gap exactly one and infinitesimal angular
defect, while its area and circumradius are infinite with the stated equivalents.
A right triangle with reciprocal legs has area exactly one half and the
stated inradius expansion at every positive infinite scale. Thin coordinate
triangles retain their exact formulas at arbitrary side scales; the omega-base
and epsilon-offset families realize finite and infinite radii and distinct
infinitesimal angle scales, including the full omega-family angle series.
First-harmonic equations with a nonzero normal vector have an exact zero, one
or two solution classification modulo ordinary full turns, at any surreal scale.
The explicit line-circle points have the stated derivative and Jacobian magnitudes; the
tangent solution has zero first derivative and nonzero second derivative.
Near tangency, the two angle branches have square-root splitting. Signed
perturbations retain the exact finite remainder at relative rate `e/tau`
and the half-valuation loss. The nearby finite circle points also realize
the example's infinite rational half-angle coordinates.
The line-circle coordinate algebra is the quadratic quotient at every
discriminant, with dimension two and a perfect residue pairing of determinant
minus one. Its universal property includes nonreduced target algebras;
at tangency it is the dual-number algebra. Verified local Laurent expansions
give the two simple residues and the derivative formula at a double root.
For positive infinitesimal separation, the two constant-numerator residues
are individually infinite and cancel exactly.
Finite phase coordinates give sine and cosine with ordinary-constant agreement,
addition identities, parity, periodicity and integer de Moivre.
Recentered ordinary real and complex analytic germs evaluate by their actual
Taylor strong sums, preserving sums, products, correctly recentered composition
and standard parts. This Taylor rule uniquely specifies the extension on its
finite analytic domain. Fine derivatives
use every positive surreal tolerance: polynomials have their formal derivatives,
formal evaluation differentiates at every infinitesimal point, and Taylor lifts
have the lifted ordinary derivative throughout their infinitesimal monads.
An exact bivariate quadratic remainder supplies a uniform ordinary bound.
The chain, reciprocal and quotient rules hold, and finite sine and cosine
agree with their separate even and odd strong Taylor sums and analytic lifts.
Their fine derivatives are cosine and negative sine at every finite input,
and the real-parameter surcomplex phase derivative is `I * cis`.
An analytic germ of finite ordinary zero order lifts to its leading monomial
times one plus an infinitesimal, with the exact predicted valuation and leading
coefficient. For real germs that monomial also determines the sign.
Ordinary analytic nonnegativity on a closed interval lifts to every actual
surreal point between its endpoints, including infinitesimal endpoint
displacements. Finiteness and the permitted one-sided signs follow from
the interval hypotheses. Strict positivity on an ordinary open interval also
lifts to every actual interior point when the function is analytic on the
closed interval. This proves the finite trigonometric signs, strict
monotonicity on the principal intervals, Jordan's inequality, the absolute
sine bound, and the strict sine/input/tangent comparison, including
infinitesimal distances from the endpoints. The explicit sine and tangent
expansions through degree five and cosine defect through degree four have
finite normalized remainders. Their exact valuations and infinitesimal
relative errors give the stated algebraic asymptotic equivalents. Prescribing
the ordinary Taylor rules on every monad uniquely determines the finite pair.
A nonconstant infinitesimal-coset indicator has zero fine derivative everywhere.
The approximation inequalities alone never give uniqueness: a sufficiently
small positive monomial produces another solution. Multivariable analytic
lifting and universe coherence remain separate obligations.
The reports placed after the canonical inventory are formalized clause by
clause. Strong sums of nonnegative Hahn series are nonnegative, and strongly
summable weights define strong Hahn measures on all subsets, additive on every
set-indexed disjoint family, with pushforwards and coefficientwise integrals.
Neumann's lemma bounds the words with a given sum without an Archimedean
hypothesis, and labeled word products, finite-subset products and the infinite
product `∏(1 - q_n)` are strongly summable. Prony's Hankel factorization,
determinant, uniqueness up to permutation and exact last-moment annihilator hold
over any field. The negative-atom Toeplitz matrices are positive definite for
every ordinary size at a positive infinitesimal, with exact Schur iterates.
Resolvent identities, projection-flag generators and rank-one completions are
exact, cofinite spans stabilize after one finite deletion, the Wick diagram
kernel has a finite indecomposable Hilbert basis, and valuations of
positive-definite Hahn matrices obey Cauchy–Schwarz.
The Wick atoms of every sector are strongly summable exactly when the
valuations admit a strictly balancing vector; otherwise the multiples of a
Hilbert-basis element give a non-summable family. The Hahn–Tate theta family
is strongly summable exactly on `U_q` and satisfies `θ(qu) = -u⁻¹θ(u)` for
every value group and coefficient field, and the partial theta series has its
exact strong domain. Hahn extension keeps the point spectrum of a bounded
normal operator, while the backward shift acquires the eigenvalue `t^η`.
Invariant strong measures are averages over finite orbits, a negative atom
with finitely many earlier atoms is detected by a polynomial square, the
critical values of a polynomial are the roots of `Disc(P - Y)` with their
multiplicities, Prony's cofactor corrections obey the valuation budget
`κ - E_i`, and polynomial iterates are equicontinuous at every point exactly
when the value group has no order unit.
The functions `1 - z/2^n` have independent square classes, a nonzero
`R(X, Y)` vanishes at `(n, 2^n)` only finitely often, and every infinite
family of the resulting jet vectors spans. Row- and column-finite matrices
form an algebra with the finite row-by-column product. Sign-coherent Wick
families are strongly summable exactly when their block sums are. When the
constants are uncountable, countably many nonzero polynomials are all nonzero
at one constant point, the unit-orbit and affine valuation lemmas and the torsion
covariance of entire Hahn functions hold for every value group, and the
exponential profile theorem holds over any ordered field equipped with an
ordered exponential and a nontrivial convex valuation.
Admissible exponent sets form cones with the period-inequality criterion,
the bounded-orbit locus of an expanding polynomial is exact, and a
stochastic compressed resolvent family determines a unique row-Laplacian generator.
Prony's perturbed annihilator has exactly one simple root in each
nearest-neighbour ball, the non-monic residue-simple Hensel lemma holds, and
the Hermite rows of the moment differential are exact. Independent square
classes give multiquadratic extensions of full degree with every sign
automorphism, extended coefficientwise to Hahn series, and finite base change
commutes with Hahn series. The vectors `(n^{-r})` have continuum many
independent classes modulo the range of `diag(1/n)`. Jensen's disk theorem
and the weighted incomplete-polynomial hull hold over every ordered field.
The Euler derivation preserves `K_Γ` exactly when `Γ = {0}` or `1 ∈ Γ`, and a
primitive of `1` is transcendental. Every nonzero noncyclic ordered abelian
group has continuum many translation classes of descending positive profiles,
and quadratic lattice energies admit finite minimum certificates.
For positive-definite covariance the Wick atoms are strongly summable exactly
when every `δ_a = λ_a + ½ Σ α_i^a c_ii` is positive, with an explicit balancing
vector and the stationary power-counting criterion. If a positive strong
measure has infinitely many atoms of valuation below `γ`, adding any signed
measure that starts at scale `γ` keeps every nonzero polynomial square
strictly positive. Moment sequences of positive strong Hahn probabilities are
characterized row by row, and the scalar Herglotz lemma holds on the halo.
The matrix-forest expansion gives the determinant, adjugate
and resolvent of a row Laplacian with nonnegative stochastic entries. Graded
quadratic forms over Hahn fields, the Newton-sum Hankel matrix, residue change
of variables for Laurent differentials, the small-divisor tree bound and the
diagonal resolvent clauses of the row-finite spectral theory are proved.
Coefficientwise sums of nonnegative real Hahn series are positive with the least
valuation, and order-limit additivity forces finitely many nonzero masses, so
it has no Lebesgue extension. The negative-atom measure has its signed
representation and unique Fourier moments. Prony weight errors incur no second
conditioning loss. The residue shadows of Hahn row-Laplacian resolvents satisfy
the same-scale and cross-scale identities and are stochastic, which leaves only
the endpoint limits for the effective-generator theorem. Truncated Wick sums
obey the valuation error estimate, the multipliers of expanding polynomial
dynamics are exact, the algebraic coefficient part is closed, the Tate
discriminant has `v(Δ) = v(q)`, the all-scale coefficient criterion decides
entireness, and every positive-order perturbation of `diag(1/n)` keeps a
cokernel of dimension at least the continuum.
Prony's main theorem holds in full: above the threshold `Θ` the perturbed
moments have a unique regular realization labelled by the strict
nearest-neighbour balls, with the node and weight error bounds, and a
last-moment perturbation shows that `Θ` is sharp. Positive root-of-unity
quadratures converge to the nonpositive negative-atom measure. The
effective-generator theorem holds for the actual residue shadows at every
scale. The row-finite Hahn inner product is positive with its valuation
formula and adjoint relation. Automorphisms of `F(i)` are classified by their
logarithmic modulus, and the extended valuation has kernel `{id, conjugation}`
over every ordered field with square roots and a convex valuation. Also proved:
the finite lattice estimate for multivariate domains, differential rigidity of
holonomic entire Hahn functions, strong measures with actual surreal and
surcomplex masses, and invariance of the Tate construction under exponent
embeddings with its abstract extension obstruction.
Positive forest sums of Hahn row Laplacians have no cancellation (relative
stability, leading terms and remainder control). The projection-flag generator
has exactly the prescribed plateaux and crossovers, its completion keeps the
same shadows, and the initial eigenvalue factors follow the Newton profile.
Gaussian integration by parts holds for the closed Wick moment formula. The
Fejér densities give positive coefficientwise measures with a fixed Haar
leading coefficient whose limit is not positive, and one positive measure
needs the full null ideal. Under Prony's finite coefficient criterion the
moment map sends the tangent lattice onto the error ball. Strongly entire functions
are closed under the algebra operations, dilation and differentiation, and
the refined periodic threshold holds under divisibility. Value-group
automorphisms now have canonical lifts on the actual surreal field, preserving
strong sums. The no-exponential-lift result for rational dilations is proved
at the actual carrier conditionally on a global ordered exponential; its
construction remains pending.
A successful build proves only the imported Lean
statements, not coverage of all the source documents.
