# The surreal and surcomplex reports

Twenty-six research packages, in five families. The typeset catalogue is
[`manifest.pdf`](manifest.pdf) (source [`manifest.tex`](manifest.tex)); it
gives a paragraph on what each report claims. This page is the map: which
family a report belongs to, and what to read before what.

Every directory holds `article.pdf`, its LaTeX source, a `README.md`, and in
most cases `code/` with verification programs and `data/` with the recorded
output of running them. The source manuscripts a merged report was assembled
from are not distributed here. What is kept is the provenance record: each
merged report says how many manuscripts went into it, what each contributed,
and where the merge had to choose between them, and the disposition of every
source result is recorded in that material.

These are AI-assisted drafts. None is refereed or machine-checked.

## `surreal/` — the surreal field **No**

Eight reports, independent of each other. Read in any order.

| directory | subject |
|---|---|
| [`hahn-evaluation-at-omega`](surreal/hahn-evaluation-at-omega/) | Lipparini's Problem 7.7, answered negatively |
| [`broadcast-sum-of-surreal-sequences`](surreal/broadcast-sum-of-surreal-sequences/) | Lipparini's sign-truncation game, Remark 7.6(3) |
| [`gonshor-product-birthdays`](surreal/gonshor-product-birthdays/) | Gonshor's `b(xy) ≤ b(x) ⊗ b(y)` on ordinal-support normal forms |
| [`gonshor-laurent-birthdays`](surreal/gonshor-laurent-birthdays/) | the same bound on `R((ω⁻¹))` |
| [`canonical-forms-need-not-be-subgraphs`](surreal/canonical-forms-need-not-be-subgraphs/) | Roughan's Figure 3 question, answered negatively |
| [`genetic-gaps-and-primitives`](surreal/genetic-gaps-and-primitives/) | a genetic indicator with derivative zero that is not constant |
| [`exponential-automorphism-rigidity`](surreal/exponential-automorphism-rigidity/) | a nonidentity exponential automorphism must displace the value group cofinally |
| [`gamma-functions`](surreal/gamma-functions/) | which surreal Gamma extensions are convex, and why Bohr–Mollerup fails |

The two Gonshor reports prove the same inequality and **neither contains the
other**: the first allows arbitrary ordinal supports but excludes `ω` and
every positive power; the second contains `ω` and its powers but restricts
supports to order type at most `ω` on the integer lattice. On their common
corner `R[[ω⁻¹]]` they agree, and the result is proved twice. They are kept
separate deliberately — a future sweep should not merge them.

**`exponential-automorphism-rigidity`** and **`gamma-functions`** are the two
standalones. Each can be read entirely on its own; nothing else here studies
the automorphism group of `No`, and nothing else here has a Gamma function,
a log-Gamma or a Stirling series in it.

The first turns on one finite lemma. For a unital field endomorphism `σ`, the
displacement `D(x) = σ(x) − x` is additive but is **not** a derivation; the
rule is the *twisted* identity `D(ab) = σ(a)·D(b) + b·D(a)`, with `σ(a)` and
not `a`, and two probes then force `D` unbounded. Applied to an ordered field
with a surjective ordered exponential and a nontrivial convex valuation, this
makes `ρ_w: Aut_exp(F; O_w) → Aut(Γ,+,<)` injective, and on `No` it makes
every exponential 1-automorphism the identity — the report's claimed negative
answer to Question 5.4 of Kaplan–Krapp–Serra, arXiv:2509.22374v3. **The
version pinning is deliberate.** The claim is against one arXiv version, and
this collection holds no other automorphism material to check the reading of
that question against.

The second classifies the family `L_a = L_0 + h_a` with
`h_a(x) = a(M(x))·pp(x)`: `L_a` is convex on `No_{>0}` **iff** `m·a(m)` is
finite for every positive infinite monomial `m`, and then strictly convex.
Since every member of the family — convex or not — keeps `Γ_a(1) = 1`, the
recurrence, every finite Gauss multiplication formula and every positive-order
fine derivative of log-Gamma, **Bohr–Mollerup fails on `No` in the strongest
available sense**, and Stirling envelopes do not restore uniqueness.

**Three unrelated things in this collection are called "rigidity."** The
*all-scale polynomial rigidity* of [`surcomplex/analysis`](surcomplex/analysis/)
says a class function on `No[i]` that is Hahn-entire at every scale is a
polynomial. The *scalar rigidity* of `gamma-functions` says compatibility with
the Berarducci–Mantova derivation forces a gauge to vanish. What
`exponential-automorphism-rigidity` proves is neither: it is faithfulness of
`ρ_w`. No shared theorem, no shared lemma, only the shared English word.

## `surcomplex/` — the algebraic closure **No**[i]

Thirteen reports. Seven are one subject — holomorphic function theory, from
twenty-seven manuscripts delivered on a single day — and there the reading
order matters. Six arrived later and stand apart from that spine; they are
listed after it.

### 1. Read [`analysis`](surcomplex/analysis/) first

It is the foundation the other six continue, and its
[`MERGE_NOTES.md`](surcomplex/analysis/MERGE_NOTES.md) is worth reading
before its article. The one thing to carry away: **there is no topological
convergence anywhere in this theory.** Every *set* of surcomplex numbers is
closed and discrete, a convergent set-indexed net is eventually constant, and
every continuous map `[0,1] → No[i]` is constant. So `Σ tⁿ = (1−t)⁻¹` is a
Hahn identity, never a limit of partial sums, and contour integration is
defined coefficientwise along ordinary complex paths.

Nine independent runs at a foundation do not agree the way nine runs at a
theorem would. Of seventeen load-bearing notions in those nine manuscripts,
six are genuinely inequivalent, and a theorem proved under one is false under
another — three inequivalent function classes, and three inequivalent
residues, two of which disagree numerically.

### 2. Read the ring table in [`analytic-geometry`](surcomplex/analytic-geometry/) next

Four coefficient rings run through this material under nearly identical
notation:

| ring | what it requires of a Hahn coefficient family |
|---|---|
| `C{z}((t^Γ))` | each coefficient a convergent germ; **no** common radius |
| `O(D)((t^Γ))` | all coefficients holomorphic on one **fixed** polydisk `D` |
| common-domain germ `Rₙ` | one ordinary neighbourhood serving all, before shrinking |
| `C[[z]]((t^Γ))` | nothing; formal coefficients |

The inclusions are strict, and the witness is explicit:

    F(z) = Σ_{r ≥ 1} t^{rη} / (1 − rz)

whose coefficient at `rη` has a pole at `1/r`, so no ordinary disk carries
the whole family. **A theorem true over one of these rings can be false over
another.** Each report therefore names the ring of every statement and
records that nothing was transported between rings; where a bridge is used it
is one-directional and flagged in the proof that uses it. Reading two reports
side by side without this table is the fastest way to attribute a theorem to
a ring it was never proved over.

### 3. The remaining five, in any order

| directory | subject |
|---|---|
| [`finite-deformations`](surcomplex/finite-deformations/) | positive Hahn perturbations keep the whole finite geometry: division with a support certificate, conservation of multiplicity at the *displaced* zeros, residue duality |
| [`contours-and-stokes`](surcomplex/contours-and-stokes/) | Jordan separation in the standard-part topology, a coefficientwise de Rham complex, Cauchy, winding, and actual contours realizing the residue series |
| [`global-divisors`](surcomplex/global-divisors/) | local-to-global: the sharp *symmetric-support* divisor criterion, Mittag-Leffler, Cousin, and the Picard dichotomy |
| [`polynomial-algebra`](surcomplex/polynomial-algebra/) | finite-degree polynomials, with the ordered-modulus and the Hahn-valuation geometries kept apart and a Rouché theorem in each |
| [`trigonometry`](surcomplex/trigonometry/) | every surcomplex direction has a *finite* surreal angle, so triangle geometry works at arbitrary scale without ever valuing `sin ω` |

Two dependencies are worth knowing. `finite-deformations` defines its residue
by a *series* and says so emphatically; supplying a surcomplex contour that
represents that functional is a separate question, and it is answered in
`contours-and-stokes`. And `analytic-geometry` cites `finite-deformations`
§15.3 for the fact that a determinant-only stability threshold is provably
lossy, rather than restating it.

### 4. Six later arrivals

These six do not belong to the holomorphic-function spine above and do not
need to be read in any order relative to it.

| directory | subject |
|---|---|
| [`differential-equations`](surcomplex/differential-equations/) | the Berarducci–Mantova derivation on `No`, its unique extension to `No[i]`, and which equations have solutions |
| [`rank-one-berkovich`](surcomplex/rank-one-berkovich/) | Tate algebras, Berkovich disks and annuli inside the fixed rank-one field `C((t^R))` |
| [`spectral-theory`](surcomplex/spectral-theory/) | finite matrices: the SVD without compactness, and singular-value scales |
| [`dynamics-and-normal-forms`](surcomplex/dynamics-and-normal-forms/) | linearization thresholds, periods and normal forms at arbitrary valuation rank, plus the quasi-periodic half |
| [`nonabelian-support`](surcomplex/nonabelian-support/) | the matrix Cousin problem and inverse monodromy for near-identity Hahn matrices |
| [`entire-functions-at-arbitrary-rank`](surcomplex/entire-functions-at-arbitrary-rank/) | entire series over one fixed Hahn field: a ring trichotomy and an exact scalar-extension domain |

**`differential-equations`** is a merge of seven manuscripts. Its organizing
identity is exact — the image of the logarithmic derivative on `No[i]` is

    { ∂y/y : y ≠ 0 }  =  No + i·A ,      A := ∂m = ∂O

so `∂y = (a+ib)y` has a nonzero solution exactly when `b` has a **finite**
primitive. Two warnings travel with that. The two printed forms `No + i·∂m` and
`No + i·∂O` are equal *only through a proved lemma*, never as notational
variants. And `A` is a **strict** subclass of `m`: `ω⁻¹` is infinitesimal while
its primitive `log ω` is infinite, so `∂y = i·ω⁻¹·y` has only the zero solution.
Collapsing `∂O` to `O` would turn the criterion into "`b` infinitesimal" and make
that equation solvable — which is exactly what all seven sources refute.

The headline negative consequence: `∂y = iy` needs a finite primitive of `1`, and
those are `ω + c`, all infinite. So `∂²y + y = 0` factors as `(∂−i)(∂+i)y = 0`
and has only `y = 0`. **There is no formal oscillator**, and that is why `sin ω`
is not a Berarducci–Mantova-differential element of `No`.

If you read only one convention from that report, read the one on **phase**.
Three different objects in its sources were all called that, and one source
printed two of them twenty lines apart:

| symbol | object | lives in |
|---|---|---|
| `θ` | the finite angle, the argument of `cis` | `O` — always finite |
| `η` | the infinitesimal residue after removing a constant unit | `m` |
| `B` | the accumulated phase, any primitive of `Im a` | `No` — leaves `O` when its purely infinite part is nonzero |

with `θ = st(θ) + η`, so the first two are related and not synonymous. "The phase
of the solution is `log ω`" is a false sentence; the report prints it beside the
true one.

**`rank-one-berkovich`** is the one report in the collection where **convergence
is real convergence**. Inside `K = C((t^R))` the absolute value `|a| = exp(−v(a))`
is genuine and `K` is spherically complete. That does *not* contradict
[`analysis`](surcomplex/analysis/): its convergence is in the intrinsic valuation
topology of one fixed rank-one field, not the fine topology induced from `No[i]`.
Its case study settles the zero geometry of `Σ t^(n²) Z^n` — the series
[`foundations`](foundations-and-computation/foundations/) exhibited — with the
first correction of the *m*-th normalized root at `t^(m(m+1))`. And at
`Z = t^(−ω)` the exponents `n² − nω` strictly decrease, so the support is not
well ordered and the series is *not* an all-surcomplex entire function: the
obstruction **agrees with** all-scale rigidity rather than refuting it.

**`spectral-theory`** is the linear-algebra chapter the collection lacked, and
the only report here with no derivation, phase or differential equation in it.
Its point is that the finite spectral theorem and the SVD need **real closedness,
not Archimedean completeness** — the proofs exhibit the extremal witnesses, so
Courant–Fischer and Ky Fan hold with extrema *attained* rather than extracted
from a compactness argument.

**`dynamics-and-normal-forms`** is a merge of seven manuscripts, six on germ
and fixed-point dynamics and one on the quasi-periodic half — a cohomological
equation on a real torus whose frequency vector has *surreal* components. The
two halves share machinery and nothing else. **Read its Section 2 before any
theorem in it.** Five **inequivalent** conditions travelled under the single
word *resonance* across those manuscripts and six under *small divisor*, and
two groups of sources used *radius* with **opposite** monotonicity; unifying
the notation without separating the notions would have produced statements
that read correctly and are false. Two traps in particular: lattice resonance
is **not** frequency resonance — the latter is about ordinary complex `ω`,
with divisors graded by Taylor degree and of Hahn valuation zero, the former
about surreal components, with divisors graded by the Fourier index and of
nonzero valuation — and the finitely many visible divisor valuations are
**not** a spectrum in any sense this collection uses.

**`nonabelian-support`** is a merge of two manuscripts, one per part, on
matrices congruent to the identity modulo positive Hahn exponents. Both of its
headline theorems read *"the criterion is that the union of the supports is
well ordered"*, and **they are not the same criterion.** The gluing criterion
is about the supports of the **normalized polar factors**, each transition
matrix factored independently and first, and is false in **both** directions
with the raw transition support in its place; the realizability criterion is
about the **raw** monodromy matrices, where the raw support *is* the invariant.
Its Section 12 exists solely to keep them apart. It also recovers the scalar
Cousin criterion of [`global-divisors`](surcomplex/global-divisors/) at rank
one, so the two are not independent results.

**`entire-functions-at-arbitrary-rank`** is a merge of two manuscripts that
were the same paper twice on the engine and complementary on the payload. Both
payloads are kept: a ring trichotomy — the entire ring is always a GCD domain,
and is a PID, or Bézout, or **GCD but not Bézout**, according to whether the
value group has uncountable cofinality, or an order unit, or neither — and an
exact scalar-extension domain, the same one for *every* nonpolynomial entire
series. It **extends** `rank-one-berkovich`, which lands in the Bézout case
where the third possibility is invisible; and **rank is not the driver**, since
a rank-two group with an order unit is Bézout while a countable-cofinality
group without one is not. Its whole-class rigidity corollary is offered as a
*re-derivation*, not a new theorem: `analysis` already proves all-scale
polynomial rigidity and `foundations` already records the exact boundary.

## `surquaternions/` — where commutativity stops

One report,
[`surquaternions`](surquaternions/surquaternions/), on Hamilton's division
algebra `H_No = No + No i + No j + No k` with central surreal coefficients. It
is filed on its own because **no commutative argument survives the move**:
conjugation, multiplicativity of the modulus, valuation and leading
coefficients, polynomial evaluation, matrix adjoints, exponential laws and
every chain rule all need separate treatment, and every commutative result
quoted from a companion report is reproved over `H`.

It develops three levels and never silently mixes them: finite algebra over an
arbitrary real closed field; set-sized Hahn workspaces `H(R((t^Γ)))`, with a
noncommutative residue algebra and the all-lengths Neumann support lemma via
Higman's finite-word lemma; and the full surreal class, with the
Ehrlich–Kaplan global phase, a global radial exponential, and the
componentwise Berarducci–Mantova derivation.

**Read its Section 2 first.** Three exponentials and four derivative-like
operators in this subject carry overlapping names, and each satisfies a
*different* law on a *different* domain; Section 2 fixes one name and one
symbol per object. Section 2.1 is the one to read before quoting anything
across families: this report's statement that the radial exponential is **not**
an additive-to-multiplicative homomorphism and the physics report's statement
that the **commutative** Ehrlich–Kaplan exponential **is** one are both
correct. The restriction to any single slice is exactly that commutative
exponential, and the law holds there; it fails only across *noncommuting*
arguments, where no common slice exists. A sentence blurring the two would
manufacture a false contradiction across this collection.

## `physics/` — the one report that is not mathematics

One report,
[`surreal-scalars-and-spacetime`](physics/surreal-scalars-and-spacetime/), a
merge of three manuscripts. **Its conclusion is negative, and the sentence it
exists to refuse, in any form, is that surreal numbers resolve the black-hole
singularity.** Surreal and surcomplex scalars make the hierarchy of quantities
near a gravitational singularity exactly representable. They do **not** make
the spacetime regular. The Kretschmann scalar of Schwarzschild is exactly
`K = 48M²/r⁶`; under a formal radial change `r = s^q·w(s)` the pole order is
exactly `6q` with `48M²` unchanged; the proper time from rest at `R` is
`(π/2)·√(R³/2M)`, which for *infinitesimal* `R` is infinitesimal and therefore
still finite, so the infall terminates either way. And `r⁶K = 48m²` has no
field-valued solution at `r = 0` in *any* characteristic-zero field.

What it is for is the representation gain — the surreal/Hahn language records
the power **and** the coefficient of every divergence exactly, keeps competing
scales separate, and detects when an expansion has been used outside its
regime — and the **claim-status firewall**. Every theorem header and every
substantive paragraph carries one of four tags: exact symbolic identity,
checked exactly and never to a tolerance; conditional theorem, with hypotheses
stated in full and **established for no physical model**; assessment, meaning
an argument and not a result; and imported. Read the ledger (its Section 2)
before any single statement from it.

## `foundations-and-computation/` — about the subject rather than inside it

Three reports that take the rest of the collection as their object. Read any
of them independently; none depends on the others.

| directory | subject |
|---|---|
| [`foundations`](foundations-and-computation/foundations/) | in what foundation does this mathematics legally live, and how would a proof assistant encode it |
| [`computer-algebra`](foundations-and-computation/computer-algebra/) | what can actually be computed exactly, and what only denoted or approximated |
| [`computable-surreals`](foundations-and-computation/computable-surreals/) | which surreal numbers admit an algorithm, and in which representation |

Each merges three manuscripts delivered together. In the first two the
difficulty was a collision of near-identical names rather than overlapping
content; in the third it was two different numerical representations of the
same objects.

**`foundations`** compares ZF/ZFC with definable classes, NBG, Kelley–Morse,
Grothendieck universes, constructive set theory, dependent type theory and
univalent foundations, and proves the size obstructions each must respect. Two
things in it are worth knowing before reading anything else in the collection.

First, the *localization theorem*: every **set** of surcomplex numbers already
lies inside one divisible set-sized workspace `K_Γ = C((t^Γ))`. That is why the
analytic reports can work in a fixed workspace without losing generality, and
why a finite zero scheme gains no points in a larger one.

Second, a pair of series over the same field `C((t^Q))` that differ only in the
sign of an exponent and reach opposite conclusions:

    sum t^(-n^2) X^n   is strongly summable at NO nonzero argument
    sum t^(+n^2) z^n   is summable everywhere, and is NONPOLYNOMIAL
                       while coherent at every radius

The second does not refute the all-scale rigidity theorem in
[`surcomplex/analysis`](surcomplex/analysis/), which is about class functions on
the whole `No[i]`, where the proper class of scales supplies the dominating
exponent the proof needs. It shows that theorem does not transfer to a fixed
value group such as `Q`. Do not read the two series as contradicting each other.
[`surcomplex/entire-functions-at-arbitrary-rank`](surcomplex/entire-functions-at-arbitrary-rank/)
explains, through its trichotomy, why the second series works at `Q` and what
would break it.

Three of the five Lean files shipped with this report were compiled for this
repository and `#print axioms` run on every declaration: no `sorryAx` and no
`Classical.choice` anywhere, and the two size-obstruction theorems depend on no
axioms at all. The toolchain used is **not** the one the sources pin, and one
shipped file does not compile as delivered. The report says so in its own
section rather than in a footnote.

**`computer-algebra`** separates finite exact denotation, effective coefficient
access, decidable equality and order, and certified approximation into capability
tiers, then works through exact representations up to transseries and a proposed
Wolfram Language architecture. Its three source manuscripts each shipped an
executable Wolfram package, all three of which are in `code/`, and **the three
are not interchangeable**:

| | coefficients | exponent lattice | complex operations |
|---|---|---|---|
| `RationalHahn` | `Q` only | `Z^d`, `v(t_j) = ω^(j-1)` | none |
| `SurrealCASCore` | `Q(i)` | **`Q^r`** — fractional exponents | conjugate |
| `HahnRational` | `Q(i)` | `Z^rank` | conjugate, Re, Im, modulus |

Two of them are near-anagrams, two export six identical public symbol names with
incompatible signatures, and two order their monomial variables by **opposite**
conventions — which reverses every inequality. A ramified root is representable
in `SurrealCASCore` and not in `HahnRational`. The report never says "the
prototype"; neither should anyone quoting it.

All three check suites reproduce exactly (34/34, 110/110, 88/88 in Wolfram;
69/69 and 323/323 in Python), but `RationalHahn` **cannot be loaded at all as
shipped** — an unclosed bracket stops it parsing, which is why its own record
submits definitions to an evaluator rather than loading the file. One character
repairs it. It ships here as delivered, defect included.

**`computable-surreals`** is the one report whose source manuscripts were never
distributed with it in the first place: its reconciliation ledger cites them by
their original TeX line numbers and `data/provenance-manifest.json` records
their archive identities and file hashes, so every disposition is traceable
against a copy obtained elsewhere. It keeps both numerical representations that
arrived — effective rational left-finite series with finite candidate covers,
and computable bounded-denominator Puiseux series — rather than picking one,
retains complementary proofs of shared statements, and separates mathematical
existence from the existence of a uniform algorithm throughout. Four
verification suites are rerun and pass: 4,967 exact comparisons, 18 named unit
tests, 266 exact checks, and 4,321 exact cross-model checks new to the merge.
**Those four units mean different things and are deliberately not added
together**, and none of them proves an infinite theorem.

## Building

Each article, from its own directory:

```sh
latexmk -pdf -interaction=nonstopmode article.tex && latexmk -c
```

Every one builds standalone — internal bibliography, no external `.bib`, no
graphics — with zero errors and zero undefined references. The catalogue
builds the same way from `manifest.tex`.

## Provenance

These reports were previously part of a larger collection whose subject was
elsewhere; they were moved here with their git history intact, so
`git log --follow` on any file reaches back past the move. That is also why a
catalogue entry may mention a merge, a duplicate sweep or a delivery number:
those describe how a report reached its present form, and the record is kept
rather than rewritten.
