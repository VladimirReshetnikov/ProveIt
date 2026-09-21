# The surreal and surcomplex reports

Fifteen research packages, in three families. The typeset catalogue is
[`manifest.pdf`](manifest.pdf) (source [`manifest.tex`](manifest.tex)); it
gives a paragraph on what each report claims. This page is the map: which
family a report belongs to, and what to read before what.

Every directory holds `article.pdf`, its LaTeX source, a `README.md`, and in
most cases `code/` with verification programs and `data/` with the recorded
output of running them. A merged report also keeps every source manuscript
verbatim under `sources/`, so the merge can be audited against what went
into it.

These are AI-assisted drafts. None is refereed or machine-checked.

## `surreal/` — the surreal field **No**

Six reports, independent of each other. Read in any order.

| directory | subject |
|---|---|
| [`hahn-evaluation-at-omega`](surreal/hahn-evaluation-at-omega/) | Lipparini's Problem 7.7, answered negatively |
| [`broadcast-sum-of-surreal-sequences`](surreal/broadcast-sum-of-surreal-sequences/) | Lipparini's sign-truncation game, Remark 7.6(3) |
| [`gonshor-product-birthdays`](surreal/gonshor-product-birthdays/) | Gonshor's `b(xy) ≤ b(x) ⊗ b(y)` on ordinal-support normal forms |
| [`gonshor-laurent-birthdays`](surreal/gonshor-laurent-birthdays/) | the same bound on `R((ω⁻¹))` |
| [`canonical-forms-need-not-be-subgraphs`](surreal/canonical-forms-need-not-be-subgraphs/) | Roughan's Figure 3 question, answered negatively |
| [`genetic-gaps-and-primitives`](surreal/genetic-gaps-and-primitives/) | a genetic indicator with derivative zero that is not constant |

The two Gonshor reports prove the same inequality and **neither contains the
other**: the first allows arbitrary ordinal supports but excludes `ω` and
every positive power; the second contains `ω` and its powers but restricts
supports to order type at most `ω` on the integer lattice. On their common
corner `R[[ω⁻¹]]` they agree, and the result is proved twice. They are kept
separate deliberately — a future sweep should not merge them.

## `surcomplex/` — the algebraic closure **No**[i]

Seven reports on one subject, from twenty-seven manuscripts delivered on a
single day. Here the reading order matters.

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

## `foundations-and-computation/` — about the subject rather than inside it

Two reports that take the rest of the collection as their object. Read either
independently; neither depends on the other.

| directory | subject |
|---|---|
| [`foundations`](foundations-and-computation/foundations/) | in what foundation does this mathematics legally live, and how would a proof assistant encode it |
| [`computer-algebra`](foundations-and-computation/computer-algebra/) | what can actually be computed exactly, and what only denoted or approximated |

Each merges three manuscripts delivered together, and in each the difficulty
was a collision of near-identical names rather than overlapping content.

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

Three of the five Lean files shipped with this report were compiled for this
repository and `#print axioms` run on every declaration: no `sorryAx` and no
`Classical.choice` anywhere, and the two size-obstruction theorems depend on no
axioms at all. The toolchain used is **not** the one the sources pin, and one
shipped file does not compile as delivered. The report says so in its own
section rather than in a footnote.

**`computer-algebra`** separates finite exact denotation, effective coefficient
access, decidable equality and order, and certified approximation into capability
tiers, then works through exact representations up to transseries and a proposed
Wolfram Language architecture. Its three source manuscripts each ship an
executable Wolfram package, and **the three are not interchangeable**:

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
