# Transseries: the polynomial–logarithmic calculus and its inversions

**Single consolidated volume for the whole `series-and-transseries` group.**
The current `transseries_and_inversion.tex` is accompanied by a retained
historical PDF from the consolidation build. Subsequent editorial corrections
and Lean crosswalks exist only in the source; no render parity is claimed.

## Status

Complete. All five source groups are merged, and all five source
directories were residue-audited and deleted on 4 September 2026.

| Source group | Lines | Absorbed as |
| --- | --- | --- |
| `transseries-tutorials/` (4 articles) | 26,099 | Part I, Orientation |
| `polynomial-logarithmic-transseries/` (1 volume) | 36,033 | Parts II–IX, the calculus |
| `special-function-inversion/` (1 volume) | 16,771 | Parts X–XIV |
| `lambert-inverse-transseries/` (3 articles) | 5,209 | Part XI, `x + W(x)` |
| `sequence-transseries/` (5 articles) | 9,743 | Part XIV, Bell and Fubini |

The provenance appendix lists all forty-two sources with the part that
absorbed each; the repair appendix lists every correction made.

## How the two apparatuses relate

The `series-and-transseries` README recorded, as an explicitly open question,
whether the polynomial–logarithmic calculus and the inversion calculi of the
special-function articles coincide. The concordance chapter answers it, pair
by pair, and the answer is **less overlap than a title-level comparison
suggests**.

An earlier stage of this merge, working from title matching alone, recorded
that the calculus "already contains" Lagrange–Bürmann at infinity and at a
finite point, residual-to-error transfer, both Bell families,
affine-logarithmic reversion and the pure Lambert block, and concluded the
inversion apparatus was largely redundant. Reading the statements shows that
overstated it. The accurate tally, of six apparent overlaps:

* **one genuine duplicate** — the exponential partial Bell polynomials are the
  same definition in two notations (proved in the concordance);
* **one strengthening in the inversion apparatus's favour** — the calculus has
  the one-sided mean-value bound, while the inversion apparatus has the
  two-sided bracket *and* the root-existence certificate, so the calculus's
  proposition is a corollary of it and not conversely;
* **one item with no counterpart** — the calculus defines only the exponential
  Bell family; the ordinary family is new;
* **three pairs that are different theorems about the same subject** —
  Lagrange–Bürmann in near-identity *operator* form against classical
  *coefficient* form; reversion of `X + aL` by Lambert polynomials against the
  closed-form pure Lambert block; leading-order slope transport against a
  bound with an explicit second-order error.

Shared vocabulary is a weak signal: two results both called
"Lagrange–Bürmann" turned out to be different theorems, and a mechanical
concordance reports them as the same. Only reading the statements settles it.

What the inversion apparatus genuinely adds over the calculus is the
exponential–power model and its axiomatized dominant core, the monomial
α-reduction, perturbed inversion around an exactly invertible core, the
ordinary Bell family, the two-sided backward-error certificate, and — with no
analogue anywhere in the calculus — the theory of inverting a **sequence**:
three distinct inverse objects, the staircase theorem, and the separation
condition. The calculus is a theory of functions on a scale; that last group
is about the passage from a function to a sequence.

## Lean crosswalk

The current integrated inventory is 960 modules and 11,966 public declarations;
944/11,806 is a historical checkpoint. `TransseriesFlat` now has 4 definitions
and 22 theorems, preserving the general vector-valued API together with the
scalar submodule, absorption, and power-scale interfaces. The integer block
interfaces and the incoming inverse-power derivative lemmas together make
`TransseriesDifferentialBlock` a 12-theorem module.

The source records status claim by claim. Exact counterparts now cover the
sequence-indexed asymptotic-scale/Poincaré definitions and uniqueness,
flatness and the corrected invisible-function proposition, Dickson and Neumann
(with `OrderDual` matching the manuscript's well-based orientation), the
displayed power–log ratio limits and chosen decreasing
sequence scales, the unit-series Bell coefficient formulas, and the quadratic
Catalan identity. The full unordered power–log scale lemma, the all-integer
Laurent block-antiderivative lemma, and the complete quadratic-core lemma are
Partial at the boundaries stated in the source. No status promotion should be
inferred for the surrounding transseries constructions.

The incoming `BellLeibnizTower` and `OrdinaryPartialBell` modules supply the
abstract Faà di Bruno formula and the ordinary/exponential normalization
bridge. `TouchardEulerOperator` supplies the Touchard definitions and
coefficient identities. The backward-error, transfer, and Lambert-certificate
claims depend on assembling their named existence and comparison theorems.
The broader Wright-omega, differential-closure, harmonic-increment, Cayley,
derangement, Lambert-correction and bracket, core-inversion,
remainder-transport, and staircase claims remain Partial where their source
clauses exceed the exposed APIs. `LeastTermIndex` supplies neighboring
ratio and unimodality lemmas; it does not prove the full optimal-truncation
claim.

## Structure

Part I orients: what a transseries is, why a scale is needed, why divergence is not failure, and the algebra of monomials — replacing four parallel expository introductions.

Parts II–IX are the calculus: the polynomial–logarithmic scale; arithmetic
and differential calculus; composition; series reversal at infinity; Wright
omega, the Lambert polynomials and Lambert `W`; from formal transseries to
analytic asymptotics; algorithms, certificates and diagnostics; extensions.

The remaining parts apply it: the apparatus for inverting a rapidly growing
function; four combinatorial sequences (rooted trees A000081, the double
factorial, the partition numbers A000041, the swing factorial A056040); four
special functions (Γ and Barnes `G`, the hyperfactorial `K`, the subfactorial,
a real-argument Fibonacci function); the reversal of `x + W(x)` in depth; the Bell numbers by a Lambert saddle and the Fubini numbers by an exact pole lattice; and a synthesis.

## Artifact status

The volume was assembled by a script from its component sources. The resulting
`.tex` is now the canonical source, its assembler has been retired, and edits
belong in that file. The retained A4 PDF documents the earlier
consolidation checkpoint and its successful build gates. The current source
contains later editorial and source-only Lean-crosswalk changes and has not
been rerendered, so the PDF is historical evidence rather than a current
render.
