# Transseries: the polynomial–logarithmic calculus and its inversions

**Single consolidated volume for the whole `series-and-transseries` group.**
The live source is `transseries_and_inversion.tex`. Its current 704-page PDF
establishes source parity; the retained incoming 702-page receipt below remains
historical pre-merge provenance.

## Status

Editorial consolidation is complete. All five source groups are merged, and all
five source directories were residue-audited and deleted on 4 September 2026.
The final merged source received three uninterrupted passes. The resulting PDF
passed the A4, rotation, PDF-version, encryption, and embedded/subset-font
checks, but it retains 114 overfull boxes and 11 duplicate Hyperref targets for
a later layout-repair pass. Its exact current receipt is in the [authoritative
receipt register](../../MANIFEST.md#current-post-merge-publication-receipts).

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

The current source adds a scoped Lean crosswalk rather than a title-based one.
It identifies exact counterparts for the abstract asymptotic-scale and
Poincaré-expansion core, flatness and invisible functions, the relevant
Hahn-series foundations, polynomial--logarithmic height estimates, Wright omega
apart from real analyticity, differential-block integration, staircase
inversion, and residual/error transport. Each note records its boundary; the
crosswalk does not promote the volume's remaining human proofs or frontier
claims wholesale.

What the inversion apparatus genuinely adds over the calculus is the
exponential–power model and its axiomatized dominant core, the monomial
α-reduction, perturbed inversion around an exactly invertible core, the
ordinary Bell family, the two-sided backward-error certificate, and — with no
analogue anywhere in the calculus — the theory of inverting a **sequence**:
three distinct inverse objects, the staircase theorem, and the separation
condition. The calculus is a theory of functions on a scale; that last group
is about the passage from a function to a sequence.

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

## Build

The volume is assembled by a script from its sources rather than edited in
place; the assembled `.tex` carries a header saying so. The current rendered
source checkpoint is 55,015 lines / 2,732,554 bytes / SHA-256
`545d4b5ead18831e37a4df0ab7fb6b74a40e1e598144dc7057e8c62aaaa46799`,
with 16 parts, 58 chapters, and 3,111 distinct labels. Its two-file
root-plus-notation closure is 55,299 lines / 2,744,389 bytes / aggregate
SHA-256 `499a045ab45fdea7849c888bc8903db0866a2d4ca27eca3db6f62a9db282af30`.
The incoming 702-page, 7,172,512-byte A4 PDF, SHA-256
`7cbc430332c78a6f2dcd06513c771e15685d87d3ef3a867f55c2687a8702d067`,
is a structurally validated historical pre-merge checkpoint. The current
three-pass render and its disclosed layout warnings are recorded in the
authoritative receipt register linked above.
