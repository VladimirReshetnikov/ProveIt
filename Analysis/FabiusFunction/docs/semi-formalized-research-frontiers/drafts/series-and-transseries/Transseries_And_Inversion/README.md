# Transseries: the polynomial–logarithmic calculus and its inversions

**Single consolidated volume for the whole `series-and-transseries` group.**
`transseries_and_inversion.tex` and the PDF built from it in the same run.

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
  proposition is a corollary of it and not conversely.  The certificate is now
  machine-checked as `Fabius.exists_eq_in_residual_interval`; unlike the two
  error inequalities, it assumes no pre-existing root or right inverse;
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

The volume was historically assembled from the five source groups listed
above.  Those inputs and the dedicated assembly configuration were retired
after residue review, so `transseries_and_inversion.tex` is now the canonical
edit-in-place source; no runnable package-local assembler survives.  Its PDF
must be rebuilt in exactly three serial `pdflatex` passes after the current
Lean-crosswalk edit.  The retained 703-page PDF is a readable historical
checkpoint, not a claim of current source/PDF parity.  A fresh measured source,
PDF, metadata, page, font, and visual receipt will replace this paragraph after
that rebuild.
