# Series and transseries

Everything in this group is now one document.

The live Lean inventory after the current integration is 961 modules and
11,974 public declarations; 944/11,806 is the preceding historical checkpoint.
The flatness module now includes both its vector-valued API and the scalar
submodule, absorption, and inverse-power-scale interfaces (4 definitions and
22 theorems). The differential-block module contains 12 theorems.

The new Bell derivation-tower and ordinary-Bell normalization results have
exact source counterparts. The Touchard definitions and coefficient identities
are also formalized. The wider Wright-omega, differential-closure, harmonic,
Cayley, derangement, Lambert-correction, core-inversion, remainder-transport,
and staircase statements still have the qualifications recorded in the source;
the least-term-index lemmas are supporting results, not a complete
optimal-truncation theorem.

> [`Transseries_And_Inversion/`](Transseries_And_Inversion/) —
> *Transseries: the polynomial–logarithmic calculus, series reversal at
> infinity, and the inversion of rapidly growing functions*. The current
> source is accompanied by a retained historical A4 PDF from the consolidation
> checkpoint; the source now postdates that artifact, and no render parity is
> claimed. 4 September 2026.

## What was merged

Forty-two independently written articles, filed between 1 and 3 September
2026, in five groups. Thirty of them had already been consolidated once, into
two volumes; those two and the remaining twelve articles are now a single
volume, and all five source directories have been deleted. Git history is the
archive, and the volume's provenance appendix lists every source with the part
that absorbed it.

| Group | Articles | Absorbed as |
| --- | --- | --- |
| `transseries-tutorials/` | 4 | Part I, Orientation |
| `polynomial-logarithmic-transseries/` | 6 | the calculus parts |
| `special-function-inversion/` | 24 | the inversion parts |
| `lambert-inverse-transseries/` | 3 | reversing `x + W(x)` |
| `sequence-transseries/` | 5 | the Bell and Fubini chapters |

## The comparison this group had left open

The previous version of this README recorded, as explicitly unmade, the
comparison between the polynomial–logarithmic calculus and the inversion
calculi that the special-function and Lambert-inverse articles each extract.
The merge makes it, and the volume's concordance chapter states it pair by
pair.

The result is **less overlap than a title-level comparison suggests**. Of six
apparent overlaps, one is a genuine duplicate (the exponential partial Bell
polynomials, the same definition in two notations), one is a strengthening in
the inversion apparatus's favour (a two-sided residual bracket with a
root-existence certificate against a one-sided mean-value bound), one item has
no counterpart at all (the ordinary Bell family), and three are different
theorems about the same subject — most notably the two results both called
Lagrange–Bürmann, which are the near-identity *operator* form and the classical
*coefficient* form, neither implying the other without a genuine argument.

Shared vocabulary turned out to be a weak signal, and an intermediate stage of
this merge was misled by it; the volume records the correction rather than
quietly fixing it.

What the inversion apparatus genuinely adds over the calculus is the
exponential–power model and its axiomatized dominant core, the monomial
α-reduction, perturbed inversion around an exactly invertible core, the
two-sided backward-error certificate, and — with no analogue anywhere in the
calculus — the theory of inverting a **sequence**: three distinct inverse
objects, the staircase theorem, and the separation condition under which an
asymptotic inverse determines an integer one. The calculus is a theory of
functions on a scale; that last group is about the passage to a sequence.

## Residue audit

Deletion followed an audit of the twelve newly merged sources against the
assembled volume, and of the two consolidated volumes by direct containment.
The two volumes are absorbed verbatim: 32 of 32,874 substantive lines of the
calculus and 4 of 14,980 of the inversion volume differ, and every difference
is a transformation made deliberately at assembly — the sectioning shift, with
its 49 consequent "this section" → "this chapter" rewrites, and three retitled
chapters.

For the twelve articles, matching every named result against the volume's 768
titled results left six with no close counterpart; all six were checked
individually and are covered under other names, are alternative derivations of
a theorem the volume does state (a Lipschitz–Poisson route and a
Bose–Einstein-kernel route to the same pole expansion), or were demoted on
purpose. The audit's first pass left ten such results, and the four that were
genuinely missing — the saddle-localization lemma, the certified pole-tail
bounds, the linear pole budget, and the weighted Fubini polynomials — were
absorbed before deleting. Numeric residue is sequence values, numerical-table
mantissas and worked-example integers, none of them a result.
