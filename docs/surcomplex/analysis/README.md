# Surcomplex analysis: holomorphic functions on K = No[i]

One article assembled from **nine separately delivered manuscripts**, with the
duplicated mathematics stated once. [`MERGE_NOTES.md`](MERGE_NOTES.md) records
the provenance, the full notation reconciliation, the eleven resolved
conflicts, and — most importantly — the **six load-bearing notions that are not
equivalent across the sources**.

## What this is

All nine archives arrived under the same name, `surcomplex_analysis`, with
`(1)` and `(2)` variants, and all nine are dated 21 September 2026. They are
nine independent attempts at one subject: a theory of holomorphic functions
over `K = No[i]`, the algebraic closure of the surreal numbers, built on
Hahn-supported series.

Nine runs at one *theorem* either agree or they don't. Nine runs at one
*foundation* can come out nine slightly different ways that look alike and are
**not interchangeable**. That is what happened, and it is what made this merge
delicate.

## The six notions that are not equivalent

A theorem proved under one version is false under another, and the sources
themselves supply the counterexamples. The three sharpest:

**Three inequivalent function classes.** A *germ-analytic* function is a
summable power series with arbitrary surcomplex coefficients — no domain, no
growth condition. A *coherent* section of `H(U)` has ordinary holomorphic
coefficient functions on one common ordinary domain. A *lift* `f^#` is the
canonical image of an ordinary holomorphic function. The identity theorem, the
global maximum principle, Liouville, uniqueness of primitives and the open
mapping theorem all hold for coherent sections and **fail** for germs. The
sharp Schwarz and Schwarz–Pick inequalities hold for lifts and **fail** for
coherent sections. Every theorem in the article names its class.

**Three inequivalent residues, two of which disagree numerically.** For
`1/(ζ − ε)` with `ε` infinitesimal, the cluster residue at the ordinary centre
0 is **1**, while the local residue at 0 is **0** — because the actual pole is
at `ε`, not at 0. Both are correct under their own definitions. Writing one
symbol for both produces a false theorem, so the article uses three:
`Res` (formal), `Res^H_a` (cluster, at an ordinary centre), `Res_b` (actual, at
a surcomplex point).

**Three inequivalent Liouville hypotheses.** A single surreal bound on the
finite halo is *vacuous* — every nonzero entire section already satisfies one.
A single ordinary real bound gives an exact characterization, **not**
constancy: `F = tz` is real-bounded by 1 on the whole finite plane and is not
constant. Only the coefficientwise hypothesis yields constancy. The article
states all three as a hierarchy.

The other three concern the Cauchy estimate (a coefficientwise warning that
must not be read as forbidding the stronger modulus estimate), the support
condition, and the boundedness notion; see `MERGE_NOTES.md`.

## Where the nine agreed

On the foundations that matter most: summability is defined identically in all
nine — a set-indexed family is summable iff the union of supports is well
ordered and each exponent occurs in only finitely many members — and all nine
prove the same collapse of topological convergence. Every set in `K` is closed
and discrete, every convergent set-indexed net is eventually constant, and
every continuous map `[0,1] → K` is constant. So `Σ tⁿ = (1−t)⁻¹` is a Hahn
identity, never a limit of partial sums. All nine say so.

## What is not settled

Recorded in the article rather than smoothed over:

- **Two different logarithms**, both called "the" logarithm, differing by
  exactly `2πi` on an explicit set of points. Both are kept, under distinct
  names, with the discrepancy computed.
- A Picard-type theorem is proved for one specified function and explicitly
  declined in general by two of the sources.

These are AI-assisted research notes. None of the nine sources is refereed or
machine-checked, and merging them does not change that.

## Layout

- `article.pdf`, `article.tex` — the merged article.
- `MERGE_NOTES.md` — provenance, notation, the seventeen notions, the eleven
  resolutions.
- `sources/` — all nine manuscripts verbatim, `NN-slug.tex`, with their
  READMEs. Nothing discarded.
- `code/` — the nine verification programs, `NN-slug.py`. All nine were run and
  all nine pass; each states that finite symbolic checks do not establish the
  general theory.
- `data/` — the recorded outputs of those runs.

## Running the verifiers

```sh
for f in code/*.py; do python "$f"; done
```
