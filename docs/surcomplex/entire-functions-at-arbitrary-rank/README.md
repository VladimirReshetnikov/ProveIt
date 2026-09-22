# Cofinality, Factorization and Scalar Extension for Entire Hahn Functions at Arbitrary Rank

**A merged research report, 44 pages.** Everything in this directory other
than `article.tex`, `article.pdf` and this README is preserved source
material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled 44-page report
README.md     this guide
sources/      the two source manuscripts, unmodified, with their READMEs and audits
code/         the two source verification programs, unmodified
data/         the two recorded verification records and the source build report
```

## What the report is

Two independently written manuscripts, both dated 21 September 2026, each
written against its own pinned snapshot of this repository, studied the same
object: ordinary power series `sum a_n Z^n` over a **fixed** Hahn field
`K_Gamma = C((t^Gamma))` with `Gamma` a set-sized divisible ordered abelian
group of arbitrary valuation rank, where *entire* means strongly
Hahn-summable at every point of that one field. Both explicitly disclaim all
of `No[i]`. This report is their **union**, not a selection.

They were the same paper twice on the engine and complementary on the
payload. Both proved the identical exact coefficient criterion, the same
cofinality dichotomy, the same support-controlled preparation theorem, the
same arbitrary-rank root counts, the same genus-zero canonical product, the
same factorization by zeros, and the same sharp change-of-workspace criterion
by the same witness. Publishing both would have printed one criterion, one
preparation theorem, one product theorem and one extension theorem twice
under two titles. Here each is printed **once**, and the two payloads — a
ring-theoretic trichotomy and a scalar-extension package — are both kept in
full.

## The two headline classifications

Write `cf(Gamma)` for the cofinality of the value group as an ordered set,
and call `delta > 0` an **order unit** when its positive integer multiples
are cofinal in `Gamma`.

**1. The trichotomy (Theorem 1.5).** The entire ring `E_Gamma` is always a
GCD domain with units exactly `K_Gamma^times`, and exactly one of:

| Value group | Entire series | Ideal structure |
|---|---|---|
| `cf(Gamma) > aleph_0` | only polynomials | PID |
| an order unit exists | nonpolynomial series exist | Bézout, non-Noetherian, full Hermite interpolation |
| `cf(Gamma) = aleph_0`, no order unit | nonpolynomial series exist | GCD but **not** Bézout |

The third case is the sharpest single result in either source. With
`gamma_(n+1)` exceeding every finite multiple of `gamma_n` and cofinal, set
`rho_n = t^(-gamma_n)` and `sigma_n = t^(-gamma_n) + t^(gamma_(n+1))`. The
two canonical products with these roots have **disjoint simple zero sets and
gcd 1, yet generate a proper ideal**: there are no entire `A, B` with
`Af + Bg = 1`. The obstruction is an exact valuation computation,
`v(g(rho_n)) = gamma_(n+1) + (2-n)gamma_n + sum_{j<n} gamma_j`, against a
growth barrier that every entire function obeys. The positive half is proved
too, by a real-valued coarsening that kills the convex subgroup below the
order unit and reduces to a complete rank-one field.

Section 4 supplies what makes the middle case **sharp** rather than merely
sufficient: a nonconstant valuation-restricted series is invertible in
`T_Gamma` if and only if its least coefficient gap is a positive order unit.
Necessity is proved by coarsening, not by observing that one geometric series
fails.

**2. The scalar-extension package (Theorem 1.6).** For any ordered-group
extension `Gamma` inside `Delta`, *every* nonpolynomial entire series over
`K_Gamma` has the **same** exact strong evaluation domain in `K_Delta`: the
valuation ring `D_(Gamma,Delta)` of `v_Delta` coarsened by the convex hull of
`Gamma`, whose residue field is `C((t^H))` rather than `C`. Entireness
survives exactly for cofinal extensions. No new zeros appear anywhere in the
surviving domain, even for an infinite divisor. On a noncofinal extension
there is no alternative entire series agreeing with the old one even on all
ordinary complex constants. And the boundary is intrinsic: `Gamma`, the
coefficient slopes `v(a_n)/n`, and the negated zero valuations `-v(r)`
generate the same convex subgroup.

## Three things to read before using a theorem from here

**The two extension statements are one statement (Remarks 1.7 and 10.6).**
One source states the noncofinal case negatively — the series is simply *not
entire* over `K_Delta`, and `E_Delta ∩ K_Gamma[[Z]] = K_Gamma[Z]` — while the
other proves the same series stays strongly summable on exactly
`D_(Gamma,Delta)` and keeps all of its zeros there. Read side by side these
look like disagreement about whether the function survives. They are the
coarse and the exact form of one fact: "not entire over `K_Delta`" means
precisely that the domain is a *proper* subring, and the extension theorem
computes which subring. The report says so explicitly in both places, and
Section 12.3 exhibits the concrete pair.

**One name for the order invariant (Remark 1.4).** The sources named the same
condition twice: *order unit* and *cofinal-cyclic element*. The report keeps
**order unit** and records the synonym once, together with the equivalences
(greatest positive Archimedean class; `m*delta -> +infinity`; `t^delta`
topologically nilpotent). This is **not** the same invariant as `cf(Gamma)`:
an order unit forces countable cofinality but not conversely, and that gap is
exactly the third case of the trichotomy. Nor is it the cofinality of an
ordinal, a diagram, or the image of a displacement map, for which other
reports in this collection use the same word.

**Ring discipline (Convention 1.2).** Every statement names its coefficient
ring. The chain here is
`K_Gamma[Z] ⊆ E_Gamma ⊆ T_Gamma ⊆ A_Gamma ⊆ K_Gamma[[Z]]`, all with **Hahn
series over C** as coefficients. Nothing here is a theorem about
`O(U)((t^Gamma))` or `C{z}((t^Gamma))`, whose coefficients are ordinary
holomorphic functions on a common complex domain. The convention is the one
stated by name in `surcomplex/analytic-geometry`, and it is invoked here so
that no reader transports a result across that boundary.

## Relation to the rest of the collection

- **`surcomplex/rank-one-berkovich` — this report extends it.** That report
  fixes `K = C((t^R))`, where the valuation is a genuine real-valued absolute
  value; it is the one place in the collection where convergence is real
  convergence, and it already contains rank-one zero-free rigidity and a
  canonical product. Neither source manuscript claims to originate either
  point. Rank one is `cf(R) = aleph_0` with `1` an order unit, so it lands in
  the **Bézout** case: the pathology of the third case is invisible there.
  Its `prop:rankobstruction` — `Q + Q*omega` admits no order-preserving
  injective additive map to `R` — is exactly why Lemma 9.1 here builds a
  *coarsening* with a possibly nonzero kernel and not an embedding. Its ring
  chain `K[Z] ⊂ T ⊂ P ⊂ A ⊂ F ⊂ E^-` resembles ours and is **not** the same
  chain; the shared symbols do not denote the same rings.
- **`surcomplex/analysis` and `foundations-and-computation/foundations` —
  published beside them.** The whole-class rigidity corollary (an ordinary
  power series strongly summable at every point of `No[i]` is a polynomial)
  is presented as a **re-derivation** from the extension theorem, not a new
  theorem: `analysis` already proves all-scale polynomial rigidity, and
  `foundations` already records the exact boundary with the sign-flipped pair
  over `C((t^Q))`, noting that `sum t^(+n^2) z^n` is summable everywhere and
  nonpolynomial. That example is Remark 3.2 here, and the trichotomy explains
  why it works at `Q` and what would break it. The reduction consumes the
  foundations localization principle — every *set* of surcomplex numbers lies
  in one divisible set-sized workspace — which is cited, not reproved.
- **`surcomplex/global-divisors` — a different ring.** Its divisor,
  interpolation and Picard obstructions live in
  `O(U)((t^Gamma))`. Nothing here restates or contradicts them.

## Explicit examples

`Gamma_infinity = ⊕_{j>=0} Q*omega^j` has countable cofinality and no order
unit, so it is a case-(iii) group. In it the Bézout counterexample has roots
`omega^(omega^n)` and `omega^(omega^n) + omega^(-omega^(n+1))`, and the
canonical product `P(Z) = prod_{j>=0} (1 - t^(e_j) Z)` over the whole basis
differs from the counterexample function by the single factor
`(1 - omega^(-1) Z)`; its zeros are the simple positive surreals
`omega^(omega^j)`. By contrast `Q^d` lexicographic and `Q e_1 + Q e_2` have
order units and are Bézout even at higher rank, while
`Gamma_(omega_1) = ⊕_{alpha<omega_1} Q*omega^alpha` has uncountable
cofinality and admits only polynomials — **rank is not the driver**. Section
12.2 adds the rank-two hidden-tail pair `A` and `B`, with identical
coefficient valuations and different monomial evaluation domains, and Section
12.6 tabulates four groups against cofinality, order units, nonpolynomial
entire series and nonconstant restricted units.

## Status and scope

These are proposed original contributions with full mathematical proofs, not
a claimed solution of any named published conjecture. Both source manuscripts
state that priority is **not** certified and that their literature checks were
targeted, not exhaustive; searches returning nothing were not treated as
evidence of absence. Neither was independently refereed; neither was
machine-checked, and **no Lean verification is claimed**. Classical rank-one
factorization, Newton polygons, canonical products, the Hahn–Neumann support
lemmas, algebraic closedness of Hahn fields, and the rank-two distinction
between positive valuation and topological nilpotence are all credited as
imported or established, not claimed. Section 14.3 preserves every limitation
recorded by either source, including: `Gamma` must be divisible and algebraic
closedness is used essentially; all supports are sets; the extension theorem
keeps `C` fixed and uses full Hahn fields only; the hidden-tail table covers
monomial arguments only; the uniform-domain statement is **false** in several
variables; and strong summability, intrinsic valuation convergence and the
fine surreal topology are deliberately never identified. No repository files
under `sources/`, `code/` or `data/` have been modified.

## The finite checks prove no infinite theorem

Two exact-arithmetic suites are preserved, one reporting **831** passing
checks and one reporting **664**, both standard-library Python with
`fractions.Fraction` and no floating point. They verify finite formulas,
finite preparation recursions, finite Newton counts, inverse jets and the
paired-root valuation formula in finitely many coordinates. They prove none
of the infinite support, cofinality, factorization, unit-necessity or
nonexistence theorems. In particular the **finite truncations of the
counterexample pair are coprime polynomials and do satisfy polynomial Bézout
identities**, so no finite computation can witness the main negative result.
Appendix C states this in full.

One usage note: the 831-check script takes a **required** `--output` path and
exits nonzero without one. That is deliberate — it prevents a re-run from
overwriting the delivered record — and is not a broken suite. Run correctly
it reproduces 831 of 831.

## Build

A normal TeX Live or MiKTeX installation with the packages named in
`article.tex` and `latexmk` is sufficient. The bibliography is embedded: no
BibTeX file, external graphics, shell escape or repository checkout is needed.

```sh
latexmk -pdf -interaction=nonstopmode article.tex
```

The delivered build is clean: 44 pages, 0 errors, 0 undefined references or
citations, 0 package warnings, 0 overfull or underfull boxes, 66 numbered
statements (18 theorems, 9 lemmas, 4 propositions, 16 corollaries, 4
definitions, 1 convention, 3 examples, 4 questions, 7 remarks).
