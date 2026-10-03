# Report38: first revisits and exact finite observations

The first-revisit, polynomial-bit-complexity and exact-observation arguments
pass this bounded proof read on their stated domains. No mathematical defect
was found. The unrestricted turmite substrate is universal, but the certified
one-visit portion treated here is decidable and does not supply a new universal
arithmetic bound. No archived Python was imported or executed.

## Identity and read scope

Archive: `docs/incoming/Polynomial_First_Revisit_and_Exact_Pattern_Queries_for_Turmites_Package.zip`,
504,531 bytes, SHA256
`e5abfdbfbbc9c203bdfafb040cba7f8c280af8b031b02103c989aeb97e085277`.
Selected named members were read as data in a private `/tmp` directory; no
generic extraction or repository write was performed. Member paths below are
relative to `Research_Report38/`.

| Member | SHA256 | Read scope |
|---|---|---|
| `README.md` | `ea5315c3daacd04e5fe5306d17e18078e831fac2f10008c9d625f26ba22cfe38` | Complete |
| `evidence/source-packet/boundary-context/proof.md` | `7a855d4af90beb924475a3b9c0e7b06fbc033503c849f9f97bb70cfc8c905761` | Complete original boundary proof |
| `evidence/source-packet/PROOF.md` | `d4fa1ecec1b80d320a36ee464095c38fe671531757cc5dfcb85c3f8b62e30f12` | Complete observation-extension proof |
| `evidence/source-packet/complexity-review.md` | `5c8a72e42ac1d804f6179ba3b8d52033744897c2ae3ecf6de0fb5417aa8c5497` | Complete bit-complexity argument |
| `evidence/source-packet/review.md` | `2b9424773c2f0af9dee87c8e2829e9f351324e33ca3da834c1bfa74ce6785895` | Mathematical/interface assessment through its recorded finding and resolution; historical test claims inherited |
| `evidence/source-packet/boundary-context/source-audit.md` | `ecffab51c5b44fe174774218fd4c29fe1e130e3cb6fefd42d3faf92ad236ff40` | Complete scope and literature record |
| `Research_Report38.tex` | `d81bc30804a381694454142e9939ee2c637f794289151566070078694d4812c7` | Main theorem, lane geometry, complexity, observation calculus, examples and universality sections; no PDF/build audit |
| `evidence/source-packet/one_visit.py` | `6b2bc54678a5a4c18db8eec23e37195a3c526d7f152863a1fb3a1f8d682429f7` | Complete source, text only |
| `evidence/source-packet/observations.py` | `a9f951d4c12df99d0d78bf6eca3fdeee55539eb1bd3938e6e4fd71ae027b5210` | Complete source, text only |

This is not a replay of author or independent test logs, an archive-verifier
security audit, a hostile-object API audit, or a certification of the shipped
PDF. The lower-level `first_hit` explicitly requires an unmodified certified
result from the same inputs; `solve` constructs that pairing itself.

## First-revisit proof and complexity

Time is observed before departure. Up to and including the first repeated
arrival, every preceding departure used a fresh site, so the head agrees with
the walk that reads the initial board without updating it. Equality of
positions, irrespective of heading, defines the first revisit.

On the defect-free periodic tile, the state `(x mod u,y mod v,heading)` has
`S=4uv` possibilities and its transition is a permutation. The successor
heading determines the predecessor site; its tile colour then determines the
inverse turn. Each prospective excursion is therefore a pure projected cycle
of at most `S` affine lanes, even when its lifted spatial drift is nonzero.
All phase pairs must still be tested for intersections.

The rank-two Cramer calculation, rank-one integer interval and rank-zero
earliest-old-index cases exhaust lane intersections. The strict chronological
inequality includes the required minus one. A collision wins a tie with a
defect arrival. Otherwise the encountered defect is fresh, and its one special
departure starts the next excursion. Thus at most `K` defect departures occur,
with at most `(K+1)S` lanes; the history excludes the current arrival at every
restart. Immediate collision after a defect departure is detected next at
local index zero.

The complexity proof controls more than the winning event. Put
`B=R+S+1`, where `R` bounds the initial and defect coordinates. A completed
lane ends fewer than `S` physical moves before its terminal defect; both its
endpoints, and hence all represented historical points, lie in `[-B,B]^2`.
Every relevant finite minimizing lane index is at most `2B`. This includes
prospective/history, defect and same-excursion comparisons, with zero drift
handled separately. Consequently the bound

```
tau <= (K+1)*(S*(2B+1)+1)
```

holds whenever a first revisit exists. The separate bounds on determinants,
Bezout coefficients, interval endpoints and reconstructed indices also control
discarded and infeasible candidates. They give polynomial bit length, rather
than merely a polynomial number of unit-cost arithmetic calls. With an
explicit rule and explicit tile, the coarse `O(N_input^7)` bound for the
pair-call arithmetic is justified. Binary coordinates may make the numerical
first-revisit time exponential; no loop expands that time interval. This
argument does not cover succinctly encoded tiles or arbitrary post-revisit
dynamics.

## Exact observations and their boundary

The lane-relation projection is one interval-congruence atom or empty in
every spatial rank. Generalized CRT handles noncoprime moduli; strict
chronology distinguishes an earlier departure from a simultaneous arrival.
Boolean operations on signed sums of atom indicators preserve values in
`{0,1}`. That invariant is essential: zero signed count implies emptiness
only for the resulting indicator, not for an arbitrary signed function.

Beyond the largest finite endpoint and initial unbounded endpoint, the
indicator is periodic with period the lcm of its unbounded atom steps.
Counting one prefix plus one period therefore decides emptiness globally;
monotone prefix-count bisection gives the exact minimum without enumerating
the period. Distributive Boolean expansion can still be exponential, as the
report explicitly states. There is no polynomial-time claim for arbitrary
observation compilation or minimization.

The colour identity is the initial colour plus the Boolean indicator of an
earlier visit, modulo the palette size. It is valid through the first repeated
arrival, before that site's second departure. Defect overrides are masked
correctly against the periodic background, and a defect never reached by the
head can still affect a stencil. The final drifting tail makes each fixed
head-relative stencil eventually periodic; this is not periodicity of the
whole changing board. The two-cell checkerboard example correctly excludes
time zero and first matches at `2M`; the defect example first revisits at
`2M+2` with a different heading from its earlier occurrence.

## Universality and a concrete arithmetic lead

The primary paper was checked directly: its Theorems 2.1 and 3.1 establish
simulation on periodic backgrounds with finite input perturbations; §5 states
the at-most-two-visits property of its constructions. This supports the
report's contextual upper side. It does not instantiate a literal periodic
colour atlas, ordinary-input arithmetic loader, or iff accepting port for
this repository. See [Maldonado et al., *Nontrivial Turmites are
Turing-universal*](https://arxiv.org/html/1702.05547).

Report38's lower side is sound: a computable reduction whose every run is
globally one-visit and whose acceptance is one of the specified finite
observations would compose with this total algorithm to decide its language.
The theorem therefore does not capture unrestricted universal computations.
Ordinary turmites also do not physically halt. No sharp literal one/two-visit
compiler threshold is newly established.

One concrete component lead is to retain the observation formula as a shared
Boolean DAG after exact lane projection, and compile **membership at a
supplied lane index** without expanding signed indicator products. Its atoms
are affine inequalities and fixed-modulus congruences. The existing
[five-witness congruence component](presburger_congruence_five.md) already
provides canonical truth and falsehood; its note, read here, has SHA256
`ee158f85fc74e1027de08433f4e4d9065c2c7b219670519047116a04aa931fa5`.
Its standalone 21-operation SOS explicitly excludes evaluation of the affine
input, truth-output use and outer composition.

For clarity, an inequality truth bit `b=[L>=0]` has two natural coordinates
`b,s` and residuals

```
b*(b-1)
L - (2*b-1)*s - b + 1.
```

They canonically give `s=L` when `b=1` and `s=-L-1` otherwise.
AND/OR/NOT circuit values can then be defined by quadratic/affine residuals,
with no Boolean expansion and unique gate values. A full paid compiler must
still charge each affine form, atom, gate, truth-output use, square and final
sum. This is an unimplemented occurrence-certificate lead, not a new saving
or bound. It does **not** certify first-hit minimality: the report's global
count/minimum computation needs a separate certificate if that property is
to be represented. Nor does it certify arbitrary supplied lane tables;
cycle, defect ownership and no-earlier-collision checks remain necessary.

The useful next task is a bounded literal DAG compiler for one nontrivial
Report38 clause, with full natural-fiber proof and paid finalizer, compared
against its expanded-atom form. Any arity would depend on that fixed compiled
lane/query description. The universal-operation frontier remains unchanged.
