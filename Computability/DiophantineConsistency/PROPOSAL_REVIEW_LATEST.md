# Later arrivals and current size reductions

This continues the [first wave11 review](PROPOSAL_REVIEW_WAVE11.md), with
arrivals eae4f1952b,440dd03ab8,d42be5cd87,43ac596e36,751bc067e2 and
1072d31072. Lean remains
paused. The entries below are ordinary mathematical results and exact
finite artifact checks; they do not assert a completed internal-ZFC
formalization or global simplicity optimum.

## New complete working points

Operations count every live binary addition, subtraction and multiplication,
including squares and fixed scalar products. Named polynomial values add
no unknowns. Domains and whole coefficient tuples remain separate.

| Domain | Unknowns | Operations | Exact degree | Evidence |
|---|---:|---:|---:|---|
| Positive integers | 9 | **433** | 1,628,768 | Saturated compact54 source plus identical norm rewrite |
| Positive integers | 9 | **722** | 1,158,228 | Collected original31 radical evaluator plus identical norm rewrite |
| Positive integers | 9 | **953** | **999,518** | Saturated H1868 radical, D collection and identical norm rewrite |
| Positive integers | 10 | **131** | 1,152 | Four-root radical/residue proposal |
| Positive integers | 11 | **111** | **211** | Adaptive q²Y carrier combined with double center |
| Positive integers | 14 | 73 / 74 / 75 / **76** | 342 / 312 / 293 / **191** | Hilbert Tenth root deletion and ordinate centers |
| Integers | 10 | 471 | 1,245,324 | Round12 short guard; full replay and ordinary guard review |
| Integers | 10 | **475 / 478 / 512** | 1,179,788 / 1,114,252 / 1,080,888 | Short guard combined with compact older shears |
| Integers | 16 | 134 / 135 | 192 / 184 | Separated rational norm and nonnegative guard finalizer |
| Integers | 13 | 185 / 186 / 195 | 1,408 / 1,392 / 1,072 | Guard-first fusion and reanchored positivity guard |
| Integers | 14 | 137 / 148 / 150 / 156 / 163 | 792 / 748 / 696 / 664 / 652 | Root fusion and compact fixed-prime norm evaluators |
| Integers | 15 | 124 / 128 | 352 / 204 | Parity-separated norm;204/128 improves344/131 |
| Integers | 16 | 115 / 119 / 132 | 160 / 112 / 108 | Parity/residue families and prime separation |
| Integers | 17 | 110 | 88 | Root-fusion quotient companion;114-gate checkpoint retained |
| Integers | 18 / 19 / 20 | not optimized in coordinate packets | 32 / 28 / 18 | Signed coordinate/quotient reductions |
| Nonnegative integers | 522 | not optimized | 4 | Synchronized arithmetic;20,225 terms, height83,900,628 |
| Nonnegative integers | 529 / 596 / 895 | not optimized | 4 | Distinct support/height tradeoffs |
| Integers | 1,224 | not optimized | 4 | Actual-row sign certificates;23,590 terms, height83,900,628 |
| Integers | 1,190 | not optimized | 4 | Signed monic projection;26,411 terms, same height |
| Integers | 1,231 / 1,298 / 1,597 | not optimized | 4 | Guarded support/height tradeoffs |

The nine-variable953/999,518 point improves both operations and degree over
the earlier1,073/1,103,950 radical form; the latter's smaller compact54
coefficient tuple remains a storage tradeoff. It trades cost with722/1,158,228. The433-operation form
improves both cost and degree over the440/1,845,940 checkpoint. The original
475/1,379,730 nine-positive form remains a separate degree/cost option.

The explicit norm identity

```
(t²-s(a+b))²-4s²ab = (t²+s(a-b))²-4sat²
```

saves one multiplication while preserving each entire parent polynomial.
It is independently derived in this research and also appears as
polarization in the concurrently arriving round12 proposal. No novelty
claim is made. [norm-tail-sharing](candidates/norm-tail-sharing/README.md)
retains all ten rewrites, complete prefix maps, whole fixed bindings,
normal/optimized checks and corruption controls. Its selected independent
review covers one saturated and one ten-integer instance.

The H1868 [D collection](candidates/saturated-h1868-d/README.md) reduces333
majorant terms to263, saving132 operations before the final norm rewrite.
The ordinary review corrects the manuscripts' population coefficient4210
to4220; the actual delivered threshold is already correct. The earlier
H2082 correction2^20 and new H1868 correction297874 are not interchanged.

The [new Hilbert Tenth transfers](candidates/fixed-root-centers/README.md)
retain the whole compact36 tuple. Their ordinary version proves rational
strong-root integrality by balanced Pell-unit reduction **after** exposing
the early main bound. Scaled ordinate centering then removes large leading
terms. The explicit4/3 counterexample explains the invalid shortcut that
would skip that bound. The fourteen-variable lower-degree equations on
other source tuples remain separate comparisons.

## Reviews and replay scopes

* [Pell-congruence integers](PROPOSAL_REVIEW_PELL_CONGRUENCES_INTEGER.md)
  check early c|f²-1 before deleted quotients, compatible canonical guards,
  all sign cases and monic F elimination. The whole source34 tuple is
  authenticated. Its positive companion is reviewed
  [separately](PROPOSAL_REVIEW_PELL_CONGRUENCES_POSITIVE.md). A bare optimized
  positive driver drops child flags and fails; direct optimized components
  and the unchanged environment-propagated driver pass. This defect is
  retained in the receipts rather than hidden.
* [Radical/residue ten-positive](PROPOSAL_REVIEW_RADICAL_RESIDUE_POSITIVE.md)
  verifies nonvanishing of every signed radical subset, index recovery
  before residue separation, and the genuine noncoprime case. Its
  [integer forms and polynomial-shear integer companions](PROPOSAL_REVIEW_RADICAL_RESIDUE_SHEARS_INTEGER.md)
  have separate scoped normal/optimized replays.
* [Ten-integer shears](PROPOSAL_REVIEW_POLYNOMIAL_SHEARS_NORM10.md) have full
  inverse polynomial translations, exact cancellation degrees and all
  three scoped components replayed in both modes.
  [Adaptive eleven and norm-tail review](PROPOSAL_REVIEW_ADAPTIVE_SHEARS_NORM_TAILS.md)
  independently checks the changed cofactor, positive inverse, finalizer,
  selected exact gate maps and actual immutable arrival bytes.
* [Saturated nine](candidates/saturated-nine/PEER_REVIEW.md) checks index
  folding, compatible finite periods, positivity before root integrality
  and the corrected radical majorant. Its complete release passed all
  eight component/mode stages. The next saturated-certificates release
  passed all five audits normally and optimized; the new H1868 source
  receives an exact transcription, degree and ordinary review in its
  materialized candidate.
* [Saturated-certificate integers](PROPOSAL_REVIEW_SATURATED_CERTIFICATES_INTEGER.md)
  check pre-auxiliary quotient divisibility, rational-root separation from
  the guard alone and a product finalizer valid for every signed input.
  The23/10 polynomial reproduces the earlier shear polynomial after
  renaming and residual reordering; its131-gate DAG is a counted endpoint,
  not another variable/degree improvement. The16/184/135 and16/192/134
  pair remains a real cost/degree tradeoff.

* [Thirteen-integer root fusion](PROPOSAL_REVIEW_ROOT_FUSION13.md) checks
  positivity from the guard before rational-root extraction, signed subset
  noncancellation, source residues and regenerated canonical witnesses.
  All six norm equations and four quotient companions pass the full
  normal/optimized release replay with the complete source34 tuple.
* [Fixed-prime radicals](PROPOSAL_REVIEW_FIXED_PRIME_RADICALS.md) use
  distinct even3-adic valuations to exclude signed cancellation within
  each squareclass, including negative radicands before positivity.
  The [compact evaluators](candidates/fixed-prime-compact-norms/README.md)
  preserve every whole polynomial exactly while saving277 operations for
  five roots and67 for four. Exact free-radicand coefficient identities,
  full prefix/tail substitutions, all six fixed tuples and attained
  degrees pass independent normal/optimized checks. The useful new
  fourteen-integer tradeoffs are652/163,664/156 and748/148.
* [Both parity families](PROPOSAL_REVIEW_PARITY_FAMILIES.md) pass their
  small-integer ordinary reviews and exact scoped replays. The first's
  15/204/128 improves root-fusion15/344/131 and fixed-prime15/214/139;
  its15/352/124 saves four operations at higher degree. The distinct
  second archive gives16/112/119 by a modulus-four root reconstruction.
  The first's16/160/115 remains a lower-operation alternative. The
  second direct-quartic and integer20 components are outside this review;
  the ordinary-only first driver and optimized component scopes are
  reported precisely rather than conflated.
* The [coordinate-family peer review](reviews/coordinate-family-peer.md)
  verifies the complete polynomial row/inverse transformations and exact
  leading forms. Twenty integer variables now reach degree18; this is a
  coordinate reduction with its own complete source binding.
* [Prime separation](PROPOSAL_REVIEW_PRIME_SEPARATION.md) passes both full
  release modes, complete fixed-coefficient reconstruction, all four
  attained degrees and the literal sixteen-variable norm identity.
  Every subset containing an old root has a unique even least3-adic
  order; the fifth guard can have odd order without invalidating that
  argument. The useful16/108/132 point lowers degree relative to parity
  16/112/119 while adding thirteen operations.

The incoming archives remain immutable and retain their original names.
Candidate provenance pins the actual arrival bytes. Scoped reviews are not
silently relabeled as complete-release replays.

## A complete direct alternative

The [direct C222 review](PROPOSAL_REVIEW_DIRECT_C222_ROUND12.md) closes the
ordinary chain from the actual unconditional C222↔ZF-refutation and
ZF↔ZFC-refutation interfaces through Horn flow, beta coding, uniform CRT,
explicit arithmetic graphs and affine gate elimination. This construction
uses no K215, native coefficient tuple or Jones universal equation.

Its original final integer quartic is actually supplied:27,916 variables,758,275
monomials, maximum absolute coefficient320,307,372,009,918. Its natural
companion has16,036 variables. The full52-stage normal/optimized authored
allowlist passes in isolated scratch, authenticating318 files and exactly
regenerating36 literal/coefficient files. The
[full replay receipt](data/round12-full-replay.json) and separate independent
mathematical review preserve their distinct scopes. A proof formalizable
in ZFC is established by the ordinary argument; a new Lean or sealed
object-ZFC derivation has not been emitted.

The newer [shared-direct review](PROPOSAL_REVIEW_SHARED_CERTIFICATES_DIRECT.md)
closes the ordinary shared-CRT construction at3,614 natural variables,
including positivity of every arithmetic call and the factorial-free
binomial range test. The full incoming replay and a separate direct-only
normal/optimized reconstruction pass. No K215 or Jones encoding enters
this route.

The [prime-power CRT lift](candidates/shared-crt-prime-lift/README.md)
removes the private-coordinate bound from the global factorial argument.
For completeness it strengthens each CRT period by exactly the relevant
prime part of the range factorial, then shifts by the stronger product.
This covers the noncoprime case where shifting by the original product
alone fails. The smaller natural polynomials have3,609 and6,180 variables;
all expanded coefficients and residuals are supplied. The first has15,752
monomials and coefficient height127,285,349; the second has17,421 terms
and height1,992. Separate ordinary and exact finite peer reviews pass.

Its [integer companion](candidates/shared-crt-prime-lift/integer/README.md)
appends1,670 guards `x=a²+b²+c(c+1)`. Legendre's three-square theorem
supplies all natural inputs; every unguarded arithmetic wire is forced
natural by its actual monic nonnegative defining equation. The full
integer quartic has8,619 variables,4,619 residuals and39,811 monomials at
the same coefficient height127,285,349. Complete prefix/guard coverage,
all1,939 retained gate definitions and exact collected expansion pass in
normal and optimized Python. The proof remains ordinary ZFC-formalizable
mathematics; no new Lean or sealed object-ZFC derivation is claimed.

The [literal beta-majorant refinement](candidates/shared-crt-beta-majorant/README.md)
sets `H=E+F`. The actual bound circuit retains the beta denominator square
`D²`, giving `H>=D²>=1` unconditionally over naturals. The separate
endpoint row `y=M0+r0+2` then gives `H>=t` before applying the arithmetic
and CRT theorems. Off the endpoint zero set that index inequality can
fail; the checker includes an exact counterexample. The resulting
quartics have3,603 natural variables/15,670 terms/height127,285,252, or
6,179 variables/17,417 terms/height1,992. Both complete expansions,
majorant path, affine restoration and normal/optimized rebuilds pass,
with separate ordinary peer review. The frozen8,619-integer equation
still uses its3,609-variable parent and remains a distinct checkpoint.

The [fixed power bound](candidates/shared-crt-fixed-power-bound/README.md)
chooses `W=n+k` in all55 positive-power calls. The actual forward Pell
construction works at every common bound `W>=n,k`; fresh witnesses
therefore exist at that fixed value. Soundness restores the two deleted
bound slacks by `wn=k,wk=n`. This removes165 semantic coordinates and
gives3,443-natural and5,960-natural quartics, with full ordinary proof,
independent review and normal/optimized exact checks. The affine form
has15,754 monomials and height127,302,193, slightly above the frozen
prime-lift parent in those metrics. No claim to dominate every metric
is made. The retained-wire form has16,894 terms and unchanged height1,992.

## Simultaneous arithmetic and smaller integer conversions

The [synchronized-certificate review](PROPOSAL_REVIEW_SYNCHRONIZED_CERTIFICATES.md)
accepts a complete522-natural-variable quartic with20,225 monomials and
height83,900,628. All27 power requests share one Pell frame,22 index
blocks and10 base moduli. A finite-unit period proves simultaneous
index-witness existence. Pell classification supplies the exponential
bound needed for power uniqueness; its weaker quadratic consequence
alone would be insufficient. Powers are interpreted pointwise before
binomial digits and semantic macro induction, resolving the deferred
radix cycle. The reduced beta source and actual23-squaring majorant
are independently checked. Full normal/optimized replays reproduce22
JSON files and reject three corrupted contraction certificates.

The [batched direct review](reviews/batched-direct-peer.md) separately
accepts667-natural and1,690-integer constructions with a common signed
quotient offset, pooled Pell frame and exact signed monic projection.
All16 direct and6 integer files rebuild byte-identically in both modes;
the integer child was explicitly rerun under optimized Python because
its wrapper omits the flag. This is a different shared-frame architecture.

Our [actual-row guard family](candidates/synchronized-row-guards/README.md)
guards only234 coordinates of each synchronized natural parent.
Every other coordinate is proved nonnegative from its literal rows at
arbitrary integer zeros, before interpreting arithmetic. The complete
quartics have1,224/1,231/1,298/1,597 integer variables and respectively
23,590/14,148/10,628/8,232 monomials. Their heights are83,900,628,
211,184,624,63,909,160 and63,908,265. Actual parent bytes, ordered sign
certificates, all fresh guards and every collected coefficient pass
independent normal/optimized checks. Minimality of234 seeds is proved
only within the explicitly restricted elementary inference class.

The [signed projections](candidates/synchronized-signed-projections/README.md)
further give1,190 integer variables,600 residuals and26,411 terms at
height83,900,628. Seven complete points retain variable/support/height
tradeoffs. Each monic substitution is replayed against every residual,
including sign guards. Reverse restoration uniquely recovers the full
guarded integer parent before the natural sign certificate is used.
No unconstrained coordinate is dropped. Both full normal/optimized
generator and independent-checker runs pass, including14 corruptions;
root separately reviewed and replayed the entire construction.

The [reanchored guard review](PROPOSAL_REVIEW_REANCHORED_GUARD13.md)
improves the thirteen-integer195-operation form from degree1088 to1072
at the same source34 coefficients. It moves a nonzero square scale
inside the lower-degree argument of the joint positivity pair. The
guard's signs and magnitude bound survive with fresh private witnesses.
Both complete scoped replays and the attained leading coefficient pass.

## Newer arrivals still being assessed

The congruence-certificate,608-shared-Pell and twelve-integer interpolation
archives arriving ina6269e4da6 remain under review. Preliminary claims
are not promoted to the table. The earlier direct7617 projection is
queued; its local-source ideas may compose with the newer frame engine.
Further combinations are researched as separate candidates. Both
differently named parity ZIPs remain distinct.
The centered-compression dependency ZIP contains a byte-identical existing
joint-guards archive rather than a new equation. Further shared-CRT bound
and Pell power-certificate reductions are being checked as separate
candidates. Research continues across encodings while Lean remains paused.
