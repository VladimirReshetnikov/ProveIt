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
| Positive integers | 9 | 405 / 413 | 1,191,570 / 1,316,546 | Tight main folding and unshifted carrier; original31 / smaller compact54 tuples |
| Positive integers | 9 | **722** | 1,158,228 | Collected original31 radical evaluator plus identical norm rewrite |
| Positive integers | 9 | 953 / 1,056 | 999,518 / 997,810 | Collected radical / position-zero complete radical; cost-degree tradeoff |
| Positive integers | 10 | **86** | 466 | Complete q-cube normalization; cost/degree tradeoff with the canonical92/283 page |
| Positive integers | 10 | 89 / 94 | 288 / 262 | Uncentered b transport; complete89-operation comparison page, exact shared-carrier direct94 |
| Positive integers | 10 | 91 / 92 / 96 / 97 | 283 / 278 / 258 / 254 | Existing b transport and exact shared direct carrier; canonical page retained |
| Positive integers | 10 | **92** | **283** | Coprime saturated Pell product; complete canonical page and indexed constants |
| Positive integers | 10 | 93 | 278 | Sharp saturated center; lower-degree tradeoff |
| Positive integers | 10 | 97 / 98 | 258 / 254 | Direct positive X, shared carrier and upper/sharp saturated centers |
| Positive integers | 10 | 97 | 368 | Existing-square transport weight; one-operation saving, higher degree |
| Positive integers | 10 | 102 | 344 | Existing-square transport and direct positive X; operation/degree tradeoff |
| Positive integers | 10 | 98 | 360 | Positive index weight, zero-offset base; preserved predecessor page |
| Positive integers | 10 | 103 | 332 | Positive index weight and direct positive X; degree tradeoff |
| Positive integers | 10 | 98 | 368 | Zero-offset scaled base, shared muY and expanded transport |
| Positive integers | 10 | 103 | 340 | Direct positive X, shared carrier and expanded transport |
| Positive integers | 11 | **111** | **211** | Adaptive q²Y carrier combined with double center |
| Positive integers | 12 | **96** | **70** | Free positive J and an identical polarized norm tail |
| Positive integers | 13 | **88** | **51** | Free positive J; previous90/51 page retained |
| Positive integers | 14 | 73 / 74 / 75 / **76** | 342 / 312 / 293 / **191** | Hilbert Tenth root deletion and ordinate centers |
| Integers | 10 | 471 | 1,245,324 | Round12 short guard; full replay and ordinary guard review |
| Integers | 10 | **475 / 478 / 512** | 1,179,788 / 1,114,252 / 1,080,888 | Short guard combined with compact older shears |
| Integers | 16 | 134 / 135 | 192 / 184 | Separated rational norm and nonnegative guard finalizer |
| Integers | 12 | 145 / 141 | 1,200 / 1,456 | Scalar intersective carrier, main folding and four-root prime separation |
| Integers | 13 | 135 | 536 | Trace before signs, main-root folding and quadratic projection |
| Integers | 14 | 117 | 312 | Signed main-root recovery, quadratic projection and reduced guard |
| Integers | 15 | 124 / 128 | 352 / 204 | Parity-separated norm;204/128 improves344/131 |
| Integers | 16 | 115 / 118 / 119 / 132 | 160 / 124 / 112 / 108 | Parity/residue families and prime separation |
| Integers | 17 | 110 | 88 | Root-fusion quotient companion;114-gate checkpoint retained |
| Integers | 18 / 19 / 20 | not optimized in coordinate packets | 32 / 28 / 18 | Signed coordinate/quotient reductions |
| Nonnegative integers | **329** | not optimized | **4** | Unified factorial/CRT binomial, derived Cantor;253 rows,12,210 terms,height86,844,780 |
| Nonnegative integers | 399 | not optimized | 4 | Projected source, summed factorial radix and rational SOS contraction;8,286 terms |
| Nonnegative integers | 402 / 403 / 453 / 667 | not optimized | 4 | Complete term/height alternatives;6,882 /8,229 /5,059 /3,632 terms |
| Integers | **359** | not optimized | **4** | Shared cap;222 rows,6,058 terms,height128,446; complete ordinary source and four root replays |
| Integers | **364** | not optimized | **4** | Unique five-sum extension;227 rows,4,574 terms,height128,446; complete quartic and four root replays |
| Integers | 433 | not optimized | 4 | Lower-term helper alternative;287 rows,4,606 terms,height128,446 |
| Integers | 436 | not optimized | 4 | Preserved joint redundant-sign parent;288 rows,4,624 terms,height128,446 |
| Integers | 439 | not optimized | 4 | F-only intermediate;289 rows,4,638 terms,height128,446 |
| Integers | 442 | not optimized | 4 | Preserved unified-binomial parent;290 rows,4,652 terms,height128,446 |
| Integers | 496 | not optimized | 4 | Preserved paired-guard quadratic-first checkpoint;307 rows,5,924 terms,height5,061,227 |
| Integers | 498 | not optimized | 4 | Complete paired guards,support16;309 rows,6,615 terms,height3,904,259 |
| Integers | 501 / 502 | not optimized | 4 | Lower-height paired guards;5,615 /6,111 terms,heights620,468 /411,053 |
| Integers | 517 | not optimized | 4 | Preserved Round14 derived parent;310 rows,6,774 terms,height3,904,267 |
| Integers | 519 | not optimized | 4 | Round14 lower-height alternative; 321 rows, 6,253 terms, height 411,060 |
| Integers | 554 | not optimized | 4 | Ten output squares, 55 guards; 362 rows, 6,927 terms, height 2,445,790,974,704; earlier source pipeline |
| Integers | 557 | not optimized | 4 | Ten output squares, 56 guards, CSE/default projection; 6,937 terms, height 2,445,790,974,704 |
| Integers | 577 / 576 | not optimized | 4 | Existing-square 63-guard CSE projections; 5,754 / 5,818 terms, heights 964,213 / 45,769,613 |
| Integers | 787 / 657 / 599 / 584 | not optimized | 4 | Existing-square 63-guard lower-height CSE projections; heights 4,750 / 737,653 / 737,653 / 938,261 |
| Integers | 575 | not optimized | 4 | Squared-output 64-guard CSE/default projection; 7,225 terms, height 2,445,790,974,704 |
| Integers | 580 / 579 | not optimized | 4 | Squared-output 64-guard CSE projections; 5,768 / 5,832 terms, heights 964,213 / 45,769,613 |
| Integers | 790 / 660 / 602 / 587 | not optimized | 4 | Squared-output 64-guard CSE low-height projections; heights 4,750 / 737,653 / 737,653 / 938,261 |
| Integers | 591 | not optimized | 4 | Common-radius72-guard CSE/default projection;9,657 terms, height2,445,790,974,704 |
| Integers | 596 / 595 | not optimized | 4 | Common-radius72-guard CSE projections;8,328 /8,232 terms, heights964,213 /45,769,613 |
| Integers | 822 / 684 / 618 / 603 | not optimized | 4 | Common-radius72-guard CSE low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 594 | not optimized | 4 | Squared-radius72-guard raw/default projection;9,588 terms, height2,445,790,974,704 |
| Integers | 598 / 597 | not optimized | 4 | Squared-radius72-guard raw projections;8,564 /8,504 terms, heights964,213 /45,769,495 |
| Integers | 824 / 683 / 619 / 605 | not optimized | 4 | Squared-radius72-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 595 | not optimized | 4 | Shifted-t72-guard raw/default projection;9,586 terms, height2,445,790,974,704 |
| Integers | 600 / 599 | not optimized | 4 | Shifted-t72-guard raw projections;8,770 /8,696 terms, heights964,213 /45,769,499 |
| Integers | 828 / 683 / 621 / 607 | not optimized | 4 | Shifted-t72-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 598 | not optimized | 4 | Power-output73-guard raw/default projection;9,600 terms, height2,445,790,974,704 |
| Integers | 603 / 602 | not optimized | 4 | Power-output73-guard raw projections;8,794 /8,710 terms, heights964,213 /45,769,499 |
| Integers | 831 / 686 / 624 / 610 | not optimized | 4 | Power-output73-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 601 | not optimized | 4 | Encoded-index74-guard raw/default projection;9,661 terms, height2,445,790,974,704 |
| Integers | 606 / 605 | not optimized | 4 | Encoded-index74-guard raw projections;8,808 /8,724 terms, heights964,213 /45,769,499 |
| Integers | 834 / 689 / 627 / 613 | not optimized | 4 | Encoded-index74-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 604 | not optimized | 4 | Output-sign75-guard raw/default-affine projection;9,676 terms, height2,445,790,974,704 |
| Integers | 609 / 608 | not optimized | 4 | Output-sign75-guard raw projections;8,823 /8,739 terms, heights964,213 /45,769,499 |
| Integers | 837 / 692 / 630 / 616 | not optimized | 4 | Output-sign75-guard raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 607 / 608 / 610 | not optimized | 4 | Factorial-bound76-guard projections;10,042 /8,706 /8,611 terms, height2,445,790,974,704 |
| Integers | 612 / 611 | not optimized | 4 | Factorial-bound raw projections;8,849 /8,753 terms, heights964,213 /45,769,499 |
| Integers | 840 / 695 / 633 / 619 | not optimized | 4 | Factorial-bound raw low-height projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 610 / 611 / 613 | not optimized | 4 | Paired77-guard projections;10,053 /8,717 /8,622 terms, height2,445,790,974,704 |
| Integers | 639 | not optimized | 4 | Paired77-guard lower-height projection;5,605 terms, height63,905,891 |
| Integers | 843 / 698 / 636 / 622 | not optimized | 4 | Paired77-guard raw projections;heights4,750 /737,653 /737,653 /938,261 |
| Integers | 642 | not optimized | 4 | Comparison-base lift, lower-height projection;5,565 terms, height63,905,891 |
| Integers | 1,493 / 846 | not optimized | 4 | Retained-wire78-guard equations;4,981 /3,813 terms, heights427 /4,750 |
| Integers | 701 / 637 / 623 | not optimized | 4 | Retained-wire78-guard projections;5,575 /8,925 /8,889 terms, heights737,653 /737,653 /938,261 |
| Integers | 613 / 614 / 616 | not optimized | 4 | Signed comparison-base lift and private sign orbits;10,013 /8,677 /8,582 terms, height2,445,790,974,704 |
| Integers | 613 | not optimized | 4 | Raw/default-affine projection;9,661 terms, height2,445,790,974,704 |
| Integers | 1,190 / 1,224 | not optimized | 4 | Preserved synchronized checkpoints, now dominated by917 |

The canonical [equation.pdf](equation.pdf) and standalone [TeX](equation.tex)
now print the complete ten-positive92/283 equation, including every fixed
constant. The separate89/288 comparison page and all earlier pages remain
preserved; see the [current page proof](candidates/one-page-saturated10/README.md)
and [comparison review](reviews/one-page-uncentered89-root-peer.md).

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

The [608-shared-Pell review](PROPOSAL_REVIEW_SHARED_PELL_608.md) is complete.
Its608-natural/1,685-integer equations are dominated by current working
points, but its self-bounding factorial is reusable: with `rho=f*n²`,
the exact ceiling of `(rho+1)^n/binom(rho+n,n)` equals f if and only if
f=n!. The ceiling rows exclude f=0 without assuming the intended value.
This removes one power call per factorial. Both full normal/optimized
replays and the independent ordinary/finite review pass. The complete
[synchronized sibling](candidates/synchronized-factorial-radius/README.md)
now reaches502/509/573/850 natural variables and passes root review.
Its composition with the newer407-source radix is underway.

The congruence-certificate and twelve-integer interpolation archives
arriving ina6269e4da6 now pass the ordinary and scoped release reviews
described below. The earlier direct7617 projection is
queued; its local-source ideas may compose with the newer frame engine.
Further combinations are researched as separate candidates. Both
differently named parity ZIPs remain distinct.
The centered-compression dependency ZIP contains a byte-identical existing
joint-guards archive rather than a new equation. Further shared-CRT bound
and Pell power-certificate reductions are being checked as separate
candidates. Research continues across encodings while Lean remains paused.


## Intersective interpolation and congruence composition

The [twelve-integer review](PROPOSAL_REVIEW_TWELVE_INTERPOLATION.md) accepts
12/248/4832 and12/223/16000, plus the trace13/190/1072 companion. The
new all-residue Pell interpolation fixes its strong pair before choosing
the intersective class; a squared-modulus period and a valuation bound
justify CRT compatibility. Zero scale is excluded before guard recovery,
and the generalized even strong multiplier is proved separately. All138
arrival members,137 manifest entries,93 inherited files and all six source34
ports are authenticated. Full normal/optimized release replays and root's
independent local algebra/arithmetic review pass. No internal-ZFC or Lean
endpoint is newly asserted.

The [congruence review](reviews/congruence-certificates-peer.md) accepts
a free positive J, keeping the possible gcd factor three until the power
and fixed-Mersenne arguments exclude it. It gives13-positive88/51 and
12-positive98/70. The [polarized norm](candidates/free-j-polarized-positive/README.md)
then lowers the latter to96 operations by an exact identity of complete
polynomials. The same incoming review accepts CRT/valuation integer
forms14/148/414,15/130/218 and16/118/124. The15-variable point is dominated
by the retained128/204 parity form; the others add useful tradeoffs.
All ten fixed payloads match their earlier whole tuples byte for byte;
normal/optimized circuit and norm replays pass. These modest positive
circuit improvements did not change the then-current13-positive90/51 PDF.

The ten-positive124-operation degree816 candidate from8380e70262 now
[passes ordinary and full replay review](reviews/ten-positive-scaled-norm-peer.md).
The [complete shared-product sibling](candidates/ten-positive-scaled-norm-shared/README.md)
saves one more operation, reaching123/816 by an exact identity. Its complete
[one-page rendering](candidates/one-page-scaled10/README.md) now passes the
independent typed-tile/native/controller rebinding and printed-formula checks
and became the preceding canonical display. The earlier13-positive90/51 page
retains its lower-degree/fewer-operation tradeoff.

The [122-operation sibling](candidates/ten-positive-scaled-norm-reuse/README.md)
then deletes `q-1` by reusing the earlier `beta*J`, with a complete ordered
gate remap and a universal polynomial identity. Independent normal/-O
checks preserve all ten unknowns, four complete ports and degree816.
That123-operation page remained valid and was retained for this minor
evaluator change; it is now preserved as the preceding degree816 display.

The [quadratic projection](candidates/ten-positive-quadratic-projection/README.md)
now reduces the ten-positive equation to106 operations and exact degree408.
The omitted main Pell ordinate is recovered from the strong/auxiliary
equations by an all-index folding argument. A strict bound on the entire
divisible projection product excludes mixed-prime branches. Complete
positive witness maps, independent ordinary reviews and all literal
normal/-O circuit/norm/leading-form checks pass. A new full page is now
checked for this significant degree and operation reduction. Its exact
[symmetric-tail sibling](candidates/ten-positive-quadratic-projection-shared/README.md)
saves a further multiplication, reaching105/408 with the same whole
polynomial and positive domain. The proposed new page uses this105-gate
form in that one significant update.


## Position zero, fixed-prime interpolation, and the new direct source

The [position-zero review](reviews/constructive-nine-peer.md) proves that
weight zero is valid in the actual H10 positive ratio interface and fully
recalibrates the population threshold after shifting source weights/targets.
The [identical norm-tail sibling](candidates/position-zero-norm-sharing/README.md)
then gives9-positive419/1472168,427/1626248 and1056/997810. Original31 and
compact54 remain different storage choices; no individual port is mixed.

The [valuation twelve-integer review](PROPOSAL_REVIEW_VALUATION_INTEGER12.md)
now accepts215/2400 and209/2912. A short intersective quintic has an odd
remainder coefficient1mod3; every nonempty changed-sign radical subset
is separated by a unique least3-adic order. This works before positivity,
including imaginary/odd-valued guards. The old full-I-before-residue
interpolation order remains intact. These dominate the earlier12-integer
239/4832 and215/16000 complete shared-norm points. Their new pointwise
circuit optimizations are underway and are not yet counted.

The [407/888 direct review](PROPOSAL_REVIEW_QUARTICS407888.md) passes its
ordinary proof, both full replays and the independent no-import checks.
Its projected eight-column source, one-sided flow-degree bootstrap,
low-digit radix reuse and fused divisibility reduce the natural quartic
to407 variables. Complete sign proofs and signed restoration give888
integers, or917 with much lower coefficient height. The independently
reviewed [502-natural factorial-radius sibling](candidates/synchronized-factorial-radius/README.md)
is retained; composing that radius with the new radix is now underway.
The3776/3671 and shared-Pell1873 arrivals remain queued as separate
coefficient/support tradeoffs; no unreviewed point is counted here.


The [valuation shared-norm packet](candidates/valuation-shared-norms/README.md)
now freezes12-integer208/2400 and202/2912. Seven exact cut identities and
an every-node proof preserve the entire polynomials. A separate graded-lex
calculation over all six formal ports certifies the actual child leading
terms and their nonzero beta-only specialization. Both full candidate
modes and root's independent review pass.

The [projected factorial-radius family](candidates/projected-factorial-radius/README.md)
now reaches399 naturals/317 rows/8286 terms/height83843274, with complete
402/403/453-variable alternatives. The summed radix bounds both factorial
binomials even when the proposed t! output is initially zero. The paired
factorial inequality supplies the strict remaining low-digit bound before
the product formula is used. All six literal quartics, raw exports and
rational SOS restorations pass normal/optimized checks and root review.
A new integer guard/projection family is being checked separately; its
unsealed counts are not yet table entries. Lean remains paused.


## Maintained one-page display

The [canonical PDF](equation.pdf) and [TeX](equation.tex) now use the
checked10-positive102-operation degree388 equation. The complete fixed
recipe is verbatim from the preserved105/408 page, including the436-character
seed, corrected initializer and943 typed tiles. The direct-J, shifted-strong
and shorter-transport proofs provide full positive witness maps; the
independent printed-front peer binds every102 gates over free coefficients.
Whole coefficient regeneration and renderer/peer modes pass, and the
one-page9-point layout was visually inspected. See the
[new page packet](candidates/one-page-shifted10/README.md) and
[root page review](reviews/shifted10-page-peer.md).
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) binds the exact displayed
hashes and earlier pages. This combined update saves three operations
and lowers degree by20 without changing the number of unknowns or any
printed constant. No global minimum or completed Lean/internal-ZFC
theorem is implied; formalization remains paused.


The [projected-radius integer companions](candidates/projected-radius-integers/README.md)
now freeze862/863/865-variable quartics at height2445790974704 and a
891-variable lower-height point at63905891. Fresh161-seed/506-derived
actual-row sign proofs precede arithmetic interpretation; reverse signed
restoration recovers every guard before natural semantics. All four complete
coefficient tables, both checker/build modes and root's ordinary review pass.
The prior888/917 and1190 checkpoints remain preserved. Further semantic
sign relaxations and lower-height retention are under separate research;
no unmaterialized count is promoted.


The [identical integer14 simplification](candidates/constructive-integer14-shared/README.md)
reduces147 to145 live operations at unchanged degree568. Two complete
`(1+x)-1=x` substitutions preserve the entire polynomial and all six
fixed coefficients. Root reviewed the literal checker, all node maps,
normal/optimized replays and all30 sealed files. The lower-degree
148/414 and lower-cost137/792 alternatives remain useful tradeoffs.
The then-current10-positive105/408 PDF and TeX are unchanged by this minor
integer-domain simplification; Lean remains paused.


The [mixed retained-wire family](candidates/projected-radius-mixed-retained/README.md)
now gives1,580/933/788/724/710 unrestricted integer variables, all at
exact degree4. It keeps all original raw rows and coefficients, proves
A and D nonnegative from four original-row bounds, and copies107 guard
triples into the literal reviewed994 equation, with six fresh Legendre
witnesses for its two remaining guards. The full592-wire map is over
integers. All five collected quartics and complete signed inverses pass
independent and deterministic checks in both Python modes. Heights remain
427/4,750/737,653/737,653/938,261; each matched159-guard sibling loses
156 coordinates,52 rows and780 terms. The smaller706-variable, larger-height
family remains a separate tradeoff. The canonical PDF/TeX and Lean are unchanged.


The [signed main-root reduction](candidates/constructive-integer14-quadratic/README.md)
now reaches14 unrestricted integer variables,121 operations and exact
degree312. Absolute-value Pell folding recovers the missing main norm
before the signed rank bootstrap; a whole-product absolute height bound
resolves the quadratic projection for both signs of H. Explicit integer
n maps preserve zero existence in both directions. The complete proof,
all six original coefficients, universal formula binding, literal35-term
norm, exact leading form and normal/optimized replays pass independent
and root review. This improves both cost and degree over14-integer
137/792,145/568 and148/414, which remain preserved checkpoints. It has
more variables and operations than the then-current10-positive105/408 page,
so that complete PDF/TeX remains the canonical display. Lean is paused.


The [contracted mixed-bound family](candidates/projected-radius-mixed-bounds/README.md)
now reaches988/729/703/701/700 unrestricted integer variables at degree4.
All585 original body rows are unchanged. Restoring592 raw wires over
integers licenses the four actual t,n,A,D row bounds;107 copied guard
triples plus six fresh A/D witnesses give the literal reviewed994 zero.
Every projection restores the entire988 parent first. Independent and
full deterministic normal/optimized checks pass all1177 row identities,
complete coefficients/inverses and15 corruption controls. The700-variable
polynomial has10,437 terms and height2,445,790,974,704;729 retains lower
height63,905,891. Each matched994/735/709/707/706 checkpoint loses six
variables, two rows and28 terms. The710-variable retained-wire option
has much smaller height938,261. Canonical PDF/TeX and Lean are unchanged.


Two [identical prefix rewrites](candidates/constructive-integer14-quadratic-shared/README.md)
reduce the new14-integer degree312 equation from121 to119 operations.
Reusing q² and factoring ell(ell+1)k²=(ell*k)(ell*k+k) preserve the entire
polynomial over every commutative ring. Complete148-to146 node coverage,
all removed private definitions, every named register, the full35-term
norm and all six payloads pass independent root review and both complete
checker/rebuild modes. All33 packet seals pass. The signed ordinary proof
and exact nonzero leading coefficient transfer unchanged. This is a minor
saving within the new signed degree312 route; the canonical10-positive
105/408 PDF/TeX remains the separate lower-variable/operation display.
Lean remains paused.


The [thirteen-integer quadratic trace equation](candidates/integer13-quadratic-trace/README.md)
now uses135 operations at exact degree536, down from184/1072. Normalized
trace gives both CRT congruences before signs, the unscaled guard gives
four-root separation, and signed Pell folding restores the main norm.
The whole-product height proof resolves its quadratic projection, then
explicit unrestricted n maps restore the frozen trace endpoint in both
directions. Root reviewed the entire ordinary proof and independent
literal checker; all four normal/optimized checker/rebuild commands pass,
including the full495-term norm, centered425-term degree calculation,
authentic six ports and all138 original archive members. This improves
both current13-integer cost and degree. At that checkpoint, the10-positive105/408 page remained
a separate lower-variable/operation display. Lean is paused.


The [five exact original-row sign consequences](research/guard-seed-consequences/README.md)
remove two factorial-output guards, the moduli-product and CRT quotient
guards, and one endpoint quotient guard before any arithmetic semantics.
The CRT numerator uses its independently proved defining sums, avoiding
a circular quotient dependency. The [complete102-guard family](candidates/projected-radius-mixed-signs/README.md)
now gives973/714/688/686/685 integer variables, all degree4. A literal
102-triple transfer plus15 new Legendre witnesses restores the full988
parent; all integer projections are reversed first. Root reviewed both
ordinary proofs and independent checkers. Full normal/optimized checks
and rebuilds pass every original-row identity, the975-step sign ledger,
all coefficients and inverses. Each matched988/729/703/701/700 parent loses
15 variables, five rows and73 collected terms at unchanged height. The
smaller-coefficient retained710 family and canonical PDF/TeX are preserved;
Lean remains paused.


The [scalar-carrier twelve-integer equations](candidates/scalar-carrier12/README.md)
now use145 operations/degree1200 and141/1456, improving208/2400 and202/2912
with the same twelve unrestricted variables and all six original constants.
A scalar intersective quintic enforces H|K and excludes zero strong scale;
prime-order separation leaves four roots, and signed folding recovers the
missing main norm before its whole-product projection. The completeness
proof keeps one strong witness fixed while selecting the translated
intersective residue. Direct nonodd step-down is proved from the auxiliary
index polynomial. Full independent ordinary review, separate all-register
ring binding, all495 norm coefficients, exact every-gate leading induction,
whole payloads/parent inventory and final normal/optimized checks pass.
Both degrees are halved; cost falls by63 and61 operations. Canonical
10-positive105/408 PDF/TeX remains the lower-variable/operation tradeoff;
Lean stays paused.


The [nine-positive folded-saturation equations](research/nine-folded-saturation/README.md)
now reach414 operations/degree1,355,142 on the full original31 tuple and
422/1,497,238 on compact54-sharp. Saturating the strong norm with the
first Pell radicand allows a two-root equation; coprimality recovers both
squares, then main-Pell folding recovers C=psi_A(B1). Positivity is proved
before extraction, and finite matrix periods construct positive i,j,n.
Both directions retain the exact source/binomial boundary and whole fixed
tuples. Root read the full ordinary proof/checker and verified every
retained source node, every local algebraic cut, centered identity and
actual-coefficient homogeneous witness in both Python modes; both complete
rebuilds pass and all packet seals are checked. Both cost and degree improve
the matched419/427 parents. Lower-degree higher-cost alternatives remain
separate, and canonical10-positive105/408 PDF/TeX is unchanged. Lean is paused.


Two [exact private sign orbits](research/guard-sign-orbits/README.md)
now replace the U and bootstrap-witness guards. Complete raw/contracted
row identities negate U and its sixteen quotient partners together, or
reflect Zminus1 with its two private wires. The independent A>=2 row
bound excludes Z=0 before reflection; U=0 uses the identity branch.
All100 remaining guard values and all643 semantic-prefix coordinates
stay fixed. The [whole100-guard family](candidates/projected-radius-mixed-orbits/README.md)
has967/708/682/680/679 integer variables at degree4. Normalize private
values first, then six fresh witnesses give the literal973 equation;
reverse all signed projections before that step. Root reviewed the full
proofs/checkers and all normal/optimized checks/rebuilds pass. The679
polynomial has397 rows and10,335 terms at unchanged height2,445,790,974,704.
Each matched973/714/688/686/685 checkpoint loses six variables and two
rows. The retained-wire low-height family and canonical PDF/TeX remain
separate tradeoffs. Lean stays paused.

## Tightened nine-positive folding accepted

The [tightened packet](research/nine-folded-saturation-tight/README.md)
now gives409 operations / degree1,191,572 on the whole original31 tuple
and417 /1,316,548 on the separate compact54-sharp tuple. It improves the
frozen414/422-operation equations in both operation count and degree.
The strong ordinate omits J, the auxiliary quotient uses positive j
without a shift, the carrier is Jn+Q, and the first norm shares its
majorant. A new strict-gap proof forces positive margin before root
extraction; two finite matrix periods and a strict carrier bound construct
all three changed positive witnesses. No tuple or domain is weakened.
The [root review](reviews/nine-folded-tight-root-peer.md) records the full
ordinary proof audit, exact degree argument, all four normal/optimized
checks and rebuilds, and closed artifact seals. This nine-variable result
is a separate tradeoff from the maintained ten-positive one-page equation.
Lean remains paused; no new internal-ZFC endpoint is claimed.

## Direct positive J in the ten-variable equation accepted

The [free-J ten-positive equation](candidates/ten-positive-free-j/README.md)
saves two operations, reaching103 at the same exact degree408 and ten
positive unknowns. The enlarged positive J domain is sound: odd main
index recovery gives p=R before q parity, then odd q would force even J
and even R. Coprimality is used only after this contradiction recovers
even q. The J=1 case constructs fresh positive source61 witnesses and
uses its actual unrestricted-positive-J soundness statement. The whole
original tuple and separately calibrated BFS tuple remain distinguished.
The [root review](reviews/ten-positive-free-j-root-peer.md) and
[independent ordinary review](reviews/ten-positive-free-j-ordinary-peer.md)
record the proof and full literal affine-map/degree checks. All four
normal/optimized checks and deterministic rebuilds passed. This minor
two-operation saving does not trigger a new canonical PDF/TeX rendering;
its complete105-operation page remains available pending a substantial
improvement. Lean remains paused.

## Raw100-guard low-height quartics accepted

The [retained-wire100-guard packet](candidates/retained-radius-mixed-orbits/README.md)
gives complete integer quartics in1559/912/767/703/689 unknowns, at
coefficient heights427/4750/737653/737653/938261. Each saves21 unknowns
and seven quadratic rows over its corresponding frozen107-guard raw
parent, without increasing height. All original raw coefficients remain.
An exact zero-set bijection restores592 triangular monic affine wires
and copies all100 guard triples to the actual frozen967 equation before
using its sign theorem; no fresh witness or sign premise is needed for
the bridge. Each signed projection first restores the whole raw parent.
The [root review](reviews/retained-orbits-root-peer.md) records all1277
row identities, complete coefficient collections, four successful
normal/optimized checks/rebuilds and closed seals. The contracted679
quartic remains a different coefficient-height tradeoff. No new Lean
endpoint is claimed and formalization remains paused.

## Smaller signed fourteen-variable guard accepted

The [guard-reduced equation](candidates/constructive-integer14-guard-reduced/README.md)
has14 unrestricted integer unknowns,117 operations and exact degree312.
It removes the explicit v-square factor from the guard. Its new proof
excludes v=0 by rationalizing the remaining two roots and deriving an
impossible CRT divisibility, before using any weak-scale estimate. Both
integer witness maps regenerate only the four private guard coordinates;
the entire degree256 norm and six fixed coefficients are unchanged.
The full output difference has degree at most304, so the complete
nonzero degree312 leading component survives. The
[root review](reviews/integer14-guard-root-peer.md) records all node/guard/
norm identities, four successful normal/optimized checks and rebuilds,
and closed seals. The [initial research note](reviews/signed14-guard-research.md)
also records why two tempting smaller positivity gadgets fail. Lean and
the canonical ten-positive page remain unchanged.

## Ten-positive102/388 accepted

The [shifted strong equation](candidates/ten-positive-shifted-strong/README.md)
now reaches102 operations and exact degree388 in ten positive unknowns.
It uses I=(i+q²)c² and the shorter transport L=HI+b. The shift preserves
the unconditional lower bound and square-ordinate divisibility; a new
rational-rho bound licenses the smaller transport before parity recovery.
Canonical completeness keeps the strong ordinate and constructs a fresh
positive final n, including zero transport quotient. The complete norm
has a nonzero selected coefficient2^28*beta^224 in degree388. The
[root review](reviews/shifted-strong10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-shifted-strong-ordinary-peer.md)
record the full proof, exact gate/degree/whole-tuple checks, four passing
normal/optimized replays and closed seals. A new complete one-page display
is being prepared for the combined gain over105/408; its predecessor
will be preserved. Lean remains paused.

## Canonical page updated to102/388

The maintained [equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) at that checkpoint printed the complete ten-positive102-operation,
exact-degree388 equation, including every fixed constant, on one Letter
page. This batches the direct-J, shifted-strong and shorter-transport
improvements into one update over the preserved105/408 page: three fewer
operations and degree20 lower. The complete436-character seed,62-character
alphabet,943 tiles and closed arithmetic coefficient recipe are unchanged.
The [new page packet](candidates/one-page-shifted10/README.md),
[independent root page review](reviews/shifted10-page-peer.md) and
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) bind the displayed bytes.
Both independent peer modes, renderer replays and full coefficient
reconstruction modes pass; the page was visually reviewed. The previous
[105/408 PDF](candidates/one-page-quadratic10/equation.pdf) and its TeX
remain preserved. Lean formalization remains paused.

## Twenty-one pointwise guard consequences accepted

The [main-root/modulus proof](research/main-root-and-modulus-signs/README.md)
recovers15 main-root signs and six power-modulus signs from the unchanged
raw equations with79 retained guards. Its independent semantic-prefix
proof precedes a strict A>W^W bound, signed-index recovery and negative-root
residue contradiction. Only then does a positive-base power call establish
f0>0 and the final modulus sign. All15 actual exponents are proved positive.
The [root review](reviews/main-root-signs-root-peer.md) and
[independent peer](reviews/main-root-modulus-signs-peer.md) verify the
complete original-row, constructor and21-call ledger; all six root
normal/optimized checks, rebuilds and peer runs pass. At the same body
tuple,79 existing triples and63 fresh Legendre witnesses reach the literal
frozen967 equation. Complete new quartics and signed projections are being
materialized separately; no unverified projected count is added here.
Lean and the current canonical PDF/TeX remain unchanged.

## Fixed root weight lowers ten-positive degree to368

The [weighted-root equation](candidates/ten-positive-weighted-roots/README.md)
has ten positive unknowns,102 operations and exact degree368. It replaces
the full-mu strong shift by I=i*c² and weights only the first root by3.
All signed cancellations are excluded before root extraction: two pairs
would imply mu|8, the third would equate an integer to -1/Delta, and a
zero triple would imply mu|2025, then mu|25 despite mu>=1025. Main folding
then gives the strict bound needed for weighted transport. Canonical
completeness uses the explicit positive shifts i_new=i_old+q² and
n_new=n_old+2*tau. The [root review](reviews/weighted10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-weighted-roots-ordinary-peer.md)
record the full proof and exact circuit/degree/whole-tuple checks. All four
normal/optimized checks and rebuilds pass; the unique leading component
has a positive selected coefficient2^28*beta^184. The prior102/388 packet
is preserved; a complete new page is under review. Lean remains paused.

## Complete79-guard compact quartics accepted

The [materialized compact family](candidates/projected-radius-main-root-signs/README.md)
gives full integer quartics in904/645/619/617/616 variables. The smallest
has376 quadratic rows,10,028 collected terms and coefficient height
2,445,790,974,704; the645-variable point has5,580 terms and height63,905,891.
Every profile saves63 unknowns and21 rows over its matching100-guard
parent at unchanged height. Complete signed inverses first restore all79
guards, then592 raw affine wires. The ordered21-sign theorem supplies
63 fresh witnesses at unchanged body values into the literal967 equation.
The [root review](reviews/main-root-quartics-root-peer.md) records full
coefficient collections, every100 copied/fresh guard-row identity, all
four passing normal/optimized checker/rebuild replays and closed seals.
These are checked whole equations, not estimates from deleting guards.
Lean and the ten-positive display remain separate and unchanged.

## Retained-coefficient79-guard quartics accepted

The [new raw family](candidates/retained-radius-main-root-signs/README.md)
keeps all original coefficients and gives1496/849/704/640/626 integer
variables, with exact degree4 and heights427/4750/737653/737653/938261.
The smallest has386 rows and8,904 collected terms. Each profile saves
63 variables and21 rows at unchanged height against its100-guard parent.
The [root review](reviews/main-root-raw-quartics-root-peer.md) records
the complete1256-row integer bijection into904, all592 affine inverses,
and the composed79-copied/63-fresh-witness transfer into literal967.
All100 target guard rows and every full collected polynomial are checked.
All four root normal/optimized checker/rebuild replays and closed seals
pass. The616-variable compact quartic is a separate height tradeoff;
no new Lean or native calibration endpoint is claimed.

## Comparison-base positivity guard removed existentially

The [comparison-base proof](research/comparison-base-sign/README.md) permits
negative B and then lifts it to a positive comparison base while preserving
all78 other guard values. Its complete1177-row audit accounts for62 private
coordinates,141 unit gates and every46 affected nongate constraints. The
signed-index and21-sign proofs precede the lift; q4 positivity is supplied
at the new tuple, not asserted at the old tuple. Three fresh Legendre
witnesses reach the literal904 source. The [root review](reviews/comparison-base-sign-root-peer.md)
and [independent peer](reviews/comparison-base-sign-peer.md) record full
normal/optimized author and peer replays, all passing. New compact/raw
quartics are being materialized separately; this theorem alone supplies no
new projected coefficient count. Lean remains paused.

## Positive short projector reaches101 operations at degree368

The [short-projector equation](candidates/ten-positive-short-projection/README.md)
uses ten positive unknowns and101 live operations at exact degree368.
Kpos=X(3c-2X)+2 is positive after main folding and obeys
Kpos=H*X*c-2*Kquad. Only2 is cancelled modulo odd H; P is retained in
the whole-product argument. Every old positive zero maps to a new one
by the strictly positive shift n_new=n_old+3*(Kquad/H)-X*c. The
[root review](reviews/short10-root-peer.md) and [independent ordinary peer](reviews/ten-positive-short-projection-ordinary-peer.md)
check the full unbounded proof. All four root normal/optimized checker
and rebuild replays, complete53-entry seals and full coefficient binding
pass. The entire polynomial change has degree at most360, preserving the
degree368 leading component. A complete one-page specification is being
reviewed for the next canonical PDF/TeX update. Lean remains paused.

## Canonical complete page updated to101/368

[equation.pdf](equation.pdf) and committed standalone [equation.tex](equation.tex)
now print ten positive unknowns,101 operations and exact degree368. This
batches the fixed root weight and positive short projector: one operation
and20 degrees below the preceding canonical102/388 page, with the entire
constant recipe unchanged. The [complete new page](candidates/one-page-short10/README.md)
includes all436 seed characters,62-symbol alphabet and943 tiles. The
[independent root page review](reviews/short10-page-peer.md) binds all101
live gates universally, verifies all four full ports, and records passing
normal/optimized page peers, renderer replays, author reconstructions and
27 closed seals. The full rendered page was visually checked. All prior
pages remain preserved; [CURRENT_EQUATION.json](CURRENT_EQUATION.json)
binds the exact canonical PDF, TeX and polynomial. Lean remains paused.

## Complete78-guard compact quartics accepted

The [new compact family](candidates/projected-radius-comparison-base/README.md)
has901/642/616/614/613 integer unknowns, all at exact degree4. The613
profile has375 rows,10,013 terms and coefficient height2,445,790,974,704;
the642 profile has5,565 terms at height63,905,891. Each saves three
unknowns, one row and15 terms at unchanged height against its matching
79-guard predecessor. The [root review](reviews/comparison-base-quartics-root-peer.md)
checks every full coefficient collection and inverse. Complete projection
restoration precedes the signed-B theorem and62-coordinate comparison lift;
all78 guard values stay fixed, while three fresh witnesses guard NEWq4
in literal904. Its21-sign theorem then reaches967. All four root
normal/optimized checker/rebuild replays, nested complete source checks
and34 closed seals pass. The canonical101/368 page and Lean remain unchanged.

## Complete78-guard low-height quartics and independent family peer

The [retained-coefficient family](candidates/retained-radius-comparison-base/README.md)
has1493/846/701/637/623 integer variables at exact degree4, with
heights427/4750/737653/737653/938261. The623 profile has385 rows and
8,889 terms; it saves three variables and one row at unchanged height
against626. The [root review](reviews/comparison-base-raw-quartics-root-peer.md)
records every1255 raw/guard row and901 restriction identity in the exact
1493↔901 integer bijection. Only after complete restoration does the
nonpointwise comparison lift reach904 with fresh NEWq4 witnesses, then967.
All four root normal/optimized checker/rebuild runs and35 closed seals pass.
The [separate family peer](reviews/comparison-base-families-peer.md) independently
checks all ten compact/raw inverse certificates, all raw/guard identities
and62 snapshot recipes. Both focused root replays reproduce its final
receipts and reject nine corruptions. The compact613 family is a separate
height tradeoff. Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Literal constructor prose correction

The [constructor erratum](reviews/main-root-constructors-erratum.md) corrects
two aliases in the frozen21-sign note: raw36=y+1>=1, and
raw86=(t+x+y+M0+2)^(2^23)>=3. Root checked every cited original row.
The431-step constructor certificate already uses those correct literal
rows, so all exponent-positivity, guard and equation conclusions remain
unchanged. Neither constructor has fixed parity from these premises.
Frozen certificates and polynomials are preserved; subsequent proofs use
the corrected descriptions. Lean remains paused.

## Direct positive X and zero-offset research

The [direct-base research](research/ten-positive-direct-base/README.md)
replaces X=wq by X=q+x and adds a delayed divisibility carrier. Its
complete prototype has ten positive unknowns,107 operations and degree340.
The [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
checks the unbounded proof and a separate complete free-ring center cut:
remove the H denominator after whole-product projection, then recover q|X,
then justify X/q⁴ as an integer. Full materialized-candidate verification
is underway; this research checkpoint alone adds no accepted frontier.
The [zero-offset draft](research/ten-positive-zero-offset/PROOF.md) proposes
removing the inner constant offset in the scaled main base. Its stronger
ratio estimate suggests one fewer operation at unchanged degree; independent
review and literal checks are pending. The canonical101/368 page and
paused Lean remain unchanged.

## Complete direct-base107/340 endpoint accepted

The [direct-base candidate](candidates/ten-positive-direct-base/README.md)
has ten positive unknowns,107 live operations and exact degree340. It
replaces X=wq by X=q+x and recovers q divisibility from a new carrier
after the whole-product projection removes H. The [root review](reviews/direct107-root-peer.md)
and [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
verify the complete proof chronology and positive witness map. All four
root normal/optimized checks and rebuilds pass, with61 closed seals,
full four-port binding, universal center/norm identities and an attained
nonzero degree340 coefficient. This lowers degree by28 at six extra
operations relative to101/368. The cheaper complete canonical page stays
unchanged; no global optimum or new Lean endpoint is claimed.

## Bootstrap guard exchange accepted; coefficient benefit still being measured

The [guard-exchange proof](research/bootstrap-guard-exchange/README.md)
replaces base0.T's sign guard by the bootstrap Zminus1 guard, keeping78
guards. Signed-A/B index recovery and four actual source calls exclude
negative A without assuming raw86 even or interpreting a factorial early.
The converse changes one free bootstrap coordinate, six gates and one
constraint. The [root review](reviews/bootstrap-guard-exchange-root-peer.md)
and [independent peer](reviews/bootstrap-guard-exchange-peer.md) check
both whole-source existence maps. Both root author/peer normal/optimized
runs reproduce the final receipts, and all four research seals pass.
Actual coefficient profiling is separate; no new projected count follows
from the exchange alone. The [paired-index proposal](research/paired-index-guards/README.md)
is another unfinished lead, with its exact local factorial/binomial
obligation recorded. Canonical101/368 PDF/TeX and paused Lean are unchanged.

## Complete ten-positive99/368 endpoint accepted

The [zero-offset equation](candidates/ten-positive-zero-offset/README.md)
uses ten positive unknowns,99 live operations and exact degree368. The
stronger directly proved ratio bound permits A=mu*a+1; sharing the
already-needed muY product in A-1=(muY)(X+1) removes a second operation.
The [root review](reviews/zero99-root-peer.md) and [independent ordinary peer](reviews/ten-positive-zero-offset-ordinary-peer.md)
check full fresh canonical completeness, including positive auxiliary T
and final n, and every soundness license. All four root normal/optimized
literal checker/rebuild replays, both focused peer modes and62 closed
seals pass. Complete coefficient payloads, all99 live definitions and the
attained degree368 leading component are bound. This improves101/368 by
two operations. The complete canonical101/368 PDF/TeX is preserved while
minor presentation updates are batched, as requested. Lean stays paused.

## Guard-exchange profile finds no benefit in the tested configurations

The [paired coefficient profile](research/bootstrap-guard-exchange-profile/README.md)
tests both compact/raw sources at five support caps, keeping every setting
and source coefficient except the guarded value fixed within each pair.
All20 profiles in each root normal/optimized replay reproduce the complete
receipts. Integer substitutions verify and every quartic is independently
expanded. The [root review](reviews/bootstrap-profile-root-peer.md) records
unchanged variable/row/support/height metrics and one added term in each
projected exchange. The accepted guard placement is retained. An unrelated
raw baseline order gives a possible613-variable/9661-term point at the
same high coefficient height; a full separate package is under review.
No new accepted frontier follows from this research measurement alone.
Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Default-affine raw613 support improvement accepted

The complete [raw/default-affine613 quartic](candidates/retained-radius-default-affine/README.md)
reduces the expanded support from10,013 to9,661 monomials at the same
613 integer variables,375 quadratic rows, degree4 and coefficient height
2,445,790,974,704. The exact unchanged1493 input uses support8 for both
affine and quadratic restorations. All880 integer restorations and all
9,661 coefficients were independently replayed in normal and optimized
Python, along with both deterministic rebuilds; see the
[root review](reviews/default-affine613-root-peer.md). All78 original
guards remain. This is a new projection configuration, separate from the
bootstrap guard exchange. The canonical one-page equation remains unchanged.

## Combined direct/zero-offset105/340 accepted

The complete [ten-positive105/340 candidate](candidates/ten-positive-direct-zero-offset/README.md)
combines the direct coordinate X=q+x with A=mu*Y*(X+1)+1 and shared muY.
It improves107/340 to105/340; the accepted99/368 candidate retains the
lower operation count. All107 direct-parent and99 zero-offset-parent
definitions are bound to the same literal105 rows. The ordinary proof
retains delayed q-divisibility, and its positive completeness map uses the
same zero-offset kernels. Root replayed all four normal/optimized checks
and rebuilds, all complete payloads and degree340 certificates; see the
[root review](reviews/direct-zero105-root-peer.md). Lean remains paused.
The canonical101/368 PDF is unchanged while these small gains are batched.

## Paired index guard theorem accepted

The ordinary [paired-index proof](research/paired-index-guards/LOCAL_FACTORIAL.md)
replaces raw1214's sign with V>=1 and replaces the two t/k122 index-slack
guards with one guard on their product. The exact local factorial bridge
uses only calls1/5/6 at retained K/shifted-K pairs; call2 is used only
for parity. This gives77 predicates instead of78 before projection. Both
zero-existence directions and full source identities passed author,
independent peer and root review in normal/optimized Python; see the
[root acceptance](reviews/paired-index-guards-root-peer.md). Projected
equation sizes remain a separate task; no count is inferred from this theorem.

## Complete77-predicate quartic profiles accepted

The [paired-guard profile packet](research/paired-index-guard-profile/README.md)
contains20 complete equations, quartics and integer projection certificates.
Its compact support32/16/8 choices have610/611/613 variables and
10,053/8,717/8,622 terms, at common height2,445,790,974,704; the lower-height
639-variable choice has5,605 terms at height63,905,891. Raw projections
reach843/698/636/622 variables at heights4,750/737,653/737,653/938,261.
Every source row, guard predicate, integer inverse and full quartic was
checked before inheriting the77-guard proof. All four normal/optimized
checker/rebuild replays passed; see the
[root review](reviews/paired-guard-profile-root-peer.md). A product wire
produces the same projected quartics. No variable saving is inferred merely
from guard count. The canonical PDF and Lean sources remain unchanged.

## Reflected auxiliary parameter improves the nine-positive family

The complete [reflected-nine packet](research/nine-folded-reflected-parameter/README.md)
uses G=F(A+C+1)-A. It stays positive before margin recovery, is1 modulo C
and -A modulo F. Signed Pell folding gives the same soundness rank; the
actual odd completeness index removes the reflection sign. The original
and compact whole tuples now have408/1,191,570 and416/1,316,546
operations/degree, saving one operation and degree2. Root ordinary review
and all four normal/optimized checker/rebuild replays passed; see the
[root review](reviews/nine-reflected-root-peer.md). All source bindings and
the canonical page are preserved; Lean remains paused.

## One factorial bound replaces two more index guards

The ordinary [factorial-radius guard proof](research/factorial-radius-guard/PROOF.md)
replaces the retained K/shifted-K index slacks by f0>=2, reducing77 to76
source predicates. A seed without its bound is either at its true index
or has the exact collapsed coordinates X=A,Y=1. Literal digit/remainder
and ceiling equations exclude every collapsed branch before factorial
meaning is used. Both old slacks are then restored; conversely f0=K!>=6
supplies the new bound. An independent ordinary/source peer and both
normal/optimized root replays pass; see the
[acceptance record](reviews/factorial-radius-guard-root-record.md). Projected
counts remain separate. The canonical PDF and Lean sources are unchanged.

## Shared minimal reflection saves two more operations

The complete [minimal-reflection sibling](research/nine-folded-minimal-reflection/README.md)
reuses the stored product F-1 and sets G=A(F-1)+F. It preserves positivity
and both residue interfaces while using only two new operations. The nine-
positive whole-tuple circuits now have406/1,191,570 and414/1,316,546
operations/degree. Root reviewed the complete ordinary proof and all literal
checks, then replayed both checker/rebuild modes; see the
[root review](reviews/nine-minimal-reflection-root-peer.md). Full fixed
coefficients and source domains are retained. The canonical PDF is unchanged.

## Complete76-predicate quartics accepted

The [factorial-radius profile packet](research/factorial-radius-guard-profile/README.md)
contains15 complete equations and full quartics, including607 variables
with10,042 terms at height2,445,790,974,704. Fresh raw configurations give
612 variables/8,849 terms/height964,213 and611/8,753/45,769,499. Lower-height
choices reach840/695/633/619 variables at heights4,750/737,653/737,653/938,261.
All have exact degree4. The full source domain, every integer restoration
and every quartic coefficient passed both independent modes and both
deterministic root rebuilds; see the
[root review](reviews/factorial-radius-profile-root-peer.md). Only after
restoring the complete76-predicate parent is its ordinary theorem applied.
No projected count was inferred from guard count. Lean remains paused.

## Exact odd-rank sharing reaches405/413 operations

The complete [shared odd-rank sibling](research/nine-folded-shared-odd-rank/README.md)
reuses the literal source register RankPlusOne in B1=R+RankPlusOne, since
R=RankPlusOne-1. It deletes one private multiplication and preserves the
entire polynomial for every assignment. Both whole-tuple nine-positive
circuits now have405/1,191,570 and413/1,316,546 operations/degree. Full
node/operand inventories, coefficients, norms and attained-degree checks
passed both checker/rebuild modes under root replay; see the
[root review](reviews/nine-shared-odd-rank-root-peer.md). The canonical
page and Lean pause are unchanged.

## Early output-sign recovery reduces the source to75 predicates

The ordinary [output-sign extension](research/factorial-radius-output-sign/PROOF.md)
removes the raw93 guard. The exact unconditional eight-row ideal gives
N=f*r+(f-1)*s+f>=2 from the retained f>=2,r>=0,s>=0 predicates, before
the prefix proof or any power meaning. This restores the sole missing
early sign premise and reaches the actual76-predicate source; the reverse
map forgets that triple. Root reviewed all source coefficients and both
normal/optimized replays; see the
[root review](reviews/factorial-radius-output-sign-root-peer.md). There
are75 predicates before projection. Actual quartic sizes remain a separate
measurement; no new Lean or canonical-page change is made.

## Complete75-predicate quartics accepted

The [output-sign profile packet](research/factorial-radius-output-sign-profile/README.md)
contains17 complete degree4 equations with all integer inverse certificates
and full coefficients. Raw/default-affine support8/16 reaches604 variables
and9,676 terms at height2,445,790,974,704. Lower-height choices include
609 variables/8,823 terms/height964,213 and608/8,739/45,769,499; raw
low-height profiles reach837/692/630/616 variables at heights
4,750/737,653/737,653/938,261. The early missing sign is rederived from
actual source coefficients before prefix closure, then every domain row,
integer restoration and quartic coefficient is checked. Root replayed
both checker and rebuild modes; see the
[root review](reviews/factorial-radius-output-profile-root-peer.md). The
canonical one-page equation and Lean sources remain unchanged.

## Encoded-index sign is recovered:74 source predicates

The corrected [encoded-index proof](research/encoded-index-sign/PROOF.md)
removes raw59's explicit sign guard. Raw59 is not a power argument: its
only source use is E=raw59+1. Early direct signs give M>=1,E>=0 and a
modified642-coordinate prefix supplies the unchanged43-argument frame.
A weak-radix carry argument restores the factorial index bounds; then only
the first ten actual powers, exact binomial digits and the moduli-product
remainder prove M=product(1+fj)>1, hence raw59>=0. This reaches the actual
75-predicate source before using its semantic chain. Full author,
independent peer and root normal/optimized checks pass; see the
[root review](reviews/encoded-index-sign-root-peer.md). There are74
predicates before projection. No projected metric, Lean or page change is
claimed by this source theorem alone.

## Identical-polynomial transport contraction reaches98/103 operations

The complete [expanded-transport graphs](research/ten-positive-expanded-transport/README.md)
have ten positive inputs and98 operations at degree368, or103 operations
at degree340. Expanding W=1+gL moves L*B into the center, saving one
operation with the identical polynomial. The direct version also shares
q(q-1) in its carrier, saving a second. Full literal row maps, recursive
free-ring coefficient identities, whole payloads and all four normal/optimized
checker/rebuild root replays pass; see the
[root review](reviews/ten-expanded-transport-root-peer.md). Every parent
positive witness and ordinary proof step transfers by identity. Lean remains
paused; the canonical101/368 page is unchanged while minor gains are batched.

## Complete74-predicate quartics reach601 integer unknowns

The [encoded-index profile packet](research/encoded-index-sign-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches601
variables,9,661 terms and height2,445,790,974,704. Lower-height alternatives
reach606/8,808/964,213 and605/8,724/45,769,499 (variables/terms/height).
Every original domain row, both directions of the full raw/compact integer
bijection, every fresh signed inverse and every quartic coefficient passed
normal/optimized root replay, along with both deterministic rebuilds. The
modified prefix/frame and independent74-predicate source peer are checked
before semantic calibration; see the [root review](reviews/encoded-index-profile-root-peer.md).
No count was extrapolated from a deleted guard. Earlier families remain
preserved. Lean stays paused and the canonical one-page equation is unchanged.

## Actual power-output sign is recovered:73 source predicates

The [power-output proof](research/pow2-output-sign/PROOF.md) removes the
raw104 sign guard. Exact early rows give B=raw104>=-1 and D=B+2>=1;
the modified641-coordinate prefix and weak frame still bound every
positive base/index. Under B=-1, actual indices t and k122=t+1 are
consecutive. Sign-safe calls0/9 recover the paired seeds, then actual call2
forces a positive residue strictly below its divisor, a contradiction.
No local factorial semantics precede this sign recovery. Both existence
maps reach the actual74-predicate parent before inheriting its theorem.
Root read the full proof and checker and matched author/peer receipts in
both modes; see the [root review](reviews/pow2-output-sign-root-peer.md).
There are73 source predicates. Projected sizes require a separate complete
materialization; the measured601-variable family, canonical PDF and Lean
pause are unchanged.

## Six e13 proposal packages screened with reproducible inert checks

The [six-archive intake](research/incoming-e13c748234/README.md) records
complete hashes,2145 member pins, historical reuse and explicit domain
comparisons. Independent data checks reproduce33 full quartic expansions,
39 supported DAG censuses and54 coefficient bindings in both interpreter
modes. After the source76–110 placement, exact old inputs are read from
pinned Git blobs in memory. Root reviewed the report/checker and matched
both sealed receipts; see the [root review](reviews/incoming-e13-root-peer.md).
Squared/centered factorial and common modular Pell identities are useful
new research leads. The squared-radius transfer has an explicit missing-
K-bound obstruction, so no one-gate compiler improvement is assumed.
Natural395/394 and other advertised endpoint tradeoffs await their own full
ordinary/literal calibration review. The current measured601-integer family
and98/368 ten-positive evaluator are unchanged; Lean remains paused.

## Replaying sealed checks after incoming archive placement

The source76–110 placement removed old incoming ZIP paths. The separate
[compatibility runner](research/historical-archives-compat/README.md) supplies
35 exact hash-checked historical ZIPs temporarily from pinned Git objects,
runs an argv command, then removes only unchanged files it created. Existing
paths are preserved and concurrent wrapper lifetimes are serialized. This
keeps all sealed proof/checker bytes unchanged. For example:

```sh
python -B Computability/DiophantineConsistency/tools/with_historical_archives.py -- python -B Computability/DiophantineConsistency/research/encoded-index-sign-profile/check.py --output /tmp/encoded74-check.json
```

Root read the complete wrapper and replayed both modes of all10 integrity
controls; the frozen601 normal/optimized receipt bytes also match under the
runner. See the [root review](reviews/historical-archives-compat-root-peer.md).
This changes reproduction only, with no equation or Lean change.

## Complete73-predicate quartics reach598 integer unknowns

The [power-output profile packet](research/pow2-output-sign-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches598
variables,9,600 terms and height2,445,790,974,704. Lower-height alternatives
reach603/8,794/964,213 and602/8,710/45,769,499 (variables/terms/height).
Only raw104's guard is deleted. Every original domain row, both directions
of the592-coordinate raw/compact integer bijection, every fresh signed
inverse and every quartic coefficient passed normal/optimized root replay,
as did both deterministic rebuilds. The weak641-prefix/43-frame source
interface and branch-local sign proof precede inherited calibration; see
the [root review](reviews/pow2-output-profile-root-peer.md). All46 corruption
controls fail as expected. Earlier families remain preserved. Lean stays
paused and the canonical one-page equation is unchanged.

## Shifted-t index guard is recovered:72 source predicates

The [shifted-t proof](research/shifted-t-index-guard/PROOF.md) removes raw825's
explicit sign guard. Partial parent proofs first recover104 and the four
other required Pell pairs without using825. The actual choose-one row then
excludes the collapsed shifted-t pair: its numerator is at least b² for
t>=2, while the t=1 ceiling forces a digit at least2. Only after this
contradiction does the signed-index theorem recover825>0. No factorial1
meaning or premature call7 interpretation is assumed. A fresh triple reaches
the actual73-domain parent before using its complete theorem. Root read the
entire proof/checkers and matched author and independent peer receipts in
both modes; see the [root review](reviews/shifted-t-index-guard-root-peer.md).
There are72 predicates before projection. The measured598-variable family
remains current until fresh complete profiles pass. Lean and page unchanged.

## Complete72-predicate quartics reach595 integer unknowns

The [shifted-t profile packet](research/shifted-t-index-guard-profile/README.md)
contains17 complete degree4 equations. Raw/default support8/16 reaches595
variables,9,586 terms and height2,445,790,974,704. Lower-height alternatives
reach600/8,770/964,213 and599/8,696/45,769,499 (variables/terms/height).
Only raw825's guard is deleted. Every domain row, both directions of all592
raw/compact restorations, every fresh signed inverse and every quartic
coefficient passed normal/optimized root replay and both deterministic
rebuilds. Both the95-identity source checker and independent15-cut peer are
pinned and replayed, with exact call7/t=1 chronology and50 corruption
controls; see the [root review](reviews/shifted-t-index-profile-root-peer.md).
Earlier families remain preserved. This is the direct quartic lane; the
fewer-variable norm/display tradeoffs remain separate. Lean stays paused
and the canonical one-page equation is unchanged.

## Squared-radius RAW prototype: complete finite checks accepted

The [separate RAW prototype](research/squared-radius-source-prototype/README.md)
changes only radius row75 and exchanges f>=2 for f>=K at the same guard
triple. All12 complete equations, signed inverse certificates, quartics and
censuses passed root normal/optimized checks and both deterministic rebuilds.
The default prototype has594 variables and9,588 terms: one fewer variable
and two more terms than595/9,586. No new consistency endpoint is inferred
from that measurement. The complete ordinary source proof and fresh
canonical completeness remain separate review obligations; see the
[root finite review](reviews/squared-radius-prototype-root-peer.md).
The accepted595-variable family, canonical page and Lean pause are unchanged.


## Complete squared-radius equations:594 integer unknowns

The [complete ordinary source proof](research/factorial-square-guard-exchange/FULL_SOURCE.md)
and its independent audit are now accepted and exactly bound to the
[frozen RAW prototype](research/squared-radius-source-prototype/README.md).
All12 materialized quartics therefore inherit the ordinary Con(ZFC)
calibration. The first radius is f² and its one guard is f>=K; the second
radius remains g*t². Direct bounds justify all8 range graphs before product
semantics, and completeness recomputes every radix/frame/Pell witness.
Root replayed both complete source audits in normal and optimized Python;
all receipts match. See the [combined root review](reviews/factorial-square-calibration-root-peer.md).

The default complete degree4 equation has594 integer unknowns,9,588 terms
and height2,445,790,974,704. Lower-height alternatives are598/8,564/964,213
and597/8,504/45,769,495 (variables/terms/height). The595-variable predecessor
has two fewer terms and is preserved. This resolves the preceding prototype's
ordinary-proof obligation without changing its sealed finite-scope flags.
The canonical ten-positive page remains unchanged; Lean remains paused.


## Complete common-radius quartic:591 integer unknowns

The [common factorial-radius proof](research/common-factorial-square-radius/PROOF.md)
keeps72 predicates with both radii f² and the one joint guard f>=K+g.
It derives g>=0 before f, repairs the t=1 shifted-seed argument using g<=f,
and rebuilds every radix/frame/Pell witness for completeness. The exact
RAW binding and a separate invertible integer row operation sharing the
base moduli license all24 checked [RAW/CSE quartics](research/common-squared-radius-source-prototype/README.md).
Root's four ordinary replays, both finite checks and both deterministic
rebuilds all pass and match their seals; see the [combined review](reviews/common-squared-radius-root-peer.md).

CSE support16/default gives591 integer variables,9,657 terms and height
2,445,790,974,704 at degree4. Lower-height CSE choices include596/8,328/964,213
and595/8,232/45,769,613 (variables/terms/height). The594-variable predecessor
has69 fewer terms and is preserved. This is the direct quartic family;
other domains and compact norm equations remain separate tradeoffs.
The canonical ten-positive page is unchanged and Lean remains paused.


## Mixed-radix seed: complete-recipe comparison is negative

The [closed mixed-radix experiment](research/mixed-radix-bfs-seed/README.md)
saves221–233 seed bits and37–39 base62 symbols, while its complete printed
recipes grow by26–35 nonwhite characters after paying for the product and
halt decoder. Root read the full proof/renderer and matched both full
render/reconstruction receipts; every action, tile and coefficient byte
remains exact. See the [root review](reviews/mixed-radix-seed-root-review.md).
All three standalone PDF/TeX siblings are preserved. The canonical page
remains the better tested display; this does not rule out other decoders.


## Squared output bounds give 575 integer unknowns

The [64-predicate ordinary proof](research/range-output-square-frame/PROOF.md)
replaces eight range output bounds by their squares, then derives their
quotient signs after positive-power recovery. All earlier seed arguments
keep their required signs; a retained positive ordinate is essential to the
signed-output lemma. Fresh completeness rebuilds the entire new frame and
private Pell data. The exact binding licenses all 24 checked
[RAW/CSE quartics](research/squared-range-frame-source-prototype/README.md).
Root's six ordinary replays, both complete finite checks and both
rebuilds pass; see the [combined review](reviews/squared-range-frame-root-peer.md).

The complete CSE/default equation has 575 integer unknowns, 7,225 terms and
height 2,445,790,974,704 at degree 4: 16 fewer variables and 2,432 fewer terms
than 591/9,657. Lower-height alternatives give 580/5,768/964,213 and
579/5,832/45,769,613 (variables/terms/height). These improve the direct
quartic family; compact norm equations remain separate. All predecessors
are preserved, the canonical ten-positive page is unchanged and Lean is paused.

## Review of the compact-kernel next-steps note

The note added in `0d0a01670f` supplies useful degree accounting and a
one-word transport research direction, rather than a new equation. Its
[current text](candidates/ten-positive-scaled-norm/NEXT_STEPS.md) corrects
three overstatements: the suggested product of two quadratic factors has
degree four; the current transport argument needs a bound on
`W/(q-1)` before divisibility is known, not merely `W>f`; and the failure
of a direct one-word substitution is not an impossibility theorem for
all encodings. No degree floor or nine-variable lower bound has been
proved. The canonical page and accepted metric tables are unchanged.


## An existing square reduces the direct quartic family to 572 integers

The [63-predicate ordinary proof](research/power0-output-square-frame/PROOF.md)
uses the existing square of the first power output in its frame and derives
that output's sign after a separate guarded output orients the t pair.
Both earlier pairing arguments use the replacement support. Fresh
completeness rebuilds the entire new frame and private Pell data.
The [complete RAW/CSE quartics](research/power0-square-frame-source-prototype/README.md)
are exactly bound to that proof; see the
[combined root review](reviews/power0-square-frame-root-peer.md).

The best equation has 572 integer unknowns, 7,211 terms, degree four and
coefficient height 2,445,790,974,704. It saves three variables, one residual
and fourteen terms against 575/7,225 at unchanged height. Lower-height
alternatives give 577/5,754/964,213 and 576/5,818/45,769,613
(variables/terms/height). All 24 full polynomial checks, both independent
checker modes and both root rebuilds pass. The compact canonical page
is unchanged by this quartic step; Lean remains paused.


## Canonical complete page: 98 operations and exact degree 360

The [updated equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) now print the complete ten-positive equation
at degree 360 in 98 operations, improving the preserved 101/368 page by
three operations and eight degrees. The full constant body remains on the
same Letter page in 9-point body type: all 436 seed characters, decoder,
943 tiles and four coefficient recipes are retained verbatim.

The [ordinary index-weight proof](research/ten-positive-index-weight/PROOF.md)
uses the pre-transport inequality k>H to replace HI by kI. Its positive
polynomial n shear proves completeness. A separate direct-base equation
has 103 operations and degree 332. All six root source audits, actual-TeX
parsing, both render modes and full tuple reconstructions pass; see the
[root review](reviews/ten-index-weight-root-peer.md) and
[page evidence](candidates/one-page-index-weight10/README.md).
The selected nonzero homogeneous component proves exact degree rather
than a sampled degree. Every earlier page, including its TeX, is preserved.
Lean remains paused; no global simplicity minimum is claimed.


## Existing-square transport: 97/368 and 102/344 alternatives

The [complete square-weight equations](research/ten-positive-square-weight-tradeoff/README.md)
reuse the existing I² gate in L and delete one multiplication. The ordinary
pre-transport inequality I>k>H preserves soundness; the positive polynomial
n shear proves completeness. Exact source, norm and leading-form checks
give 97 operations at degree 368, or 102 operations at degree 344.
These save one operation against 98/360 and 103/332 while raising degree.
All six fresh root normal/optimized replays pass, with 27 actual-artifact
corruptions rejected in each mode; see the
[root acceptance](reviews/ten-square-weight-root-peer.md).
The canonical 98/360 one-page PDF/TeX is retained, all predecessors are
preserved and Lean remains paused.

## A second signed output reduces the quartic family to 569 integers

The [62-predicate ordinary proof](research/power3-output-square-frame/PROOF.md)
appends the square of output106, uses it only in the frame, and removes
that output's scalar guard. Actual call3 keeps output106. Independent
supports orient its t pair before the signed residue recovers106=f^t>0.
The delayed bound for130 and its five related signs are restored before
later source semantics. Fresh completeness rebuilds the changed frame
and private Pell witnesses. Both common factorial radii remain unchanged.

The [complete equations and certificates](research/power3-square-frame-source-prototype/README.md)
include 24 RAW/CSE configurations. The best has **569 integer unknowns,
363 residuals, 7,197 monomials and exact degree four**, with coefficient
height 2,445,790,974,704. Its 885 signed restorations recover every parent
coordinate; none is unconstrained. Savings vary by configuration, as
recorded in the [combined root review](reviews/power3-square-frame-root-peer.md).
Lower-height CSE alternatives include 574/5740/964213, 573/5804/45769613,
581/5731/938261, 596/5521/737653, 654/4784/737653 and 783/3599/4750
(variables/terms/height). The retained parent is 1454/4791/428.

Both ordinary checker modes, both complete finite checker modes and both
full rebuilds pass fresh root review and match retained author receipts.
All prior packets remain preserved. This improves the direct quartic
family; the canonical ten-positive 98-operation/degree-360 page is unchanged.
Lean formalization remains paused, and equation-size research continues.

## Direct tile indices shorten the complete printed recipe

The [directly indexed standalone page](research/indexed-tile-enumeration/equation.pdf),
with [TeX](research/indexed-tile-enumeration/equation.tex), removes the
sorted-rank computation for the same 943-tile language. The complete
constant recipe falls from 2,393 to 2,343 nonwhite printed characters;
the whole page falls from 3,217 to 3,167. All index explanations, the full
436-character seed and its 62-character alphabet are counted. The page
retains ten positive unknowns, 98 operations, exact degree 360 and the
same one-Letter-page layout.

The new selector order changes K. Its [ordinary proof and root review](research/indexed-tile-enumeration/PEER_REVIEW.md)
rebuild the entire native witness and cofinal rank controller for the new
coherent tuple; they do not transfer old packed words pointwise. All 430
transitions, 943 tile conjugacies, 66,062 native basis identities, four
complete integers and controller unit/order/lift facts pass independent
checks. Eight fresh root normal/optimized build, render, checker and
artifact runs match the author records; each artifact run rejects 40
actual corruptions and passes two complete controls.

This 50-character gain is retained as a research alternative. The canonical
98/360 PDF and TeX stay unchanged until a larger improvement is ready.
Lean remains paused and the reduction goal continues.

## Six shared sums permit six product guards

The [anchored product-guard proof](research/shared-remainder-product-guards/PROOF.md)
replaces twelve scalar sign guards by six quadratic product guards. It
uses only ten exact source row sums and four retained anchor pairs:
r+s=a+b>=0 together with rs>=0 forces both removed signs. The signs are
restored before any existing Pell or source interpretation is invoked.
Every raw arithmetic coordinate, including the complete W/A/Pell data,
stays fixed; only guard witnesses are rebuilt.

The full parent drops from 1,454 coordinates and 1,248 residuals to
**1,436 coordinates and 1,242 residuals**, with 56 predicate graphs.
Fresh root normal/optimized checks and rebuilds pass, as does the
independent peer review; see the [root acceptance](reviews/shared-remainder-product-guards-root-peer.md).
The literal checker verifies 16 source identities and rejects 23 actual
corruptions. A separate audit checks all 118 old/new graphs and the
32 possible abstract anchor selections, with 192 difference identities.
Only the fixed six replacements are materialized.

Projected quartic savings remain to be measured from complete equations
and certificates. The current best checked direct quartic still has
569 integer unknowns. The canonical compact page is unchanged and Lean
remains paused.

## Eight new proposal archives at 45b399ec51

The [static intake](research/intake-45b399ec51/TRIAGE.md) authenticates all
eight archives, 1,693 members and 237 statically indexed Python files.
It records exact read scopes and distinguishes delivered claims from
accepted results. No incoming program was executed for this checkpoint.
An independent root replay verifies every member hash and the AST index.

The most promising new claims are ten-positive 92/283 and 93/278 saturated
Pell equations, a ten-positive 96/266 coprime-fusion equation, and direct
quartics with 517 or 519 integer variables. Complete mathematical and
code reviews are in progress. The current page and accepted comparison
frontier are unchanged by intake alone. New shared-sum, quotient-frame
and transport-majorant mechanisms are recorded as separate research leads.
Lean remains paused; successful substantial compact improvements will
replace the canonical PDF and its standalone TeX after full verification.

## Complete shared-remainder compiler reaches 557 integer variables

The [new complete finite family](research/shared-remainder-product-source-prototype/README.md)
now realizes the separately approved 56-guard source theorem. Its best
checked default has **557 unrestricted integer variables, 363 rows,
6,937 quartic terms and height 2,445,790,974,704**. This saves twelve
variables and 260 terms against the preserved 569-variable equation,
at the same row count and height. All 24 RAW/CSE profiles, complete
coefficient maps, inverse restorations and exact censuses pass fresh
normal/optimized rebuilds and independent checks; 89 corruption controls
are rejected. The default has 879 signed restorations and no unconstrained
deletion. Actual deltas for every configuration are retained in the packet.

The [root acceptance](reviews/shared-remainder-product-source-root-peer.md)
composes these finite results with the exact complete ordinary source
theorem and native calibration. A finite polynomial check alone does not
supply that interpretation. Earlier packets remain preserved. The
compact ten-positive page and paused Lean work are unchanged by this result.

## Significant compact-page improvement: 92 operations, degree 283

The canonical [PDF](equation.pdf) and standalone [TeX](equation.tex) now
print the [complete saturated Pell equation](candidates/one-page-saturated10/README.md):
**ten strictly positive unknowns, 92 operations and exact degree 283**.
This saves six operations and lowers degree by 77 from the preserved
98/360 page. All constants, tiles, the decoder and complete 436-character
numeral fit on the same Letter page in 9-point body type.

The [ordinary proof](research/ten-positive-saturated-pell/PROOF.md)
establishes both directions with fresh positive witnesses, coprime root
recovery and a global attained degree proof. Its whole indexed native
composition licenses the shorter fixed recipe jointly at all four ports.
Independent actual-TeX parsing binds every displayed definition and the
complete boxed equation to all 92 live gates, and verifies every rendered
front glyph and the whole PDF constant body. Normal/optimized source,
renderer, parser and artifact checks pass. See the
[root promotion review](reviews/ten-saturated-pell-root-peer.md).

Separate complete tradeoffs use 93 operations at degree 278 and direct
positive X charts with 98/258 and 99/254. Earlier pages and complete source
packets remain preserved. No global optimum or new Lean endpoint is claimed.

## A derived anchor permits a seventh product-guard exchange

The [new ordinary source proof](research/shared-binomial-digit-product-guard/PROOF.md)
replaces scalar guards on raw123 and raw564 by one product guard. Retained
raw94/raw95 signs and literal rows derive raw91>=1; with retained raw537,
the exact source identity gives raw123+raw564>=1. The product then restores
both removed signs before any inherited source interpretation. Each
direction fixes the whole raw body and rebuilds only guard auxiliaries.

The complete literal parent has **55 guards, 1,433 variables and 1,241 rows**.
Four exact source ideals, every guard graph, full maps and whole inherited
seals pass independent normal/optimized checks with 27 corruption controls.
See the [root acceptance](reviews/shared-binomial-digit-product-root-peer.md).
No projected improvement is predicted: the measured default remains the
557-variable quartic pending a separate full compiler packet. The canonical
92/283 page and paused Lean work are unchanged.

## Reviewed Round14 direct quartics: 517 and 519 integer variables

The [ordinary review](research/intake-45b399ec51/ROUND14_REVIEW.md)
approves the new factorial/carrier architecture and signed-Pell proof
relative to the named inherited C222/refutation contracts. Complete
[scoped reproduction](research/round14-direct-reproduction/README.md)
and fresh root normal/optimized runs rebuild all 34 distinct endpoint
artifacts exactly, including full quartics, signed inverses and integral
translations. The independent static collector rejects twelve actual
data corruptions. See the [root acceptance](reviews/round14-direct-root-peer.md).

The new points are **517 unrestricted integer unknowns, 310 rows, 6,774
quartic terms, height 3,904,267**, and **519 unknowns, 321 rows, 6,253
terms, height 411,060**. Both have exact degree four. All earlier complete
families are preserved. The architecture generators themselves were not
replayed; their frozen raw interfaces and ordinary semantics were reviewed
separately. The unrelated norm branch and Lean were not executed.

The eight newly unpacked manuscript releases now occupy111 through118
under con-zfc-diophantine-forms. Exact historical ZIPs remain readable
from the pinned Git arrival commit; selected adapters authenticate their
whole bytes without restoring them into docs/incoming. This relocation
does not itself approve any other incoming mathematical claims. The
canonical ten-positive92/283 PDF and TeX remain unchanged.

## Reusing the existing b saves one more multiplication

The [complete reused-b extension](research/ten-positive-reused-b-weight/README.md)
gives **91/283, 92/278, 97/258 and 98/254** operation/degree profiles
with ten strictly positive unknowns. It replaces L=k(T+alpha) by the
already evaluated b=c(T+alpha)-R. The ordinary proof bounds b before
transport and constructs a fresh positive n. The changed remainder has
degree six, below all existing center defects, so every exact degree
and nonzero global leading form is preserved.

Independent full proof/code review and six normal/optimized replays pass;
all 152 interfaces and 378 gates, complete parent-row maps and both whole
native tuples are bound. Twenty graph corruptions and 31 malformed
artifacts are rejected. See the [root acceptance](reviews/ten-reused-b-root-peer.md).
This one-operation gain is recorded separately while further changes are
batched; the canonical complete92/283 PDF and TeX remain unchanged.
Lean work remains paused.

## The complete 55-guard source family reaches 554 variables

The [new finite packet](research/shared-binomial-digit-product-source-prototype/README.md)
materializes every RAW/CSE profile of the separately accepted seventh guard
exchange. Its best default has **554 integer variables, 362 rows, 6,927
quartic terms and height 2,445,790,974,704**. Against the preserved557
family it saves three variables, one row and ten terms. Both root checker
JSONs and all four normal/optimized full replay transcripts match the
author exactly; every coefficient, signed inverse and census passes, and
90 actual corruptions are rejected. An independent retained-set audit
checks all24 old/new profiles and their actual three delta classes.

The [root acceptance](reviews/shared-binomial-digit-product-source-root-peer.md)
composes those finite results with the exact complete ordinary source
theorem. All coefficient/term alternatives and earlier equations remain
preserved. The separate Round14 family reaches517/519 variables; this
554 result is progress within the older source pipeline. The canonical
92/283 PDF and TeX and paused Lean work are unchanged.

## Removing the center gives 89/288 and 95/262 tradeoffs

The [complete uncentered packet](research/ten-positive-uncentered-b-weight/README.md)
uses **89 operations at exact degree288**, or95 at degree262 on the
direct chart, with ten strictly positive unknowns. The already folded
odd Pell index excludes the first two auxiliary possibilities; the fifth
index forces a strong enough transport bound to omit Cg altogether.
Positive completeness follows from the exact forward n_new=n_old+Cg
shear; positivity of a reverse shear is not assumed.

The global degree proof is a polynomial cancellation argument with a
uniquely dominant final term and explicit nonzero highest coefficients.
Independent full proof/code review and all six normal/optimized replays
pass, covering every live gate, all four parent routes, both whole native
tuples,10 source corruptions and28 malformed artifacts. See the
[root acceptance](reviews/ten-uncentered-b-root-peer.md).
These save operations with slightly higher degree than their centered
parents. The canonical complete92/283 PDF and standalone TeX remain
stable while further changes are batched. Lean remains paused.

## Pointwise guard compression for both Round14 sources

The [new ordinary theorem](research/round14-pair-guard-compression/PROOF.md)
licenses nine individual pair exchanges in the517 ancestry and eight
in519. Exact common-numerator and factorial/digit identities restore all
removed signs over every unrestricted integer body zero, before source
semantics. Both directions fix the entire body tuple and choose fresh
Legendre witnesses. Mixed and factored source views are proved separately.

Independent normal/optimized checks bind19 exact identities,123 old guard
graphs and complete noncontiguous body maps, and reject28 actual corruptions.
Every old guard auxiliary is checked to occur only in its own guard row;
the appended private Horn body coordinate is retained. See the
[root acceptance](reviews/round14-pair-guard-root-peer.md).
This is an ordinary guard-domain result, with no new materialized equation
or projected count. Existing517/519 quartics and the complete92/283 PDF
and TeX remain unchanged until separate complete candidate checks pass.
Lean remains paused.

## Complete 89-operation one-page alternative

The separately preserved [PDF](candidates/one-page-uncentered89/equation.pdf)
and [standalone TeX](candidates/one-page-uncentered89/equation.tex) print the
entire ten-positive,89-operation,degree288 equation, including every fixed
constant and the full436-character numeral. It fits on one Letter page in
9-point type, with3,111 nonwhite extracted characters. Compared with the
canonical92/283 page it saves three operations and increases degree by five.

Independent actual-TeX/PDF review checks all31 definitions, all89 live gates,
every rendered formula glyph, the whole constant body and both compressed
and raw bytes of the complete indexed coefficient tuple. Root fully read
the independent parser; fresh normal/optimized runs exactly match both
retained peer receipts, rejecting13 actual printed mutations. All23 closed
payload files and110 peer bindings pass. See the
[root acceptance](reviews/one-page-uncentered89-root-peer.md).
The canonical92/283 PDF and TeX remain stable while further gains are batched;
Lean remains paused.

## One multiplication shared across all five direct variants

The [complete direct-carrier packet](research/saturated-direct-carrier-cse/README.md)
reuses the already live qbJ=q*(q-1) in P1=q³*qbJ and deletes its private q⁴
gate. Every whole output polynomial is unchanged. Operation/degree profiles
become97/258 and98/254 for the saturated upper/sharp routes,96/258 and97/254
for reused-b, and94/262 for uncentered transport. All independent positive
inputs, both whole native tuples and the complete global degree proofs transfer
by the free polynomial identity and induction through every remaining row.

Root read the entire proof and executable closure and independently replayed
all six normal/optimized producer/checker/artifact commands. Every receipt
exactly matches the author;36 complete malformed artifacts are rejected per
mode. All old/new rows, sole consumers, coefficient bytes and leading-form
records are bound. The restricted associative search has no global minimality
claim. See the [root acceptance](reviews/saturated-direct-carrier-cse-root-peer.md).
These minor gains are batched; the canonical92/283 PDF and TeX remain unchanged,
and Lean remains paused.

## Complete paired-guard quartics reach 496 integer variables

The [reviewed full source compiler](research/round14-pair-guard-projections/README.md)
materializes twelve projection profiles and all24 plain/centered quartics from
the sealed ordinary pair-guard theorem. Centered derived support16 gives
**498 variables,309 rows,6,615 terms,height3,904,259**, improving the preceding
517/310/6,774/3,904,267 in every measure. Quadratic-first gives **496 variables,
307 rows,5,924 terms,height5,061,227**, with higher coefficient height.
The lower-height ancestry gives502/320/6,111/411,053, or501/319/5,615/620,468.
Every unknown is an unrestricted integer and every complete equation has exact
degree four. All alternatives and predecessors remain preserved.

The whole producer/checker/vendor closure was reviewed independently before
its first full run. Root and peer each ran both full checker modes and both
deterministic rebuild modes; all receipts match the author exactly. Every
coefficient, monic restoration, source body/ideal/power map, signed inverse
fixture and full translation is checked, rejecting38 actual corruptions per
mode. Each inverse explicitly initializes the two genuinely free coordinates
before reverse monic restoration. A separate independent collector, fully read
and replayed by root in both modes, verifies all26 complete quartics and all
calibration chains and rejects eight additional malformed binding controls.

The [root acceptance](reviews/round14-pair-guard-projections-root-peer.md)
composes those finite premises with the sealed ordinary guard theorem and
its explicit inherited C222/Pell/refutation calibration. The canonical compact
92/283 PDF and TeX remain unchanged; Lean remains paused. A later incoming
Round15 proposal claims442 variables and is a separate review priority; that
claim is not promoted by this acceptance.

## Complete unified-binomial quartic: 442 integer unknowns

The [reviewed Round15 direct equation](con-zfc-diophantine-forms/125-unified-binomial-round15/direct/integer442/)
has **442 unrestricted integer unknowns,290 residuals,exact degree four,
4,652 terms and coefficient height128,446**. It improves the496-variable
checkpoint in every listed measure and also improves the502-variable
lower-height alternative. Their complete equations remain preserved.
The separately checked natural architecture reaches329 nonnegative unknowns,
with six complete natural alternatives. Natural and integer domains stay explicit.

One binomial simultaneously certifies the factorial and CRT product. Its raw
bounds establish the pure radix before digit meaning. Selectively even Pell
indices, residue-one orientation and seven weighted guard pairs reduce the
signed source. Root and peer independently reviewed the complete unbounded
arguments, actual source/seed/frame/guard/remainder interfaces and full executable
closure before execution. Soundness and completeness rebuild private Pell
witnesses from the semantic front tuple.

Both fresh root normal/optimized scoped replays exactly match the peer. Each
reconstructs all72 architecture files,15 signed-source files and five centered
endpoint files byte for byte; all569 original private archive members remain
unchanged. The independent auditor checks all natural/integer projections,
180 monic restorations,15 declared free coordinates,13 separate private-slack
inverses,54 integral translations and every quartic coefficient, rejecting14
actual corruptions per mode. The canonical placement's omitted duplicate imports
are supplied only in private exact-archive trees, with no repository restoration.
See the [root acceptance](reviews/round15-direct-root-peer.md),
[ordinary/source review](research/intake-5f3379063d/ROUND15_DIRECT_REVIEW.md)
and [scoped reproduction](research/round15-direct-reproduction/README.md).

The inherited C222/Pell/refutation calibration remains explicit; no new internal
ZFC or Lean endpoint is claimed. The canonical ten-positive92/283 PDF and TeX
remain unchanged because this is a separate quartic tradeoff. Lean stays paused.

## Eight newer bundles: full domain-aware intake retained

The [new static intake](research/intake-5f3379063d/README.md) authenticates all
eight original archives and2,686 members at commit5f3379063d. Root read all
three inert programs and replayed each in normal/optimized Python; complete
inventory and literal receipts exactly match the author. Seventeen complete
quartics were independently expanded with34 actual row/coefficient corruption
controls per mode. The height-one polynomial's entire literal coefficient list
and census also pass, while its lifting/compiler closure remains a separate
obligation. All23 intake payload files and391 whole-file peer bindings are sealed.

The principal442 integer route has its separate full approval already recorded.
The319-natural modular-binomial and261-natural pooled-Pell constructions are
new review and composition leads, with different domains and explicit source,
signed, majorant and completeness obligations. Their counts do not describe
unrestricted-integer quartics. Other source34 integer circuits retain separate
six-port calibration. Existing ten-positive89/91/92/94/96/97 profiles reprinted
in these bundles add no new compact record by their counts alone. The
[future-lead notes](research/intake-5f3379063d/FUTURE_LEADS.md) preserve those
opportunities without promoting unchecked source/compiler claims. The canonical
92/283 PDF/TeX and paused Lean work remain unchanged.

## Complete ten-positive 86-operation cost alternative

The [q-cube-normalized equation](research/ten-positive-qcube-normalization/README.md)
has **86 live operations and exact global degree466**, with ten strictly positive
unknowns. It evaluates Y=q³s, absorbs the integral old Y/q³ term into a fresh
positive n, and cancels a common q³ from both cleared carrier coordinates.
The entire old norm is q^12 times the new one under n_old=n_new-s. This is a
cost/degree tradeoff against89/288; the source proof excludes negative transport
directly before using the shifted integer, and its canonical positive converse
uses the explicit inherited q³|Y condition. No reverse positive shear is assumed.

Root and peer reviewed the complete ordinary proof and all source/collector/
artifact code. All six fresh root normal/optimized receipts exactly match the
author. Thirty-six free polynomial interfaces cover every actual gate; both whole
coefficient tuples, all215 source pins and262 peer bindings are authenticated.
Nine graph and33 complete artifact corruptions are rejected per mode, with four
positive/output controls. The global cancellation proof identifies the entire
105-term leading form and a nonzero coefficient -2^10*beta^326, proving466
without relying on a sampled ray. See the
[root acceptance](reviews/ten-qcube-normalization-root-peer.md).

All earlier equations remain preserved. The canonical92/283 PDF and TeX stay
stable while the cost/degree alternatives are compared; a separate complete
86/466 comparison page is now accepted with its complete PDF and standalone TeX. Lean remains paused.

## Ordinary factorial-output guard removal accepted

The [new staged theorem](research/round15-factorial-output-guard/PROOF.md)
proves that the exact Round15 source's remaining37 predicates already force
F>=1. It interprets only the retained t pair first: raw rows give B>=1,q>=2
and L>=2; the q request orients the pair, then the F²+1 request gives V>=1
for arbitrary signedF. The literal identity FB=V+slack recovers F's sign
before any F-dependent seed or K meaning is used.

All522 body coordinates and446 rows are fixed; only the private F Legendre
triple is discarded and existentially restored. Root and independent reviewer
read the complete proof and source boundary; fresh normal/optimized root
receipts exactly match the author. Twenty actual identities, all38 guard
graphs/privacy, the complete frame and all18 power interfaces pass, with30
actual corruptions rejected per mode. See the
[root acceptance](reviews/round15-factorial-output-guard-root-peer.md).
This is an ordinary guard-domain theorem, without a new projected count or
materialized quartic. The442 checkpoint and canonical92/283 PDF/TeX remain
preserved, and Lean stays paused.


## Complete 86-operation comparison page accepted

The [new one-page PDF](candidates/one-page-qcube86/equation.pdf) and
[standalone TeX](candidates/one-page-qcube86/equation.tex) print the entire
**ten-positive,86-operation,degree466** equation, including all fixed constants
on the same Letter page in9-point type. Root and peer reviewed all31 actual
printed definitions, the boxed equation and86 live gates. Fresh normal and
optimized root checks match the peer exactly;19 actual printed corruptions
are rejected per mode. The entire rendered constant body,436-character numeral,
whole indexed tuple and all four coefficient payloads are authenticated.

The closed27-file payload and117 whole-file peer bindings pass root checks;
root also visually inspected the final page. See the
[root acceptance](reviews/one-page-qcube86-root-peer.md). This saves six
operations against92/283 while adding183 degrees, so it remains a separate
comparison and the canonical equation.pdf/.tex retain92/283. All predecessors
are preserved. Lean remains paused.


## Both Round15 sign guards are jointly redundant

The [joint ordinary proof](research/round15-signed-frame-orientation/PROPOSAL.md)
proves that the exact522-coordinate/446-row body and36 retained predicates
already force F>=1 and A>=2. It first interprets t at a signed center,
recovers F, then uses the two requests on the SAME positive even-K ordinate
to exclude A<0. The second request uses the signed negative output of the
first; no output sign is assumed early. This is a new joint argument, not
an application of the F-only theorem with its A premise missing.

Root and peer reviewed the full unbounded proof and all340 checker lines
before replay. Fresh root normal/optimized receipts exactly match the author:
32 source/frame identities,four universal signed norm identities,all38 old
guard graphs/privacy,the full37-atom frame and18 interfaces pass;58 actual
corruptions are rejected per mode. Both witness directions fix the complete
body and restore only the two private Legendre triples. The closed11-file
payload and48 root bindings are sealed; see the
[root acceptance](reviews/round15-signed-frame-root-peer.md). No new projected
count is claimed pending the separate compiler packet. The442 checkpoint,
canonical92/283 PDF/TeX and paused Lean work remain preserved.


## Shared-cap source reduction: ordinary proof and design accepted

The [signed-cap study](research/signed-pell-cap/README.md) extends pooled
Pell index recovery to signed ordinates. Including the positive cap itself
in the pooled residue forces the center positive at an even frame index.
The complete absolute-center anchor and constructive CRT/completeness order
are independently reviewed; see the [root review](reviews/signed-pell-cap-root-peer.md).
Its [source design](research/signed-pell-cap/DESIGN.md) pools all15 original
undoubled pairs for18 calls, retaining one full cap comparison, the derived
t+1 pair and all five shared moduli. The literal successor source/checker is
still pending. This is an ordinary mathematical lead with no new equation or
count claim; all accepted pages, quartics and paused Lean work remain preserved.


## Complete direct quartic reaches436 integer variables

The [joint centered equation](research/round15-sign-guard-projections/full-data/joint_F_A/centered/equation.json)
has **436 unrestricted integer variables,288 rows,exact degree4,4,624 terms,
height128,446 and row height256**. It saves6 variables,2 rows and28 terms
against the preserved442 parent at unchanged heights. The F-only intermediate
has439 variables/289 rows/4,638 terms at the same heights; both complete plain
charts remain available too. All four endpoints have their own exact complete
source, projection and translation certificates.

Root and peer read the entire new code/proof closure before execution. All
four fresh root checker/rebuild receipts and stdout files exactly match the
author. Every one of the40 generated full-data members rebuilds byte-exactly;
36 actual corruptions are rejected per collector mode. Root separately checked
the entire factored variable/row maps and180-step lists: the only retained
coordinate losses are the declared3/6 guard auxiliaries, with the same15 free
coordinates and full reverse reconstruction. The closed85-file author payload
and separate root replay packet are sealed; see the
[root acceptance](reviews/round15-sign-guard-projections-root-peer.md).
No global optimum or new internal-ZFC/Lean theorem is claimed. The canonical
ten-positive92/283 PDF and TeX remain the separate compact display. Lean stays paused.


## A private-helper reflection replaces two guards by one

The [new ordinary normalization](research/round15-helper-reflection/PROOF.md)
replaces d>=0 and V>=1 by the single affine bound v255>=4. An explicit
five-coordinate involution preserves all446 body residuals up to sign and
fixes every semantic/frame/power port. It restores the two old signs before
the matching F-only or joint theorem is applied. This is an existential
normalization of private witnesses, not a fixed-whole-body guard deletion.

Both fresh root normal/optimized receipts exactly match the author: all446
row identities,the full body-SOS identity,522 coordinate involutions,all38
old graphs/privacy and18 actual corruption controls pass. The complete
ordinary packet is sealed; see the
[root acceptance](reviews/round15-helper-reflection-root-peer.md). A separate
materialization is required for any projected count. The accepted436 quartic,
cap prototype's initial helper policy and canonical PDF/TeX remain preserved.


## Signed-cap literal source accepted

The [complete emitted source](research/signed-pell-cap-source/README.md) now
matches the reviewed15-target/18-call cap design. All four complete JSON
artifacts, every removed/private/retained row and guard map, the even frame,
full cap anchor and joint residue are checked. Root independently replayed
both checker and both byte-exact rebuild modes; all four receipts exactly
match the author. Each checker rejects12 actual corruptions and verifies178
retained sign identities,all42 required front targets,15 positive original
index bounds,18 unsquared power congruences and five shared moduli.

The [root acceptance](reviews/signed-pell-cap-source-root-peer.md) composes
those exact interfaces with the complete ordinary soundness/completeness
proof at the unchanged semantic front. Old doubled Pell witnesses are rebuilt
freshly. The closed21-file payload is sealed, retaining F/V/d and the existing
weighted/remainder policies. No factorization, projection, expanded quartic
or new numerical frontier has run here; the finite projection packet is a
separate next step. The436 checkpoint and canonical PDF/TeX are preserved.
Lean stays paused.


## One-word window: mask obstruction and narrower open target

The [complete ordinary review](research/one-word-window-review/REVIEW.md)
proves that alpha=1, and every power-of-two slack, contradicts the retained
native mask population budget before transport is used. The former cyclic
group heuristic does not exclude arbitrary word ties or nonlinear digit
decoding. The [corrected active brief](candidates/ten-positive-scaled-norm/ONE_WORD_WINDOW.md)
now distinguishes those scopes and retains the locally valid selective gap
alpha=(MC AND MF_native)*J-1 as an open compiler target.

Root and independent peer reviewed the full arguments and exact source bytes;
the historical and corrected briefs are preserved in a closed ordinary packet.
See the [root acceptance](reviews/one-word-window-root-peer.md). Transport,
carry/anchor/alignment and a replacement for the independent dummy controller
still require complete proofs. No nine-positive equation, new size bound or
formalization is claimed. The canonical PDF/TeX remain unchanged. Lean stays paused.


## Helper normalization reaches433 integer variables

The [complete centered quartic](research/round15-helper-guard-projections/full-data/joint_helper/centered/equation.json)
has433 integer variables,287 rows,4606 terms and exact degree4, with quartic
height128446 and row height256. It saves3 variables,1 row and18 terms against
the436 parent at unchanged heights. The private-helper inverse may change five
body coordinates before restoring the old signs; the semantic front is fixed.

All author source/full checks and four fresh independent root full checks and
byte-exact rebuilds pass; each collector rejects42 actual corruptions. Root
also checked the entire partial coordinate/row maps,180 matched monic steps,
15 free coordinates and whole calibration bindings. See the
[root acceptance](reviews/round15-helper-guard-projections-root-peer.md).
The plain chart is preserved too, with a14-point quartic-height increase.
Earlier equations and canonical PDF/TeX remain preserved. Lean stays paused.


## Shared Pell cap reaches359 integer variables

The [complete shared-cap quartic](research/signed-pell-cap-projections/data/centered/equation.json)
has359 integer variables,222 rows,6058 terms and exact degree4, with height
128446 and row height256. It removes74 variables and65 rows compared with
the433 helper form, while adding1452 terms. Both forms remain available.

The complete ordinary source theorem now composes with explicit Horn witness
overwrite maps,147 certified monic restorations and the actual free list
[133,135]. Four fresh root collector/rebuild modes and all eight retained
receipt/stdout files exactly match the author; each collector rejects34
actual corruptions. Both whole polynomials, translations, centering and
ordinary/native endpoint bindings pass. See the
[root acceptance](reviews/signed-pell-cap-projections-root-peer.md).
Further cap/guard relaxations remain separate proposals. The compact canonical
PDF/TeX and earlier equations are preserved. Lean stays paused.


## Three further cap simplifications: ordinary proofs accepted

The [unoriented cap theorem](research/signed-pell-cap-unoriented/PROPOSAL.md)
removes the cap lower graph and its pooled error term. A nonzero requested t
excludes the collapsed cap first; signed-center power semantics then recover
the native arithmetic front before fresh positive private witnesses are built.
The [F recovery theorem](research/signed-pell-cap-factorial-output-guard/PROOF.md)
omits F's graph in the current policy by using signed targets and the supported
t pair before its old positivity ledger. The
[current-cap helper involution](research/signed-pell-cap-helper-reflection/PROOF.md)
replaces two helper graphs by one, using four actual private ports.

Root and independent peers reviewed every proof and literal interface; each
ordinary packet is closed. These are separately scoped results. Combining
them requires a fresh source proof, all coordinate/graph maps and independent
checks; no projected count follows by subtraction. The accepted359 quartic,
433 lower-term alternative, canonical PDF/TeX and paused Lean work remain
preserved.


## Ten scalar graphs can share one eight-factor product

The [new current-cap ordinary theorem](research/signed-pell-cap-scalar-product/PROOF.md)
restores ten scalar signs using one strict product of eight nonnegative
factors. Signed-index power analysis first recovers x and the reciprocal
index automatically. Four q-divisible denominator powers are established
before all eleven successor residues, with no premature K/N interpretation.
Only then does the product exclude the remaining eight zero factors.

Root and independent peer reviewed the complete258-line proof and literal
interfaces, including67 source rows,11 whole polynomial ideal combinations
and all30 omitted auxiliary occurrence sets. See the
[root acceptance](reviews/signed-pell-cap-scalar-product-root-peer.md).
Both directions fix the original cap body. F, helper signs and both old cap
policies remain; a future refined-source composition needs a separate proof.
No successor equation or projected saving is claimed. Canonical PDF/TeX and
accepted equations are preserved; Lean stays paused.


## Combined refined cap source accepted

The [complete refined source](research/signed-pell-cap-refined-source/README.md)
now binds the three separately proved cap/F/helper reductions with an explicit
combined chronology. It normalizes the helper first, recovers signed-A target
indices using only absolute bounds and nonzero t, then restores F before
reconstructing fresh positive private witnesses at the unchanged native front.

Four fresh root source collector/rebuild modes exactly match the author;
each collector rejects25 actual corruptions. The full four JSON files, all
graphs/maps/privacy,37 atoms/54 ports,15 norms/18 requests/five moduli and
staged178-identity sign ledger pass. See the
[root acceptance](reviews/signed-pell-cap-refined-source-root-peer.md).
This is a complete ordinary/literal source checkpoint with no new projected
quartic count. The359 and433 alternatives and canonical PDF/TeX remain
preserved. Lean stays paused.


## Partial-sum extension ready for materialization

The [fixed-chart partial-sum theorem](research/signed-pell-cap-pool-grouping/PROPOSAL.md)
and its inert coefficient calculation passed complete root and independent
ordinary/static reviews. Five unrestricted sums uniquely extend each zero
of the accepted centered359 chart, fixing every old coordinate. The exact
row reconstructions and full SOS difference are checked. Two independent
root inert replays match the frozen author records byte-for-byte.

The prospective364-variable/227-row quartic has4574 terms and height128446.
Those are fixed-layout calculations; the complete successor equation is
still pending materialization and independent checks. No optimizer was run
and no survival or global-minimum claim is made. The accepted359 and433
alternatives, canonical PDF/TeX and paused Lean work remain preserved.


## Affine window-gap lemmas reviewed

The [ordinary affine-gap note](research/one-word-window-affine-gap/PROPOSAL.md)
now isolates a bounded transport kernel for gaps whose fixed polynomial
has constant term different from1. It also constructs a different
constant-term-one gap satisfying both local masks, and a separate
large-kernel arithmetic family. Root and independent review accept these
lemmas and their carry-aware limits. Their simultaneous compiler and
controller intersection remains open; no nine-positive equation or
numerical improvement is claimed. Canonical PDF/TeX remain unchanged.


## Scalar-product row-address correction

The new scalar-product note cited two wrong power-row addresses. Its q-base
y+1 and x+1 requests are at old source rows292 and307, respectively;
rows297 and312 belong to different successor-base calls. The intended ports
and ordinary argument are preserved by the [explicit erratum](reviews/signed-pell-cap-scalar-product-row-erratum.md).
Root and [independent review](reviews/signed-pell-cap-scalar-product-row-erratum-peer.md)
checked all18 actual call memberships and both complete lowered requests.
The earlier literal-binding acceptance must be read with this correction.
Frozen packets and delivered equations are preserved; subsequent interfaces
must check the row-to-call membership explicitly.


## Complete grouped quartic:364 variables and4,574 terms

The [delivered grouped equation](research/signed-pell-cap-grouped-quartic/data/equation.json)
and [whole expanded polynomial](research/signed-pell-cap-grouped-quartic/data/expanded_polynomial.json)
now have364 unrestricted integer variables,227 quadratic residuals and
exact degree4, with4,574 terms and height128,446. Five unique unrestricted
sums preserve every old coordinate of the accepted359 chart. The complete
row reconstruction, full SOS difference, whole polynomial under extension,
all seven inherited maps and native calibration pass independent checks.

All five author commands and four fresh root check/rebuild modes pass;
each collector rejects30 actual corruptions and all eight root receipt/stdout
records match exactly. See the [root acceptance](reviews/signed-pell-cap-grouped-quartic-root-peer.md).
The new form removes1,484 terms while adding five variables to the359 form.
It improves the older433/287/4606 alternative by69 variables,60 rows and
32 terms at unchanged heights. The359 form remains the lower-variable
alternative. No optimizer or new source semantics is part of this extension.

This is useful direct-quartic progress, not a significant improvement over
the compact ten-positive page. Canonical equation.pdf and equation.tex stay
preserved under the owner's update policy. Lean remains paused.


## Scalar compression composes with the refined cap source

The [new ordinary composition proof](research/signed-pell-cap-refined-scalar-product/PROOF.md)
now permits the eight-factor replacement at the exact refined source.
Its signed-A, t-only chronology recovers the ten omitted scalar signs,
then restores their graph witnesses on the original unnormalized whole
body. Both directions fix that body, h and every retained witness.

Root and independent review accept the complete proof and literal interface,
including all18 joint call/row/port memberships,168 whole row records and
all367 reflection identities. See the [root acceptance](reviews/signed-pell-cap-refined-scalar-product-root-peer.md).
The earlier row erratum is respected. This is a labelled-policy theorem;
a numeric source and projected equation remain separate work. No numerical
saving is inferred, and canonical PDF/TeX and paused Lean remain preserved.


## Exact cyclic carries and a carry-free compiler obstruction

The [new ordinary one-word note](research/one-word-linear-boolean-window/PROPOSAL.md)
uses the Hilbert Tenth spectral theorem to rule out the specified cofinal
carry-free full-target layout. It also proves exact transport equivalence
to a unique cyclic carry stream in a fixed bounded alphabet, with every
offset collision included. Fixed-period carry schedules retain the same
obstruction; a successful cofinal route needs carry periods unbounded by
a fixed constant.

The [independent root review](reviews/one-word-linear-boolean-window-root-peer.md)
accepts these precise lemmas and local Boolean gate identities. A complete
carry-dependent compiler, fixed coefficients, padding and rank controller
remain open. No nine-positive equation, new numerical frontier or canonical
PDF/TeX update follows. Lean remains paused.


## Affine-square lifts reduce prospective term and coefficient size

The [ordinary affine-square theorem](research/signed-pell-cap-affine-square-lifts/PROPOSAL.md)
uniquely extends the accepted364 chart while fixing every old coordinate.
Root independently checked both complete virtual quartics, every changed
row, full SOS differences and whole-polynomial substitutions. Four lifts
give prospective368/231/4467/98336 (variables/rows/terms/height); six give
370/233/4443/53943, with residual height160 and exact degree4.

See the [root review](reviews/signed-pell-cap-affine-square-lifts-root-peer.md).
These are inert fixed-layout calculations with full coefficient hashes;
a delivered successor remains pending. No optimizer retention or global
minimum is claimed. Accepted equations and canonical PDF/TeX stay preserved,
and Lean stays paused.


## Complete refined-product source accepted

The [literal refined-product source](research/signed-pell-cap-refined-product-source/README.md)
now realizes the complete signed-A scalar-compression theorem. Both maps
fix the original unnormalized399-coordinate body and all retained witnesses.
Seven monic products and one strict graph replace ten scalar graphs.
Its guarded478-coordinate/365-row namespace is a SOURCE count only.

All five author commands and four fresh root source checks/rebuilds pass;
each collector rejects35 actual corruptions, including wrong call-row
memberships. Every whole artifact, map, graph, privacy cut,15norms/18requests/
5moduli/37frame atoms/54ports/11ideals and full calibration pass. See the
[root acceptance](reviews/signed-pell-cap-refined-product-source-root-peer.md).
No optimized quartic count follows yet. Existing359/364 equations, canonical
PDF/TeX and paused Lean work remain preserved.


## Complete refined-product quartic reaches329 integer variables

The [delivered centered equation](research/signed-pell-cap-refined-product-projections/data/centered/equation.json)
and [entire quartic](research/signed-pell-cap-refined-product-projections/data/centered/expanded_polynomial.json)
have329 unrestricted integer variables,216 quadratic rows,5,728 terms and
exact degree4, with height128,446 and residual height256. Against the
complete359 form this saves30 variables, six rows and330 terms at unchanged
heights. The364-variable grouped form retains its lower4,574-term tradeoff.

Both full static reviews, all five author commands and four fresh root
checks/rebuilds pass. Both collectors reject46 actual corruptions; all
eight full root JSON/stdout records match the author byte for byte. The
actual148 monic steps, two free coordinates, Horn private overwrites,
integer translations, every coefficient and complete source calibration
are checked. See the [root acceptance](reviews/signed-pell-cap-refined-product-projections-root-peer.md).
The fixed policy claims no global optimum. Earlier equations and the
canonical92/283 page remain preserved; Lean remains paused.


## A fused ninth factor removes one source guard graph

The [ordinary fused-product theorem](research/signed-pell-cap-nine-factor-fused/PROOF.md)
replaces r0>=0 and P8>=1 by the single quadratic graph
`(r0+1)P8-1=a9²+b9²+c9(c9+1)`, without another product coordinate.
The retained Qy anchors first recover y>=0; all eight other factors are
proved nonnegative before strict fused positivity restores r0 and all signs.
Both maps fix the whole original unnormalized406-coordinate body and
restore TWO fresh old graph triples. The complete ordinary proof,181literal
rows, all graph/privacy/interface maps and all eleven coefficient identities
pass independent and root review. See the
[root acceptance](reviews/signed-pell-cap-nine-factor-fused-root-peer.md).

The475-coordinate/364-row,24-graph namespace is a declared source policy
only. A complete materialized successor and projected size remain pending;
no dimension saving is inferred from source subtraction. The329-variable
equation, canonical compact page and paused Lean work remain preserved.


## Complete fused-nine source accepted

The [literal fused-nine successor](research/signed-pell-cap-nine-factor-source/README.md)
now materializes the one-graph replacement on the complete original body.
All406 body coordinates/all341 residuals are fixed; the guarded source has
475 coordinates,364 quadratic rows and24 whole graphs. Both old triples
are freshly restored before complete parent calibration. These are source
dimensions only; a projected quartic has not yet been measured.

Both full static reviews, all five author commands and four fresh root
checks/rebuilds pass. Both checkers reject46 actual corruptions, and all
eight full root JSON/stdout records match the author byte for byte. Root
reauthenticated all228 external/five core pins and twelve exact closed
inventories. See the [root acceptance](reviews/signed-pell-cap-nine-factor-source-root-peer.md).
The existing329-variable quartic and canonical92-operation/degree283 page
remain preserved. Lean remains paused.


## Complete nine-positive equation fits one page

The [complete comparison PDF](candidates/one-page-saturated9/equation.pdf)
and [standalone TeX](candidates/one-page-saturated9/equation.tex) print the
entire nine-positive433-operation, exact-degree1,628,768 equation and
every fixed constant on one Letter page at9-point mathematics/8-point
seed. The full original722-character recipe reconstructs all four native
payloads and eleven signed fixed leaves, including initializer698.

All40 displayed identities/every464graphnode/all85free-port kernel
coefficients,29actualTeX corruptions and three positive controls pass
in normal/optimized checks. Both pure rebuilds reproduce all five derived
files, and all eight fresh root JSON/stdout records are byte-identical.
Actual PDF text, strict overflow checks and separate root/peer visual
reviews pass. Seven closed histories preserve every failed checkpoint.
See the [root acceptance](reviews/one-page-saturated9-root-peer.md).
This is a variable-count alternative with substantially higher cost and
degree; the canonical ten-positive92/283 PDF/TeX remain preserved. No
new Lean or encoded internal-ZFC proof is claimed. Lean remains paused.


## Two support-pair products replace four scalar graphs

The [ordinary exchange](research/signed-pell-cap-support-pair-products/PROPOSAL.md)
replaces four scalar sign graphs for183/184/191/192 by two directly
quadratic product graphs. The abstract signed-cap argument and positive
t-only request first give L=q^t and Qt1=q^(t+1), without their output
signs. Both weighted sums are then strictly positive, so the product
predicates restore every old sign. Four fresh old triples are restored
on the unchanged original406-coordinate body before full parent calibration.

Root and independent full reviews accept the unbounded proof and exact
whole source/privacy/interfaces; see the [root review](reviews/signed-pell-cap-support-pair-products-root-peer.md).
This note emits no new source or quartic and claims no projected size.
The current complete equations, canonical PDF/TeX and Lean pause remain
preserved. The separate fused-nine projection is still being checked.


## A simpler nine-positive printed front is prepared

The [new standalone TeX draft](candidates/one-page-shared-odd9/equation.tex)
uses the already accepted413-operation, exact-degree1,316,546 endpoint.
It retains the same entire722-character native recipe as the completed
433-operation page, saving20operations and312,222degrees. Both complete
ordinary/data and mathematical-page reviews pass, including the fresh
positive i/j/n witness maps, all four entire raw coefficient payloads,
all85 translated free-port kernel terms and the whole444-node graph.
The [sealed assessment](research/nine-page-lower-frontier-assessment/ASSESSMENT.md)
explains why the405-operation original31 endpoint cannot reuse this tuple.

This is mathematical TeX preparation. New actual-TeX/PDF validation,
rendering fit and independent visual checks remain pending; no413PDF
is claimed. See the [root preparation review](reviews/one-page-shared-odd9-mathematical-preparation-root.md).
The completed433comparison, canonical92/283 page and Lean pause remain
preserved while the separate reviewed toolchain is prepared.


## Complete413-operation nine-positive page accepted

The preferred [nine-positive comparison PDF](candidates/one-page-shared-odd9/equation.pdf)
and [standalone TeX](candidates/one-page-shared-odd9/equation.tex) now print
the entire413-operation, exact-degree1,316,546 equation and every constant
on one Letter page at9-point mathematics/8-point seed. It saves20operations
and312,222degrees against the preserved433comparison at the same entire
original722-character recipe. The first render and all five author commands
pass, with no retry, layout change or overflow warning.

Both normal/optimized actual auditors prove all43interfaces/every444node/
all85free-port kernel terms, reconstruct all four whole payloads/eleven
signed fixed leaves, reject34actual TeX corruptions and accept four
harmless controls. Both pure rebuilds reproduce all five rendering files;
all eight fresh root JSON/stdout records match the author byte for byte.
Both actual PDF visual reviews pass. See the [root acceptance](reviews/one-page-shared-odd9-root-peer.md).
The main ten-positive92/283 PDF/TeX, all predecessors and the Lean pause
remain preserved while newer compact proposals undergo separate review.


## Complete fused-nine quartic reaches327 integer variables

The [complete centered equation](research/signed-pell-cap-nine-factor-projections/data/centered/equation.json)
and [entire quartic](research/signed-pell-cap-nine-factor-projections/data/centered/expanded_polynomial.json)
have327unrestricted integer unknowns,216rows,5,718terms, exact degree4
and height128,446 (residual height256). This saves two unknowns and ten
terms against329 at unchanged rows/heights. Actual retained maps account
for every change: six old guard auxiliaries disappear; the existing p8
and three fresh mixed-graph auxiliaries survive. No other old mapped
retained coordinate is lost. The grouped364/4,574-term alternative stays.

Both full static reviews, all five author commands and four fresh root
checks/rebuilds pass. Both collectors reject54actual corruptions. Every
full root JSON/stdout record is byte-identical to its author counterpart.
All147monic restorations/two actual free coordinates/Horn overwrites,
both integer translations, every coefficient, seven whole baseline charts
and complete native/source calibration are checked. See the [root acceptance](reviews/signed-pell-cap-nine-factor-projections-root-peer.md).
The accepted327equation and all predecessors remain preserved while new
Round16 claims undergo separate review. Canonical92/283 and the Lean pause
remain unchanged.


## Seven new proposal archives: staged compact forms lead the next review

The [closed static intake](research/intake-fd3e384e92/README.md) authenticates
all seven ZIPs from `fd3e384e92`, their 3,294 members and 26 complete supplied
quartic vectors. The [root review](reviews/intake-fd3e384e92-root-peer.md)
independently checks the entire inventories and literal censuses. Data counts
alone do not establish source correctness or equality to a sum of squares.

The leading compact proposals have ten positive unknowns and 84 operations
at degree 436, or 85 operations at degree 328. Both retain all four entire
accepted indexed coefficient payloads. The
[ordinary review](reviews/staged-certificates-compact-ordinary-peer.md)
requires an explicit completeness correction: retain the actual canonical
bound `R>3q` to obtain the positive shifted transport coordinate. The weaker
generic `R>=3` premise does not suffice. The
[static checker review](reviews/staged-certificates-compact-verifier-static-peer.md)
licenses preparation of a separately pinned packet, not execution or endpoint
acceptance. Six omitted placement files are present in the original ZIP;
the incoming tree remains untouched.

The [Round16 review](reviews/round16-shared-caps-ordinary-peer.md) records the
324-variable/208-row/5,808-term proposal and its new source obligations. It
saves three variables against accepted 327 while adding ninety terms. Its
positive representative sum needs a new dependency proof before combining
it with compressed signed guards. The
[SignedFree review](reviews/signed-free-scales-ordinary-peer.md) repairs an
incorrect complete leading form without invalidating its degree-44 witness.

No incoming program was run for this intake. The canonical 92/283 PDF,
complete 413-operation nine-positive page and accepted 327-variable quartic
remain unchanged while the staged 84/85 finite packet and complete page are
prepared. A significant verified improvement will be reflected in the
maintained PDF and TeX, with complete predecessors preserved. Lean remains
paused and the size-reduction goal remains active.


## Doubled product-square equations accepted at84/436 and85/328

The [complete finite packet](research/ten-positive-doubled-product-square/RESULTS.md)
now passes both static reviews, all four released author checks and four
fresh root replays. Every whole root JSON and stdout agrees byte for byte
with the author. The two ten-positive equations use84 operations at exact
degree436 or85 at328, with all four unchanged indexed coefficient payloads.
The repaired ordinary proof explicitly retains canonical `R>3q` for shifted
positive T. The whole source/native interpretation, all actual gates and
full leading forms are bound; see the
[root acceptance](reviews/ten-positive-doubled-product-square-root-peer.md).

Both improve the86/466 comparison in operation count and degree. They save
operations relative to the maintained92/283 page while increasing degree.
The85/328 form is being prepared as a complete-page successor with the same
entire printed constants; no PDF is promoted before its separate formula,
render and visual checks pass. The327-variable quartic is unchanged. Lean
remains paused, and no global optimum or consistency assertion is made.
