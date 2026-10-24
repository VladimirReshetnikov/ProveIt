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
| Positive integers | 9 | 419 / 427 | 1,472,168 / 1,626,248 | Position-zero normalization; original31 / smaller compact54 tuples |
| Positive integers | 9 | **722** | 1,158,228 | Collected original31 radical evaluator plus identical norm rewrite |
| Positive integers | 9 | 953 / 1,056 | 999,518 / 997,810 | Collected radical / position-zero complete radical; cost-degree tradeoff |
| Positive integers | 10 | 123 | 816 | Scaled centered sixteen-fold norm with shared product |
| Positive integers | 11 | **111** | **211** | Adaptive q²Y carrier combined with double center |
| Positive integers | 12 | **96** | **70** | Free positive J and an identical polarized norm tail |
| Positive integers | 13 | **88** | **51** | Free positive J; canonical90/51 page retained |
| Positive integers | 14 | 73 / 74 / 75 / **76** | 342 / 312 / 293 / **191** | Hilbert Tenth root deletion and ordinate centers |
| Integers | 10 | 471 | 1,245,324 | Round12 short guard; full replay and ordinary guard review |
| Integers | 10 | **475 / 478 / 512** | 1,179,788 / 1,114,252 / 1,080,888 | Short guard combined with compact older shears |
| Integers | 16 | 134 / 135 | 192 / 184 | Separated rational norm and nonnegative guard finalizer |
| Integers | 12 | 208 / 202 | 2,400 / 2,912 | Fixed-prime separation with identical shared norms |
| Integers | 13 | 184 | 1,072 | Trace recovery and identical shared-norm evaluator |
| Integers | 14 | 137 / 148 | 792 / 414 | Root fusion and CRT/valuation composition |
| Integers | 15 | 124 / 128 | 352 / 204 | Parity-separated norm;204/128 improves344/131 |
| Integers | 16 | 115 / 118 / 119 / 132 | 160 / 124 / 112 / 108 | Parity/residue families and prime separation |
| Integers | 17 | 110 | 88 | Root-fusion quotient companion;114-gate checkpoint retained |
| Integers | 18 / 19 / 20 | not optimized in coordinate packets | 32 / 28 / 18 | Signed coordinate/quotient reductions |
| Nonnegative integers | 399 | not optimized | 4 | Projected source, summed factorial radix and rational SOS contraction;8,286 terms |
| Nonnegative integers | 402 / 403 / 453 / 667 | not optimized | 4 | Complete term/height alternatives;6,882 /8,229 /5,059 /3,632 terms |
| Integers | 917 | not optimized | 4 | Lower-height projection;6,986 terms, height63,906,036 |
| Integers | 888 | not optimized | 4 | Guarded signed projection;10,156 terms, height2,445,790,974,704 |
| Integers | 1,190 / 1,224 | not optimized | 4 | Preserved synchronized checkpoints, now dominated by917 |

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
circuit improvements leave the canonical13-positive90/51 PDF unchanged.

The ten-positive124-operation degree816 candidate from8380e70262 now
[passes ordinary and full replay review](reviews/ten-positive-scaled-norm-peer.md).
The [complete shared-product sibling](candidates/ten-positive-scaled-norm-shared/README.md)
saves one more operation, reaching123/816 by an exact identity. A complete
alternate one-page rendering is being prepared; the canonical13-positive
90/51 page retains its lower-degree/fewer-operation tradeoff.


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
