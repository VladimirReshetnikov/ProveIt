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
| Positive integers | 9 | 409 / 417 | 1,191,572 / 1,316,548 | Tight main folding and unshifted carrier; original31 / smaller compact54 tuples |
| Positive integers | 9 | **722** | 1,158,228 | Collected original31 radical evaluator plus identical norm rewrite |
| Positive integers | 9 | 953 / 1,056 | 999,518 / 997,810 | Collected radical / position-zero complete radical; cost-degree tradeoff |
| Positive integers | 10 | 103 | 408 | Direct positive J, symmetric norm and quadratic main-Pell projection |
| Positive integers | 11 | **111** | **211** | Adaptive q²Y carrier combined with double center |
| Positive integers | 12 | **96** | **70** | Free positive J and an identical polarized norm tail |
| Positive integers | 13 | **88** | **51** | Free positive J; previous90/51 page retained |
| Positive integers | 14 | 73 / 74 / 75 / **76** | 342 / 312 / 293 / **191** | Hilbert Tenth root deletion and ordinate centers |
| Integers | 10 | 471 | 1,245,324 | Round12 short guard; full replay and ordinary guard review |
| Integers | 10 | **475 / 478 / 512** | 1,179,788 / 1,114,252 / 1,080,888 | Short guard combined with compact older shears |
| Integers | 16 | 134 / 135 | 192 / 184 | Separated rational norm and nonnegative guard finalizer |
| Integers | 12 | 145 / 141 | 1,200 / 1,456 | Scalar intersective carrier, main folding and four-root prime separation |
| Integers | 13 | 135 | 536 | Trace before signs, main-root folding and quadratic projection |
| Integers | 14 | 119 | 312 | Signed main-root recovery, quadratic projection and identical shared prefix |
| Integers | 15 | 124 / 128 | 352 / 204 | Parity-separated norm;204/128 improves344/131 |
| Integers | 16 | 115 / 118 / 119 / 132 | 160 / 124 / 112 / 108 | Parity/residue families and prime separation |
| Integers | 17 | 110 | 88 | Root-fusion quotient companion;114-gate checkpoint retained |
| Integers | 18 / 19 / 20 | not optimized in coordinate packets | 32 / 28 / 18 | Signed coordinate/quotient reductions |
| Nonnegative integers | 399 | not optimized | 4 | Projected source, summed factorial radix and rational SOS contraction;8,286 terms |
| Nonnegative integers | 402 / 403 / 453 / 667 | not optimized | 4 | Complete term/height alternatives;6,882 /8,229 /5,059 /3,632 terms |
| Integers | 708 | not optimized | 4 | Mixed-domain lower-height projection;5,887 terms, height63,905,891 |
| Integers | 1,559 / 912 | not optimized | 4 | Retained-wire mixed guards;5,289 /4,134 terms, heights427 /4,750 |
| Integers | 767 / 703 / 689 | not optimized | 4 | Retained-wire mixed projections;5,897 /9,247 /9,211 terms, heights737,653 /737,653 /938,261 |
| Integers | 679 / 680 / 682 | not optimized | 4 | Signed comparisons, derived guards and private sign orbits;10,335 /8,999 /8,904 terms, height2,445,790,974,704 |
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
checked10-positive105-operation degree408 equation. The full fixed-constant
recipe remains verbatim from the preceding ten-positive page, including
the436-character seed, corrected initializer and943 typed tiles. Separate
peers checked uniform native/controller rebinding and independently rebuilt
all four coefficient integers in both Python modes. The new quadratic
projection has complete ordinary positive witness maps; its symmetric
norm is a universal identity. The complete free-port
front matches all105 literal gates, and the one-page9-point layout was
visually inspected. [CURRENT_EQUATION.json](CURRENT_EQUATION.json) records
the exact displayed hashes and preserves both earlier page links.
Halved degree and18 fewer operations at the same ten-variable count is
the selected improvement. No global minimum or completed Lean/
internal-ZFC theorem is implied by this display choice.


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
The current10-positive105/408 PDF and TeX are unchanged by this minor
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
more variables and operations than the current10-positive105/408 page,
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
both current13-integer cost and degree. The10-positive105/408 page remains
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
