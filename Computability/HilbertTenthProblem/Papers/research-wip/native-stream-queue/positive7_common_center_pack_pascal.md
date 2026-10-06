# Sharing the common center across positive7 relator pack lanes

For every fixed integer r>=1, the current shared-decoder compiler admits
an exact local replacement that removes the2r separately materialized
center additions. The simplest schedule adds1M and removes rA overall,
saving r-1 total operations. A second schedule collects the entire center
contribution at a later high-left boundary. Its difference from the parent is

    +(4-eta)M+(4-eta-2r)A,                             (1)

so it saves2r-8+2eta operations, where eta=1 exactly when the binary
expansion of m=8+2r begins100, and eta=0 otherwise. Both schedules pay
every extra product, sum and join. The better displayed saving is

    max(r-1, 2r-8+2eta).                               (2)

This is a handwritten local proof and ledger, not a new complete source.
It preserves the entire packed polynomial for every integer assignment,
and hence preserves the parent's entire final polynomial when correctly
composed. It changes neither the guard nor the positive semantic forms.
No count of any frozen source is reassigned. Root proposed collecting the
common center; the author derived the division-free shifted correction
and its insertion before the two six-field pairs.

## 1. The paid cut and its actual consumers

Use the parent's canonical SAME-V fixed recipe, its five-addition shared
decoder c=C*(H4,H5,H6,H7)^T, and each relator's signed linear forms

    L_(j,1)=u_(j,1)*c1+u_(j,2)*c2,
    L_(j,2)=v_(j,1)*c1+v_(j,2)*c2+v_(j,3)*c3.

Their already charged dot products cost5M3A per relator. The old
producer appends A_(j,i)=L_(j,i)+W for i=1,2, where the common
W=lambda*D*J is already paid outside the cut. These two additions make
the old form stage5M5A per relator. Every coefficient product, including
zero and unit products, stays present in the new schedules.

The full independent source companion found exactly these external
arithmetic consumers, for every j:

* centered_form_j_1 occurs in left_form_pair_j;
* centered_form_j_2 occurs in left_form_shift_j.

In the source grammar L_(j,1) is decoded_u_sum_j and L_(j,2) is
decoded_v_sum_j. Both exist before the two center additions. The
centered forms also describe the native lanes in metadata; that semantic
use must be preserved even when their executable registers are removed.

Write P for the runtime lane base, Pn=P^n, and
R_n(P)=1+P+...+P^(n-1). The retained support cut already supplies

    P, P2, P4, P7, P12, P28, R2, R7, Pm, Rm,
    U4=1+P2, U6=1+P6, G7=(1+P7)(1+P14).

Here m=8+2r. The possible power aliases change register names, not these
paid values. This note uses no uncharged power or geometric sum.

The unchanged high-left producer starts at T0=D*P+S and descends through
j=r,...,1, with the four-lane relator recurrence

    pair=A_(j,1)+P*A_(j,2);
    acc=P4*acc+U4*pair.                                (3)

It next appends four copies of the same seven-history block B7,

    acc=P28*acc+G7*B7,                                 (4)

then the two six-field pairs, first B6b and then B6a:

    acc=P12*acc+U6*B6b;
    acc=P12*acc+U6*B6a.                                (5)

Their actual six-field contents and all producers remain unchanged.
Finally the original selector-prefix join uses Pm and its shared selector
word. Neither the right pack nor the selected-output pack is changed.

## 2. Uniform quartet sharing

Prepare once

    H=R2*W                                             (6)

at1M. Delete the2r rows A_(j,i)=L_(j,i)+W, retain the dot products,
and replace the pair in(3) by

    pair=L_(j,1)+P*L_(j,2)+H.                          (7)

This uses one additional A per relator relative to the old pair producer.
Since H=(1+P)W, expression(7) is exactly A_(j,1)+P*A_(j,2).
Every following accumulator is therefore identical to its parent value.
The net difference is+1M-rA, proving the saving r-1. At r=1 this is
a total-cost tie, exchanging one addition for one multiplication; no
strict r=1 improvement is claimed.

## 3. Collecting all centers at one existing boundary

Instead use the uncentered pair L_(j,1)+P*L_(j,2) in every relator
quartet, with no extra per-relator row. Let acc0 denote this uncentered
accumulator. The omitted polynomial after all r quartets is

    W*R4*(1+P4+...+P^(4r-4))=W*R_(4r).                (8)

Equation(4) multiplies this difference by P28. Thus immediately after
the four seven-field blocks, the exact correction is W*P28*R_(4r).
Adding it there restores the parent accumulator before either line(5).
The two six-field pairs would subsequently multiply an uncorrected
difference by P24; placing the correction before them accounts for that
shift without paying any new power.

The useful division-free identity is

    (Pm+P8)*(Rm-R8)=P16*R_(4r).                        (9)

Indeed m-8=2r, Rm-R8=P8*R_(2r), and
Pm+P8=P8*(1+P^(2r)); multiply and use
R_(2r)*(1+P^(2r))=R_(4r). This is an identity in Z[P], valid also
at P=0,1 and negative P. There is no geometric-series division.
Since P12*P16=P28, the following fully paid eight-row schedule supplies
and inserts precisely the correction:

    P8=P7*P;                  R8=R7+P7;
    plus=Pm+P8;               difference=Rm-R8;
    t1=W*P12;                 t2=t1*plus;
    correction=t2*difference;
    restored=acc0+correction.                           (10)

The last row is placed just after left_seven_high_join. Its result
replaces that value in left_six_high_shift_b. Thereafter the parent
accumulator, all pack joins and all later consumers agree exactly.
Schedule(10) costs4M4A, including both new support values and the final
join. Relative to the parent, only the2r center additions disappear and
these eight rows are added: +4M+(4-2r)A, saving2r-8 total operations.

### Exact optional support aliases

The parent's retained geometric extension starts with seed6 or7 when
binary m begins110 or111, respectively, otherwise seed2 on its leading10.
At each subsequent bit it produces P_(2n), R_(2n), and, for a1 bit,
P_(2n+1), R_(2n+1). Consequently P8 and R8 are both already paid
exactly when binary m begins100. To reach8 the seed must be2, its first
post-seed bit must produce4 without the odd append5, and a further bit
must double4 to8. Later prefixes strictly increase; the6/7 branches
cannot reach8. In the domain m>=10 even, leading100 has the requisite
further bit automatically (the first case is m=16).

In that case use geom_P8 and geom_R8 instead of the first two rows(10).
They precede this correction and are already live in the geometric
extension. This gives(4-eta)M+(4-eta)A and proves(1). This alias is
distinct from the power/factor aliases already reviewed in Aristotle's
note; no operation is credited twice. No other unproved sharing is used.

## 4. Ledger choice, positivity and whole-polynomial scope

The first schedule is cheapest among these displayed choices for
1<=r<=7 (ties may occur); the collected schedule is strictly cheaper
for r>=8. In the small range, eta=1 only at r=4,5; at r=5 both schedules
save4 total operations. The exact examples r=1,2,4 therefore save0,1,3
operations, respectively, using the uniform schedule. At r=8 the
collected schedule saves8; at r=12 it saves18 because m=32 begins100.
These are handwritten substitutions in(1)-(2), not source evaluations.
The r=0 fallback remains separate and receives neither schedule.

The guard still uses ell=V*C, not just the sparse V entries. W, lambda,
Cg, K, every action coefficient, the canonical V, the same supplied
ordinary input,96+6r positive witnesses and23 comparisons are unchanged.
Neither new schedule claims that L_(j,i), acc0 or difference is a
positive native port. At a full zero the old guarded semantic expressions
A_(j,i)=L_(j,i)+W remain positive and satisfy the original lane bounds.

More directly, each replacement preserves the complete left packed
polynomial on every integer tuple with the inherited linked fixed recipe.
All other native inputs, all residuals and the final sum of squares are
therefore the same polynomials. Positive zero tuples and ordinary-input
projection are unchanged, without a new witness map, program encoding,
native soundness lemma or carry argument. A future source must actually
implement the described consumer substitutions for this inference to apply.

It must also replace references to deleted executable form names in
computed-port/lane metadata by explicitly semantic expressions L+W and
references to the existing L and W producers. It must not relabel L as a
positive formed lane or claim that an uncomputed A register still exists.
The dot products, shared decoder and W remain executable and live.
Any aliased P12, U4 or other support name must be resolved consistently.
No runtime branch, new fixed role, or new witness is introduced.

## 5. Retained boundaries and earlier valid schedules

**Remark 1 (deleting the center is not itself an identity).** Dropping
the2r center additions without either correction changes the final high
word by W*P52*R_(4r). For the local integer cut r=1,P=2,W=1 this is
15*2^52, not zero. This is a polynomial counterexample, not a claimed
full positive compiler zero. Semantic forms cannot simply be replaced
by L in the native theorem.

**Remark 2 (no free geometric quotient).** The equation
P16*R_(4r)=R_(2m)-R16 does not make division by P16 a free allowed
arithmetic operation. In particular at P=0 it is not even a numerical
quotient. Moving the correction to the stated lower-block boundary and
using(9) supplies the required integer polynomial with charged products.

**Remark 3 (retained valid preliminary schedules).** An earlier placement
after all52 paired lanes used W*P36*(R_(2m)-R16): P36 from P12 costs2M,
R16=R2+P2*R7*(1+P7) costs2M1A, and R_(2m)=Rm*(1+Pm) costs1M1A.
The difference, two remaining products and final join give7M4A overall.
Factoring the same expression as W*P36*(Pm+P8)*(Rm-R8) gives6M4A.
Both identities and ledgers are valid but weaker than(10). They were
preliminary handwritten suggestions, never complete emitted sources.

**Remark 4 (fixed-role operation types).** The frozen shared-decoder
primary's sentence “Each role occurs in one paid multiplication” is
false for the global gamma role, whose unique paid occurrence is the
program_tau addition. Riemann's independent source companion retains
that correction and his first failed overstrong audit. These schedules
leave all6+15r roles unchanged:5+15r occur in multiplications and gamma
in one addition. Every new sparse basis role remains a paid product.

**Open question 1 (complete composition, credited to root).** Emit and
independently audit one of these schedules in a complete source, including
all-r grammar, deleted producer fanout, semantic lane metadata, support
aliases, finalizer and liveness. Only that successor may claim a complete
new operation count. Numerical universal relators, source degree, further
sharing and optimality remain open. Formula(2) compares only the two
displayed choices; it is not an arithmetic lower bound.

## 6. Evidence and review boundary

The complete shared-decoder primary and composer, the complete local
decoder and high-left proofs, and Riemann's complete frozen source review
were read as inert text. The actual geometric and high-left producer
grammars were reread in the preceding frozen emitters. No source or
coefficient array was evaluated and no degree was propagated. The source
review supplies the independently audited sole-consumer statement; the
new argument and all new counts are handwritten. The metadata companion
binds exact bytes and read spans, not numerical experiments.

Aristotle independently read the full242-line mathematical draft and
passed every identity, paid ledger, alias condition and semantic boundary,
requesting no correction. Root also read all242 lines and independently
passed the omitted-center factors, insertion point, all counts and
scope statements with no correction. Only this final review/status
provenance changed afterward. This proof and its metadata are frozen.
No supplied,
archived, committed, predecessor or frozen helper was executed/imported.
No scientific sampling, emitter, build, repository edit or Git mutation
was performed. New files are confined to/tmp.
