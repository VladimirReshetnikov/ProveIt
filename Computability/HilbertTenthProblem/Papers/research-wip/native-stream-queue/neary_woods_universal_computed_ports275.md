# Compute the three joined-AND fields: a275-operation U9 polynomial

The [factored-port successor](neary_woods_universal_factored_ports269.md)
gives269 operations at the same degree bound3853 and43 witnesses. It
saves six additions by exact polynomial identities, with unchanged
supplied coordinates and positive domain; this275 packet remains reproducible.

The explicit U9 universal construction now costs **275=136M+139A**, with
**261=131M+130A certificate operations**, **five comparisons**,
**43 positive existential witnesses**, four positive program parameters
and degree **at most3853**. Three formerly supplied AND truth fields can
be computed from already-paid ports. The retained history and recoder
bounds prove their positivity before any native typing. The checksum
then becomes identically1 and its product multiplication disappears.

The [source](neary_woods_universal_computed_ports275.py) and
[receipt](neary_woods_universal_computed_ports275.json) transform the
literal [duration-floor282 family](neary_woods_universal_duration_floor282.md).
An intermediate computing only the first field costs279, with45
witnesses and degree at most3980. Computing both input fields costs276,
with44 witnesses and degree at most3902. These two intermediate maps are
positive-zero graph bijections. Computing all three fields preserves
the accepted outer relation; its converse first uses the parent's
existing private checksum normalization when necessary.

The unchanged fixed U9 table, numeral recipes, ordinary input, valid
program slices and exact counter initialization remain those of the
parent. The separate75-operation certificate and87-operation universal
polynomial are unchanged.

## 1. Literal ports and the retained equations used here

Distinguish the recoder input scale q0 from the joined native scale q.
Let ell denote `program_duration_bound`, h denote `quotient_hat`, and
g denote `fusion_output_slack`. All supplied coordinates are positive.
The unchanged282 source has

    q0=x+ell+input_slack,
    rload=q0+z+power_gap,
    Q=(2^D-1)rload+1, B=2^(D-1)Q,
    ell<B-1,
    J=(B-1)duration_quotient+ell,
    P=(B-1)J+1, S=q0P, copies=xJ,
    K=h+g,
    Ahat=(Q-1)(h-1)+z+1.                         (1)

Here D is the parent's actual fixed positive U9 width, which is at
least3. The strict bound on ell follows from these positive formulas
as proved by282; it is not an additional comparison. In particular
q0>x, J>0 and J<P. The retained mask comparison is

    S=(2B-1)K+1.                                  (2)

Write L=16BS for the paid low-block scale. The four low values in the
literal joined source are

    A_lo=16B*copies+16ell+12,
    B_lo=16BK+16ell-6,
    Z_lo=16B(Ahat-1)+8,
    L=16BS.                                        (3)

For the history write h0 for `hist__height_sum__2`, b for
`hist__B__3`, j for `hist__J__7`, and p for `hist__P__10`. The actual
height is a sum of four positive terms, so h0>=4. Its fixed positive
radix gives b>=h0. The four selector hats define

    S_i=Shat_i-1>=0, j=sum_i S_i>=0,
    p=(b-1)j+1.

The retained history global comparison is exactly

    H_U+H_V+ZUhat0+ZVhat0+ZVhat1+global_bound=p.     (4)

There are six positive terms, so p>=6. Hence j>=1, b<=p, each selector
S_i<=j<=p-1, and each of H_U,H_V and the three output hats is less
than p. None of this uses a native equation, a power-of-two conclusion,
one-hot selection or a chronological history interpretation.

The source reconstructs the selected frozen282 parent and checks its
entire source, comparison list, positive domains, factor partition and
public interfaces. Thus(1)--(4), all fixed numeral roles and the joined
packing rows below are guarded as actual source, not caller promises.

## 2. Three strict margins before native typing

First, the low values satisfy

    0<A_lo<L, 0<B_lo<L, 0<Z_lo<L.                  (5)

Indeed ell<B-1 and copies<S give

    A_lo<16B(copies+1)<=16BS=L.

Equation(2) gives K+1<=S, so similarly B_lo<16B(K+1)<=L;
its explicit formula is positive. For the low output, Q-1>z+1 follows
from(1). Since h>=1 and K>h,

    1<=Ahat<(Q-1)h<Bh<BK<S.

This proves the remaining part of(5). In particular this use of the
projected Ahat does not presume that it is an AND output.

For the high words, put

    C=sum_(i=0)^3 S_i p^i,
    M_C=j(1+p+p^2+p^3),
    H_R=H_U+pH_V,
    M_R=(h0-1)j(p+1),
    H_b=H_U+pH_V+p^2H_V,
    Z_b=(ZUhat0-1)+p(ZVhat0-1)+p^2(ZVhat1-1),
    M_b=(b-1)((S_1+S_2)+pS_0+p^2S_1).

These are the actual three selected-product lanes of the frozen source,
including its grouped slope selector. Its joined words are

    H_h=H_b+p^3C+p^7H_R+b p^9,
    M_h=M_b+p^3M_C+p^7M_R+(b-1)p^9,
    Z_h=Z_b+p^3C+p^7H_R,
    T=p^11.                                        (6)

Equation(4) and the selector definitions give, as ordinary integer
inequalities,

    0<=Z_b<p^3, 0<H_b<p^3, 0<H_R<p^2,
    M_C-C=sum_i(j-S_i)p^i>=0,
    0<=M_b<=p^3-1,
    0<=M_C<=p^4-1, 0<=M_R<=p^2-1.                 (7)

For M_b, each selected group is at most j, so multiplying a lane by
b-1 gives at most(b-1)j=p-1. For M_R, use h0<=b and
(b-1)j=p-1. No digitwise Boolean assertion is involved.

The identical controller/range portions of H_h and Z_h cancel exactly:

    H_h-Z_h=b p^9+H_b-Z_b>=1.                     (8)

Also M_b,M_R and M_C-C are nonnegative. Since H_R<=p^2-1 and
Z_b<=p^3-1,

    M_h-Z_h >=(b-2)p^9+p^7-p^3+1>1,               (9)

where b>=4 and p>=6 suffice. Finally(7) telescopes through the actual
lane positions to give

    M_h <=(p^3-1)+(p^7-p^3)+(p^9-p^7)+(p^10-p^9)
         =p^10-1,
    H_h-Z_h<=p^10+p^3-1.

Consequently

    T-H_h-M_h+Z_h >=p^11-2p^10-p^3+2>=2.          (10)

All three margins(8)--(10) follow from positive supplied coordinates
and the two retained outer comparisons(2),(4), before native typing.

The padded joined ports and scale are

    A=A_lo+L H_h, Bp=B_lo+L M_h,
    Zp=Z_lo+L Z_h, q=LT.                            (11)

Combining(5),(8)--(10), the following three computed values are
strictly positive:

    F1=A-Zp,
    F2=Bp-Zp,
    F0=q-A-F2-1=q-1-A-Bp+Zp.                       (12)

For example F1>=A_lo+L-Z_lo>0, and the same argument proves F2>0.
For F0, the integer bounds A_lo,B_lo<=L-1 give

    F0>=2L-A_lo-B_lo+Z_lo-1>=Z_lo+1>0.

Thus the reserved high history lanes provide all three required
positivity margins. No extension of a Pell rank theorem to a signed
truth field is needed for this packet.

## 3. Literal substitutions and exact full-output identities

Mode A replaces the one addition

    input_A=F1+F3

by the one subtraction F1=padded_A-F3, removes the supplied F1 and its
port comparison, and aliases every old input_A consumer to padded_A.
Mode AB additionally makes the corresponding substitution
F2=padded_B-F3. The certificate cost stays unchanged in both cases.
Equation(12) proves that the newly computed coordinates are positive
at every new zero: any zero of the grouped finalizer first makes the
retained outer comparisons(2),(4) hold. For an anchored finalizer this
uses the integer identity

    anchor_product*(1+sum residual^2)=1,

which forces the sum to be0 and the anchor to be1. For an all-SOS
finalizer the conclusion is immediate.

For mode all, retain both substitutions and replace the checksum's
three additions/subtractions

    shared_sum02=F0+F2,
    bs_Q=shared_sum02+input_A,
    checksum=q-bs_Q

by exactly three subtractions

    remaining=q-padded_A,
    before_one=remaining-F2,
    F0=before_one-1.

The checksum is now identically1. Substituting this numeral into each
literal group product removes its private multiplication by1. A
singleton checksum group would instead remove the trivial1=1 comparison;
if it were the anchor, the finalizer becomes the ordinary SOS. The
actual twelve selected parent schedules all put the checksum in a
larger group, so each loses exactly one certificate multiplication.
No emitted multiplication by a fixed nonunit numeral is free.

For all three modes and every integer assignment, adding the fields
from(12) to the supplied tuple gives the exact full-polynomial identity

    F_new(v)=F_parent(Phi(v)).                       (13)

Every retained residual and every unspecialized unit factor agrees.
The removed port residuals are identically zero, and in mode all the
old checksum is identically1. This is an ordinary polynomial identity,
including signed assignments. Phi need not be positive off zero.

Modes A and AB are graph bijections on the complete positive zero sets:
the parent port comparisons recover precisely the erased coordinates,
and(12) proves positivity in the forward direction.

Mode all is a graph bijection onto the parent positive zeros with
checksum+1. It is not claimed to preserve every parent zero on the same
supplied tuple. The next section supplies the remaining converse.

## 4. Complete positive converse for every selected group schedule

The [coupled two-core theorem](neary_woods_universal_joint_and_coupled.md),
Sections2--5, already proves at every parent positive zero that all norm
and linear factors are+1, the geometry index factor is+1, and the joint
checksum and joint index factors have the same sign epsilon. This
statement applies to all selected grouped schedules: their zero implies
the original total unit product is1, and the same sign proof applies.

If epsilon=1, every factor is+1 and the erased fields already equal(12).
Simply project them out. If epsilon=-1, use the parent's established
normalization

    F0_old -> F0_old-2>0,
    bound_beta -> bound_beta+2>0.                  (14)

Its hypotheses, private-consumer guards and full strong equations are
unchanged here. The joint packed integer drops by2, while its positive
X scale, every outer port, every geometry quantity and every ordinary
input/program/history coordinate remain fixed. The checksum and joint
index both become+1; all other factors remain+1. Hence every original
group product is now1, irrespective of the partition. The resulting
tuple is a parent positive zero with checksum+1, to which the graph
projection applies. No fresh auxiliary rank lemma or new Pell extension
is used.

This proves complete accepted-outer equivalence between mode all and
each selected282 parent. Soundness is the positive lift(12),(13).
Completeness either projects directly or first applies(14). The effective
valid program tuple and ordinary input are unchanged. The parent's
leading-zero-padding theorem and exact synchronized counter therefore
give the same universal relation with43 positive witnesses in the
default schedule. Arbitrary invalid program parameters are not promoted
to a new universality claim.

The API's ordinary `project_from_parent` only erases computed fields.
Its optional `normalize_negative_checksum=True` implements(14) before
erasing fields when the retained sign conditions hold; its mathematical
use is on complete parent zeros. Historical parent packets are preserved,
and `lift_to_parent` restores the immediate selected282 tuple before any
earlier coordinate helper is applied.

## 5. Actual counts, degrees and finite-family scope

For the default selected parent the literal ledgers are:

| Computed fields | Certificate | Comparisons | Witnesses | Polynomial | Degree bound |
|---|---:|---:|---:|---:|---:|
|F1|262=132M+130A|6|45|279=138M+141A|3980|
|F1,F2|262=132M+130A|5|44|276=137M+139A|3902|
|F0,F1,F2|261=131M+130A|5|43|275=136M+139A|3853|

Both program-bound interfaces are supported. Witness counts exclude the
ordinary input and program parameters. All the original fixed numeral
multiplications, including the enormous fixed data width's two paid
loader roles, remain in the actual source.

The complete all-fields images of the eleven selected parent frontier
points have the following costs; their receipt contains literal DAGs.

| Polynomial operations | Degree upper bound | Positive witnesses |
|---:|---:|---:|
|275|3853|43|
|276|3437|43|
|277|3391|43|
|278|2273|44|
|279|1505|44|
|280|1459|44|
|281|1142|44|
|282|1098|44|
|283|764|44|
|284|734|44|
|285|608|44|

The separate fixed43-witness image costs282 with degree at most1344,
256 certificate gates and nine comparisons. These are the transformed
twelve selected parent schedules. This packet does not rerun the full
partition search after the substitutions, and claims neither a global
optimum nor an exhaustive frontier over unselected schedules.

Degrees are propagated through the new literal definitions. Both native
main-norm cancellations retain their exact guarded polynomial identities.
No zero-set equation lowers an off-zero degree. For the default parent,
the unit-degree bound is3892 and the largest remaining port residual
degree is44, giving3980. Removing both ports leaves maximum residual
degree5, giving3902. The checksum factor has degree49; specializing it
to1 reduces the unit bound to3843, giving3853. The computed fields do
not increase the packed integer's dominant degree or the other factor
bounds. Every displayed degree is a conservative upper bound.

## 6. Reproducible checks

```sh
python3 neary_woods_universal_computed_ports275.py
```

The checker emits72 ledgers: twelve parent choices, both program-bound
interfaces and all three modes. It checks2,304 full-source, factor and
complete-output identities, including1,152 signed assignments, with
2,304 coordinate round trips. Explicit positive off-zero assignments
give a negative computed field, retaining the distinction between
integer identity(13) and positive-zero equivalence.

Another249 positive outer fixtures satisfy exactly the retained mask
and global-bound comparisons and verify all three computed-field
margins. Of these,203 use a non-dyadic recoder input base. They test
untyped scalar bounds, not full native Pell zeros or valid chronological
histories. Seven incompatible-parent cases exercise the strict producer,
comparison, domain and nested-public-export guards. Every emitted gate
reaches its chosen complete output.

Author receipt generation and a fresh default replay pass. The root's
independent full proof/source review and fresh replay also pass without
findings. That review checked all three pretyping margins, the exact
selected lane order, checksum normalization and accepted-outer scope.
Its additional2,048 abstract necessary-domain margin checks pass; these
are not full-source identities or full native Pell zeros. All four local
links resolve.
An independent propagation through all72 literal sources, expanding the
exact main-norm cancellation rather than calling the ledger helper,
also confirms every degree bound, opcode count and unique witness count.

A second independent full proof/source/fresh-default review passes
without findings. Its own executor and manual coordinate lift checked
288 complete parent-finalizer identities across24 contexts and all three
modes on both interfaces:144 signed assignments and144 positive ones,
including24 positive off-zero tuples with negative computed fields.
Separately,512 untyped history assignments combined with32 independently
assembled recoder ports give16,384 positive field reconstructions. All72
opcode ledgers pass. These are algebraic and component fixtures, not
numerical full Pell zeros.

A third independent full proof/source/fresh-checker review found no
mathematical, count, degree or scope issue. Its own literal executor and
manual field lifts checked288 complete retained-source, factor and
output identities,144 signed, across all72 configurations. That review
identified one stale group-product metadata alias after checksum
specialization. The alias list is now remapped and aligned with the
surviving partition; each sampled assignment additionally verifies that
every named group value equals the direct product of its listed unit
factors. The root independently reviewed this correction. No arithmetic
schedule or receipt content changed.
