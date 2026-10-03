# A paid mask tradeoff for the nonempty Nielsen benchmark

The actual Nielsen source from [inverse macro sharing](group_projective_inverse_macro_sharing.md) admits two complete successors:

| Current source | Certificate | Full polynomial | Positive witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|
| Unit top mask, reused32-lane range |353=143M+210A|**370=149M+221A**|54|6|4909|
| Unit top mask, separate8-lane range |354=144M+210A|**371=150M+221A**|54|6|3517|

Both represent the same proper, nonempty ordinary-input predicate as the frozen Nielsen source. The historical predecessor costs371=150M+221A at degree4909 with top mask2. Removing that private multiplication saves1M; spending1M on a separate eight-lane range mask lowers the degree to3517. This is a two-source cost/degree comparison, not an optimization census or a numerical universal bound.

The [source](group_projective_nonempty_mask_frontier.py) and [receipt](group_projective_nonempty_mask_frontier.json) read the actual frozen Nielsen array and authenticate the [unit-top-mask theorem](group_projective_unit_top_mask.md) and required inherited sources/proofs. They import no historical modules and run no historical builders or suites. Every predecessor remains unchanged.

## 1. Literal source changes and the paid extra product

The parent uses28 nonidle Nielsen edges,25 states and32 controller lanes. Its exact physical macro table is

    R=(2,3,6,7), U=(1,5),
    (R, U^5, inverse(R), inverse(U^5)).

Its ordinary input and height remain `u=24x+13`, `D=u+height_slack`, `B=16D`; all supplied coordinates are positive integers. The graph, lane assignment, edge hats, history fields, selected-source hats, native coordinates, comparisons and full finalizer are retained literally.

Both successors delete the private row

    range_Bminus_shift = 2*range_body_scale

and change its sole consumer to

    range_M = range_Mbody + range_body_scale.

This is the already proved unit-top-mask operation. No new coordinate or restoration arithmetic is introduced.

Let `R_k(P)=1+P+...+P^(k−1)`, and recall that `P=(B−1)J+1` is computed. The reused-range source retains

    controller_origin = J*R_32(P),
    T = P^40,
    T2 = T*P^32 = P^72.

The separate-range source keeps those controller and T producers, and emits exactly one new multiplication

    range_origin8 = J*R_8(P).

Only the range-mask consumer changes from controller_origin to range_origin8. The source also replaces the right operand of the existing T2 multiplication by the already paid P8, giving

    range_mask = (2D−1)*range_origin8,
    T2 = T*P^8 = P^48.

The actual P8 and R8 producers are already live. There is no previously paid J*R8 product, which the checker verifies from every multiplication row. P32 remains live in T, and R32 remains live in the controller origin. Thus no further private instructions disappear: separate range really costs one additional multiplication. Both whole graphs pass complete liveness and supplied-coordinate closure checks.

## 2. Exact changed scalar interfaces

Write h,m,z for the eight-lane physical packed history, physical selector mask and selected-source word; write C for the28-edge controller word. Let k=32 for reused range and k=8 for separate range. The helper proves these complete scalar polynomials from the actual instructions, over every commutative ring:

    controller_origin = J*R_32(P),
    T=P^40, T2=P^(40+k),
    range_mask=(2D−1)*J*R_k(P),
    H=h+P^8*C+T*h+B*T2,
    M=m+P^8*J*R_32(P)+T*range_mask+T2,
    Z=z+P^8*C+T*h,
    q=32*B*T2.

For separate range it also proves the complete J*R8 polynomial. It then compares every retained register and the whole output after substituting the proved changed range/top-mask ports. All six comparisons and all seventeen finalizer instructions are checked literally. This is an exact source-interface proof, not a same-tuple equality of the old and new full polynomials.

For reused range the only changed native unit is the index unit. If T2 denotes the unchanged paid power in that form, the exact same-coordinate correction is

    index_new−index_old = 16*T2*(q^2−1),
    F_new−F_old = 16*T2*(q^2−1)*U_other*(1+sum_outer_residual_squares),

where U_other is the product of the six retained native/joint factors other than the index unit. The receipt checks this whole correction on complete signed and rational assignments. The general identity follows from the literal folded-index proof in the pinned unit-top-mask theorem. The separate-range form changes q and several native fields, so this particular correction is not asserted for it.

## 3. Positive soundness before typing

At a positive full zero, the unchanged output

    U*(1+R0²+R1²+R2²+R3²+Rflow²)−1

first makes all five outer residuals zero and every individual factor a sign. The joint bound gives P≥12, each history field below P and each selected-source word below P. Nonnegative edge words and the repunit identity then give J≥1 and B≤P. The retained input/height prefix gives B≥608>32 before any native or Boolean interpretation.

For either k, the lower physical and controller blocks remain bounded by P8 and P32 respectively. Each range-mask coefficient `(2D−1)J` is below P. In the reused case its width is32; in the separate case it is8. Consequently in each complete scalar interface,

    H=H0+B*T2, M=M0+T2, Z=Z0,
    0≤H0,M0,Z0<T2.

The smaller P48 scale is therefore sufficient for the separate case; it is not substituted into the old32-lane range without shortening that mask. The unit top coefficient1 gives

    H−Z≥(B−1)T2+1,
    M−Z≥1,
    2B*T2−H−M+Z≥(B−3)T2+2.

Thus the actual four native truth fields are strictly positive, sum to q−1 and retain residues1,4,2,8 modulo16. This establishes the hypotheses of the [tail bootstrap](group_projective_tail_quotient_shift.md) for either paid scale. Its native sign/index recovery remains valid without assuming the old X>r too early. It forces all native and joint factors to1 and types q as dyadic. The literal `q=32B*P^(40+k)` then types B and P as dyadic, with `P=B^t` and t≥1.

Only after that typing do we separate the joined AND into physical, controller and range blocks. The unit top mask contributes zero because B AND1=0. The physical and controller blocks are identical in the two successors. In the range block h<P8 and, since P is dyadic,

    ((2D−1)*J*R_32(P)) mod P^8
       = (2D−1)*J*R_8(P).

There is no coefficient carry: `(2D−1)J<P`. It follows exactly that

    h AND ((2D−1)*J*R_32(P)) = h

if and only if the same equation holds with R8. The extra24 high mask lanes in the reused source contain no history bits. This is a typed binary equivalence; no unconditional polynomial equality between R32 and R8 is claimed.

The unchanged one-hot controller, weighted flow, selected-source fields, retained D>u and four endpoint transports then recover the same genuine projective chronology. This proves soundness for both full sources.

## 4. Same outer-coordinate projection and accepting inputs

Conversely, keep the ordinary input and all outer controller/history coordinates of a positive zero in any of the parent or successor sources. Its recovered dyadic P,B and true joined AND satisfy either range recipe by the preceding low-eight identity, and either top mask by B AND1=B AND2=0. The displayed pretyping bounds give positive native fields at the actual new q and packed index. The prescribed native converse and tail-coordinate theorem supply fresh positive native coordinates. All six comparisons and the complete finalizer then hold.

This proves equality of the full positive-zero projections onto x, height_slack, the four histories, eight selected-source hats,28 edge hats and the joint global slack. It is stronger than agreement on the represented x values, but it fixes no native witnesses. It is not a full positive-zero bijection or a signed/rational-zero theorem.

The inherited predicate is proper and nonempty. For every positive x congruent to2 modulo5, with u=24x+13, the physical word `R U^(u−1)` is a Nielsen word and sends `(1,u,1,u)` to `(0,1,0,1)`. The original proof excludes x=1 using the order-six modulo5 orbit. No exact classification beyond its stated sufficient/necessary residues is introduced here.

The receipt explicitly constructs the x2,u61,124-step outer computation with D128 in both successors, and x7,u181,364 steps with D256. It checks positive hats/global slack, all five outer residuals, both complete joined AND instances, exact scale and all four positive truth fields. **No enormous native Pell zero is materialized.** Native existence is the proved component extension. Computation duration remains existential and unbounded; these are illustrative fixed-table sources, not instantiated universal alphabets.

## 5. Exact full degrees and complete verification

Every supplied coordinate, including x, has degree1; fixed compiler numerals have degree0. The complete guarded main-norm cancellation is the same ring identity as in the parent, with every actual producer checked. The separate-range source uses `m=32`, computed P (`nu=2`) and `a_scale=48`; reused range uses a_scale72. The exact full-degree formula from the pinned tail proof is

    73+2*(29*a_scale+7*m+106).

The seven factor degrees, ordered first/main/auxiliary/index/linear/strong/joint, are

    reused32: 679,1210,884,532,532,1064,2;
    separate8: 487,874,596,388,388,776,2.

The outer sum contributes6, giving4909 and3517. The naive bounds are5055 and3615. For each actual complete source the recorded weighted-indeterminate substitution has a nonzero coefficient at the claimed guarded degree modulo1000000007; this proves attainment for the literal fixed-numeral polynomial. No equation holding only at zeros is substituted to lower degree.

The source recounts all741 live operations across the two complete arrays, proves17 scalar polynomials and740 retained-register interfaces, checks all12 comparisons and both seventeen-gate finalizers, and certifies both exact degrees. It checks12 complete numerical outputs, including4 rational assignments;54 additional exact low-eight binary mask cases; and the four genuine accepted outer histories described above. These finite checks supplement the general positive-domain proof rather than replace it.

Run from any working directory:

    python3 group_projective_nonempty_mask_frontier.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/to/group_projective_nonempty_mask_frontier.json

Use `--output` to write the deterministic receipt. Authentication checks every pinned dependency anew, preferring the specified root and using sibling files only for missing relative files. The helper is a bounded source/proof CLI, not a maintained hostile-input compiler API. No frozen source is edited, no graph or lane optimization is repeated, and no improvement to the established universal operation frontier is claimed.
