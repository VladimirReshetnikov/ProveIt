# Packed selected outputs for the atomic matrix history

The complete fixed-table source has **3,162 operations = 1,467M + 1,695A**, **152 positive integer witnesses**, and exact degree **34,817**. Relative to [atomic context packing](matrix193_atomic_context_packing.md), it saves **993 operations (62M and 931A) and 308 witnesses**. The controller, ordinary input, matrices, and valid fixed-program coefficient recipe are unchanged. This remains above the universal 84-operation bound.

The change stores selected outputs in two whole integer blocks and recovers four weighted sums by carry-free integer multiplication. There are still 340 physical selection slots inside one joined AND: no reduction of that slot count is claimed. Coefficient polynomials, powers, digit-extraction comparisons and positive bounds are all charged. No digit extraction, Hadamard product, or division is a circuit primitive.

The complete diagnostic source costs 330 operations and 57 positive witnesses, with exact degree 1,361. It is larger than the old 227-operation diagnostic; the saving depends on the fixed table having many selection slots. Neither that diagnostic nor arbitrary assignments to the fixed coefficient ports are asserted to be universal.

## 1. Retained interface and fixed numerical recipe

Read the frozen atomic receipt as data. Its controller is LOAD 0, SWITCH 1, TILEs 2–97, IDLE 98, with n=99, m=128 and two states. Its 72 distinct X matrices, 96 distinct Y TILE matrices, LOAD and SWITCH form 170 groups. Group selectors S_g are sums of edge words over their fixed edge subsets.

The X block has l_X=144 lanes, the fixed Y/LOAD block has l_Y=194 lanes, and the two context-SWITCH lanes remain separate. The X block comes first, then the Y block, then the SWITCH lanes. All program-dependent SWITCH coefficients retain their existing paid arithmetic.

For each of the first two blocks and output coordinate j, let a_(j,l) be its lane coefficient from M_g-I. Thus the two lane coefficients for output 0 are M00-1,M10, and those for output 1 are M01,M11-1. Fix

    M_block = 1 + max_(j,l) |a_(j,l)|,
    b_(j,l) = M_block + a_(j,l).

Every b is a strictly positive fixed integer less than 2M_block. Let C be the smallest power of two strictly exceeding both numbers 2M_block*l_block. The actual values are

    M_X = 17381989392455015642208733,
    M_Y = 392491491,
    C = 2^93 = 9903520314283042199192993792.

The diagnostic has l_X=l_Y=2, M_X=M_Y=2 and C=16. These integers are computed from the authenticated fixed matrices; they do not depend on the duration, ordinary input, supplied witnesses or program contexts.

Retain the parent's eight fixed coefficient ports and valid recipe for initial rows, R, positive dyadic radix multiplier K and Hfix. In particular K>=32 and K>1+the largest matrix column absolute sum; Hfix>=max(m,340) and exceeds the absolute initial coordinates. Compute

    D=x+Hfix+height_slack, c0=D-1, B=K D,
    E_e=Ehat_e-1, J=sum_e E_e, P=(B-1)J+1,
    Q=C P.                                                   (1)

Q is a wider lane radix; P remains the time-history scale and the native joint-bound port. Every power of Q below has a fixed exponent determined by the table. No expression Q^t or new relation between a variable duration and an exponent is introduced.

## 2. New supplied coordinates and pretyping bounds

Replace the 338 individual positive selected-output hats in the two fixed blocks by block hats Z_X+1,Z_Y+1. Add positive block slacks enforcing

    Z_X + block_slack_X = Q^l_X,
    Z_Y + block_slack_Y = Q^l_Y.                              (2)

The two SWITCH outputs still use positive hats, encoding Z_SW0,Z_SW1. Change the native joint sum to

    G=H0+H1+H2+H3+Zhat_SW0+Zhat_SW1+bound_global.              (3)

In particular the large block integers are not included in G. At any positive integer zero, the unchanged integer native product times 1+SOS equals one. Hence all outer comparisons hold, the native product equals one, and every native factor is a sign. From G-P=±1 and positivity, each H_i and Z_SWj is below P. Since G>=7, P>=6; J=0 would imply P=1, so J>=1 and P>=B. The inherited K,Hfix bound then supplies P>=12 for the native bootstrap.

In every lane formula from the atomic source replace the spatial lane radix P by Q; retain the time scale P in the history equations, native joint factor and population argument. Let ell=340 and R_a(Q)=1+Q+...+Q^(a-1). Define

    Hphys=sum_g Q^(2g)(H_(row(g))+Q H_(row(g)+1)),
    Mphys=(B-1)(1+Q) sum_g S_g Q^(2g),
    Zphys=Z_X+Q^l_X Z_Y+Q^(ell-2)(Z_SW0+Q Z_SW1),
    Hrange=H0+Q H1+Q² H2+Q³ H3,
    Controller=sum_e E_e Q^e,
    O=J R_m(Q), O4=J R_4(Q), M4=(2D-1)O4,
    T=Q^(ell+m), T2=Q^(ell+m+4),
    H=Hphys+Q^ell Controller+T Hrange+B T2,
    M=Mphys+Q^ell O+T M4+T2,
    Z=Zphys+Q^ell Controller+T Hrange,
    q=32 B T2.                                               (4)

Before any native typing, E_e>=0 and each selector S_g<=J. Thus every physical mask lane is at most P-1<Q. The history and SWITCH lanes are below P<Q, and (2) bounds each large selected block by its allotted Q-power. The controller and range blocks have the same elementary bounds as in the parent, now with Q in place of the lane radix. Consequently each body below T2 is less than T2. The four native truth fields are positive, sum to q-1 and retain their residues 1,4,2,8 modulo 16.

The same native bootstrap therefore yields dyadic q and the joined AND. Equation (4) forces B and Q dyadic, and Q=C P with fixed dyadic C forces P dyadic. The native repunit theorem gives P=B^t for t>=1. The controller AND gives one edge per cell. The four range lanes bound every shifted history digit by 2D-1.

Finally the joined AND, separated into Q-blocks, uniquely determines the block digits

    Z_block=sum_(l=0)^(l_block-1) Z_l Q^l,
    Z_l=H_(row(l)) AND ((B-1)S_(group(l))).                    (5)

In particular 0<=Z_l<P, even though the preliminary block constraints only gave 0<=Z_l<Q. This stronger conclusion is obtained before using any convolution bound.

## 3. Exact middle-digit and word-sum extraction

For a block of length l define, using paid fixed-coefficient Horner evaluation,

    B_j(Q)=sum_(r=0)^(l-1) b_(j,r) Q^(l-1-r).

Multiplying by Z_block makes the coefficient of Q^(l-1) equal to

    d_j=sum_r b_(j,r) Z_r.                                  (6)

Every coefficient of the whole convolution is nonnegative and strictly less than

    l*(2M_block)*P < C P=Q.

Thus ordinary integer multiplication introduces no carries between these Q-digits. Four such products suffice, one for each output coordinate of each block.

For each product supply nonnegative low,d_j,high via positive hats and impose

    B_j(Q)*Z_block = low + Q^(l-1)*(d_j+Q*high),
    low + low_slack = Q^(l-1),
    d_j + dot_slack = Q,                                    (7)

with both slacks positive. These comparisons enforce 0<=low<Q^(l-1) and 0<=d_j<Q. Euclidean uniqueness then forces exactly the middle digit (6); high needs no upper bound. Conversely the actual product supplies nonnegative high,low,d_j and strictly positive slacks.

To remove the common offset M_block, recover the sum s=sum_r Z_r. Since

    Z_block congruent to s modulo Q-1,
    0<=s<l P<Q-1,

s is the unique remainder. Supply nonnegative s and a nonnegative quotient through positive hats and require

    Z_block=(Q-1)*sum_quotient+s,
    s+sum_slack=Q-1,                                       (8)

with positive sum_slack. These are two paid comparisons per block. The strict bound uses C>2M_block*l, M_block>=1 and P>=1.

The resulting unshifted matrix increment is

    delta_j = d_j-M_block*s
              -c0*sum_g (a_(j,2g)+a_(j,2g+1))*S_g.          (9)

Expand (6) and s to verify (9): it is exactly sum_g of the corresponding coefficients times (Z_(2g)-c0*S_g, Z_(2g+1)-c0*S_g). This is the old atomic correction after (5) has recovered the selections. The two SWITCH increments are computed directly with their original four fixed multiplications. Signed intermediate results are allowed; every newly supplied coordinate is strictly positive through its hat or slack.

This proof establishes positive-zero equivalence. It does not assert an all-value polynomial identity between sources with different supplied coordinates. In particular arbitrary values of the new quotient/remainder ports do not implement digit extraction unless their paid comparisons vanish.

## 4. Ordinary input and positive completeness

With (9) in place, the four aggregate history equations, controller flow and marked-LOAD population equation are unchanged:

    B(H_i+delta_i)=H_i+F_i P-I_i,
    J-E_LOAD-E_SWITCH+P=B(J-E_LOAD),
    (B-1)*population_quotient=E_LOAD+B-1-x.

The inherited fixed K bounds the first-disagreement matrix residual by B. Thus these equations recover the exact atomic trajectory. The SWITCH pre-state is typed before multiplication by R. The unchanged LOAD growth gives k<D for its population, while x<D; reduction modulo B-1 gives k=x. The fixed-program matrix membership and unary initialization therefore have exactly the same ordinary-input projection as the atomic parent.

For completeness, start with its accepting finite atomic trajectory and choose a sufficiently large dyadic D exactly as in the parent. Form every old selected lane Z_l. Concatenate the first 144 and next 194 into the new block integers. Equations (2), (7) and (8) have the positive hats and slacks described above. Choose the new joint slack as

    bound_global=P+1-sum_i H_i-Z_SW0-Z_SW1-2.

The four histories and two SWITCH selections satisfy

    sum_i H_i+Z_SW0+Z_SW1 <= (12D-6)J,
    bound_global >= ((K-12)D+5)J >0.                         (10)

All new outer constraints and the joined AND hold. The inherited native converse provides fresh positive native witnesses for the newly widened packing fields. No map keeping the old native Pell tuple is claimed. The construction preserves the accepted ordinary-input set, allows the same x=0 boundary, and restricts to ordinary positive inputs by x>0.

## 5. Fully emitted cost and exact degree

| Complete source | Packing | Native | Outer producers | Finalizer | Total | M,A | Positive witnesses |
|---|---:|---:|---:|---:|---:|---|---:|
| Diagnostic |90|63|103|74|330|132M,198A|57|
| Original fixed table |893|63|2,132|74|3,162|1,467M,1,695A|152|

The 24 comparisons are the old six, two block bounds, twelve middle-extraction comparisons and four word-sum comparisons. The 338 old selected hats are replaced by 30 positive coordinates: two block hats, two block slacks, twenty middle-product hats/slacks and six word-sum hats/slacks. The two SWITCH hats remain. This gives the exact witness saving 338-30=308.

The entire emitted uniform array contains 1,022 distinct integer literals; its largest absolute literal is C=2^93, with 94 bits. All other fixed matrix-derived coefficients and the eight inherited coefficient ports have the finite recipes above. Every nontrivial runtime multiplication by one of these numerals is counted. All source rows and free ports are structurally live. No claim of arithmetic optimality is made.

The new Q=C P has degree two, counting fixed coefficients as degree zero. The top terms of q and the native F3 remain degrees 945 and 943. For F3 the unchanged Q^(ell+m) Hrange term strictly dominates the compressed output blocks. The native factor degrees are therefore still

    4727,8506,5684,3780,3780,7560,2,

whose sum is 34,039. This uses the exact all-value main-norm expansion, not a zero-set substitution: if Droot=X+ac+gamma*(4a+3), then

    Droot²-(a²+4a+3)c²
      =X²+2acX+2gamma*(4a+3)X
       +2ac*gamma*(4a+3)+gamma²*(4a+3)²-(4a+3)c².

Its unique top degree is 8,506. The other displayed factors have the same nonzero leading forms as in the atomic proof after the fixed rescaling of the spatial radix; the changed G has degree one and leaves the joint factor's degree-two leader -P unchanged.

A middle-product residual for a block of length l has unique highest degree 2l+1 from -Q^l*high_hat. Its left product has degree at most 2l-1; the remaining right terms have lower degree. Other new comparisons have degree at most 2l. The old history/control/population residuals have degree at most three. Consequently the sum of squares has exact degree 4*194+2=778. The independent high hats and real sum-of-squares noncancellation make this uniform under valid coefficient specialization. The whole source has exact degree 34,039+778=34,817.

For the diagnostic the native degree is 1,351 and the longest block has length two, giving exact total degree 1,351+10=1,361. These are polynomial degree statements on all independent supplied ports, not degrees restricted to native zeros.

## 6. Verification scope and replay

The [fresh helper](matrix193_packed_output_scout.py) reads the predecessor arrays as inert JSON and emits both complete arrays in the [receipt](matrix193_packed_output_scout.json). It uses no predecessor Python imports or execution. Its receipt checks every source row's dependencies and liveness, exact stage and operation counts, and the fixed coefficient recipe. Its three strict dependencies are the frozen atomic receipt and companion plus the marked-loader receipt containing the literal native contract. Their exact SHA-256 values are included in both source and receipt; all three were authenticated before emission.

| Artifact | Frozen SHA-256 |
|---|---|
| Python | `80959b87138eea4148b5fc6aafb78fc73a5a8283d3b676c142f57b8a8190fba9` |
| JSON | `74f119d979d92851e571967de7baf046e85d523ba9ca03acf21fa92bafa1c244` |

The evidence includes 32 modular complete-output comparisons against independent direct formulas, ten diagnostic outer fixtures evaluated through all literal nonnative source rows, and a dense complete diagnostic specialization of degree 1,361. The actual saved 83-TILE word plus SWITCH is also reconstructed exactly at x=0. For that large fixture the packed blocks, four integer products and middle extractions, all 24 mathematical outer comparisons, joined AND and positive fields are materialized; the whole literal outer DAG is not re-evaluated with those enormous integers. The modular checks cover that emitted DAG. No native Pell tuple is materialized for any outer fixture.

The big fixture remains the parent's illustrative zero-input boundary, not an asserted numerical universal-program instance. The finite checks support the changed packing implementation; the full input-projection theorem depends on §§2–4 and the explicitly inherited matrix/native theorems.

The diagnostic dense specialization has leading coefficient 567,060,132 modulo 1,000,000,007. In the actual 84-cell outer fixture, D and B retain 476 and 561 bits, Q has 47,134 bits, and q has 22,247,342 bits. Its outer-field digest is `69354b5e33fc40c1990a31713d5ae17b53265374f1590b2ae26b6082f983f610`. These values describe the widened packing in this source, not the old atomic receipt.

Fresh normal and optimized exact receipt replays from working directory `/` both passed. Parsing rejects duplicate JSON keys and comparison is recursive and type-exact. Once this trio and the three pinned dependencies are installed together, the replay commands are:

```sh
replay_wip=/absolute/path/to/native-stream-queue
python3 "$replay_wip/matrix193_packed_output_scout.py" \
  --root "$replay_wip" --expect "$replay_wip/matrix193_packed_output_scout.json"
python3 -O "$replay_wip/matrix193_packed_output_scout.py" \
  --root "$replay_wip" --expect "$replay_wip/matrix193_packed_output_scout.json"
```
