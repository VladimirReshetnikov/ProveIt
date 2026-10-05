# A nine-operation shared input for strictly positive matrix equality

Root's fixed rational change of coordinates and constant-coordinate sharing reduce the input loader of the accepted positive-matrix equality substrate from14 operations to **9**, with two explicit schedules: **5M+4A** and **4M+5A**. Both produce the same positive integer column in dimension8, with no auxiliary witnesses. A newly fixed strictly positive integer matrix alphabet recognizes exactly the same ordinary inputs by equality of its first and last terminal coordinates.

The signed action is rescaled by a nonzero duration factor; its zero test is unchanged. This is an input-loader improvement, not a paid fixed-arity certificate for an unbounded word or a reduction of the complete universal operation frontier. The fixed signed alphabet and effective group theorem remain inherited from the frozen positive_matrix_single_equality_transfer_aristotle packet. That14-operation packet is unchanged and remains valid. The13- and10-operation intermediate constructions below are valid upper bounds, not failed theorems or minimum claims.

## 1. The inherited ordinary-input relation

The parent supplies a fixed finite signed integer7-by-7 alphabet A_sigma and fixed row

    u=(1,0,1,1,0,1,-4),

with the following interface. For every recursively enumerable S of positive integers, effectively fixed positive program numerals alpha,beta give

    x in S iff exists a finite word w: u A_w v(x)=0,
    r=alpha*x+beta,
    a=(r-1)^2+1,
    b=(r-1)r^2+r+1,
    c=r^4+(r+1)^2,
    v(x)=(a,b,c,a,b,c,1)^T.                                  (1)

The alphabet is independent of both program and ordinary input. The actual universal slice has alpha=12*2^(p+1), beta=12*2^p, fixed before x varies; no run-time exponentiation is supplied. Because alpha,beta,x are positive integers, r>=2. On the stated universal slice with p>=0, r>=36.

Let e_i denote the seven-coordinate row selecting coordinate i. Define the fixed rational matrix T by its seven rows:

    row1 = u/2,
    row2 = e2-3e7,
    row3 = e3+e4-2e7,
    row4 = e4-2e7,
    row5 = e5-3e7,
    row6 = e6+e4-2e7,
    row7 = e7.                                                 (2)

This matrix is invertible. Indeed if y=Tz, then

    z7=y7,
    z4=y4+2y7,
    z3=y3-y4,
    z6=y6-y4,
    z2=y2+3y7,
    z5=y5+3y7,
    z1=2y1-y3+y4-y6+2y7.                                     (3)

Substitution verifies every row of(2), including 2y1=z1+z3+z4+z6-4z7. Thus T^(-1) is integral, as is2T. No arbitrary integer input is assumed to map integrally under T; the specific family(1) does, as shown next.

Writing V=(r^2+1)^2, the elementary identities a+c-2=V and u v/2=V give

    T v(x)=(V,b-3,V,a-2,b-3,V,1)^T.                           (4)

The entries here are integers. Some signed coordinates could be0 at r=2; the positive lift requires only that adding its fixed buffer gives positive coordinates, which is proved below.

## 2. Integer letters, word order and the exact zero contract

Define the new signed alphabet

    G_sigma=2 T A_sigma T^(-1).                                (5)

Both2T and T^(-1) are integral, so every G_sigma is an integer matrix. The alphabet is finite and effectively fixed independently of p and x. It uses the inherited abstract effective alphabet rather than a newly supplied numerical matrix list. Any coincident matrix labels may simply be retained; this does not change word reachability.

Use the same word order throughout: for w=(sigma1,...,sigmat), A_w=A_sigmat...A_sigma1, and likewise G_w. Adjacent factors T^(-1)T cancel, giving, including the empty word t=0,

    G_w=2^t T A_w T^(-1),
    G_w T v(x)=2^t T A_w v(x),
    2 e1 G_w T v(x)=2^t u A_w v(x).                            (6)

The last equation is an equality of integers. It proves that the first G-output coordinate is0 if and only if u A_w v(x)=0, for each finite word. No division, witness for divisibility, computed duration or extra scalar coordinate is needed to test zero.

**Review remark 1 (zero preservation does not mean unchanged action).** The stronger statement that(5) preserves the old signed trajectory literally would be false. If A=I_7, then G=2I_7, so a t-letter word acts by2^tI_7. In general the new first coordinate is2^(t-1)u A_w v, as a rational identity; the last line of(6) is its all-integer formulation, valid even at t=0. Root's proposal correctly uses the unchanged zero test. The positive lift in the next section exactly represents G through its decoder, not the unscaled A-action.

## 3. A common-row-sum positive alphabet

Apply the parent's elementary positive lift to G. With1 the seven-dimensional all-ones column, set

    kappa=1+max_(sigma,i) sum_j |G_sigma[i,j]|,
    C=8kappa,
    L_sigma=[G_sigma+kappa*1*1^T   kappa*1-G_sigma*1]
            [kappa*1^T             kappa            ],
    D=[I_7 | -1].                                                (7)

Every entry is an integer at least1: each absolute matrix entry and absolute row sum of G is at most kappa-1. Every row of every L_sigma sums to C, and direct multiplication yields

    D L_sigma=G_sigma D,
    D L_w=G_w D.                                               (8)

Put

    aa=(r-1)^2,
    bb=(r-1)(r^2+1),
    fhat=(r^2+1)^2+1,
    z(x)=(fhat,bb,fhat,aa,bb,fhat,2,1)^T.                       (9)

Because bb=b-2 and aa=a-1, equations(4),(9) imply Dz=Tv. For r>=2, all coordinates of z are positive integers. All subsequent states remain strictly positive under any word of the L-family. Combining(1),(6),(8) proves

    x in S iff exists a finite word w:
                    (L_w z(x))_1=(L_w z(x))_8.                 (10)

The only terminal test is that coordinate equality. The alphabet, row sum and buffer1 are fixed before p and x vary. The empty word is rejected because its coordinate difference is V>0. There are no variable initial witnesses, intermediate guards or new input codes.

**Review remark 2 (the positive-input endpoint r=1).** Extending the positivity assertion in(9) to every r>=1 would be incorrect: at r=1, aa=bb=0. The frozen14-operation parent handled that larger auxiliary r-domain, but the nine-row column uses r>=2. This restriction loses no ordinary input in(1), because positive alpha,beta,x already imply r>=2. The signed coordinate a-2 may be0 at r=2; this does not violate positivity of the lifted column, whose corresponding coordinate is aa=1.

## 4. Two complete nine-operation loaders

Literal copies and fixed output entries cost no arithmetic. Every binary product, including alpha*x, and every addition/subtraction is charged. The primary schedule is

|Row|Operation|Type|
|---|---|---|
|1|rx=alpha*x|M|
|2|r=rx+beta|A|
|3|eta=r-1|A|
|4|s=r*r|M|
|5|u=s+1|A|
|6|aa=eta*eta|M|
|7|bb=eta*u|M|
|8|V=u*u|M|
|9|fhat=V+1|A|

The output is precisely(9). Every row is live; every computed operand precedes its use. The complete loader has5M+4A=9 operations and zero supplied auxiliary witnesses. The repeated copies of fhat and bb are the source of sharing. The matrix T in(2) is part of the fixed alphabet construction and is not applied by an uncharged run-time matrix product: this nine-row source computes the entire column directly.

A second paid schedule gives the same output with4M+5A=9:

|Row|Operation|Type|
|---|---|---|
|1|rx=alpha*x|M|
|2|r=rx+beta|A|
|3|eta=r-1|A|
|4|aa=eta*eta|M|
|5|twice_r=r+r|A|
|6|u=aa+twice_r|A|
|7|bb=eta*u|M|
|8|V=u*u|M|
|9|fhat=V+1|A|

Here u=(r-1)^2+2r=r^2+1. Again every row is live and topologically ordered. No symbolic propagation or execution of a saved source array is used to obtain either ledger: they are the displayed eighteen newly handwritten row definitions and their identities. No optimality claim is made for the9 total or either split.

## 5. The valid intermediate13 and10 bounds

The first proposed rescaling uses T_half=diag(1/2,1,...,1)Q, where Q is the parent's unimodular matrix with first row u. It has integral inverse and2T_half is integral. Its raw input is (V,b,c,a,b,c,1), so buffer1 gives (V+1,b+1,c+1,a+1,b+1,c+1,2,1). Deleting the parent's doubling ff=V+V and changing the final row to V+1 gives13=5M+8A, with the same zero proof as(6). It is a valid intermediate construction.

The next coordinate matrix T_bar keeps first row u/2 and rows2,4,5,7 from(2), but uses row3=e3-2e7 and row6=e6-2e7. Its inverse is integral: z3=y3+2y7,z6=y6+2y7,z4=y4+2y7,z1=2y1-y3-y4-y6-2y7, with the other coordinates as in(3). Its buffered input is (V+1,bb,cc,aa,bb,cc,2,1), where cc=V-aa=c-1. Adding that one subtraction to the primary nine-row schedule gives10=5M+5A. This column is positive for r>=2. The final T replaces its two cc outputs by copies of fhat, deleting the cc operation and giving9. All three coordinate choices use the same scaled zero principle, with separately chosen fixed positive matrix alphabets.

The13 and10 counts are retained as valid upper bounds in the derivation, not as unproved minimum claims. No frozen14 proof or source is altered, and no unpublished intermediate draft is required as a mathematical dependency of this final note.

## 6. Normalized contraction and the exact-equality boundary

Each P_sigma=L_sigma/C is row stochastic and has entries at least1/C. Subtracting the all-ones8-by-8 matrix divided by C leaves a nonnegative matrix with row sum theta=1-8/C=1-1/kappa. The subtracted term contributes the same value in every coordinate. Hence for osc(z)=max_i z_i-min_i z_i and every word length t>=1,

    osc(P_sigma z)<=theta osc(z),
    osc(C^(-t)L_w z)<=theta^t osc(z).                           (11)

The empty word preserves oscillation separately. If the whole G-family is zero, kappa=1 and one step gives equality; otherwise0<theta<1. Along any infinite word, normalized minima are nondecreasing and maxima nonincreasing, and their difference tends to0. With positive initial values this proves convergence to one common positive value. The newly chosen row sum C may differ from the parent's row sum; no equality of their letter values or sizes is claimed.

Convergence remains distinct from exact finite acceptance. For a scalar example using signed G=[2], kappa=3 and C=6, the lift is L=[5,1;3,3]. Starting at(2,1), its coordinate difference is2^t at length t and never vanishes, while the normalized difference is(1/3)^t. This follows directly from D L=2D and is a boundary example, not the universal alphabet. It complements the frozen parent's difference1 example without modifying it.

The parent's finite-cap obstruction continues to apply: a total effective faithful replacement of(10) by only nonnegative polynomial updates and fixed-threshold/congruence guards, with computable finite input-dependent parameters, would decide the inherited nonrecursive ordinary-input instances. This uses the parent's accepted capped and group interfaces; it is not a new external undecidability claim.

**Open question 1 (credited unbounded-history compiler task).** Root's changes pay five fewer input additions than the14-row parent in the5M schedule, without supplying a fixed-arity ordinary-integer certificate for the selected unbounded word. Selectors, chronological consistency, duration/radix data, endpoint equality and ordinary-input binding remain to be paid. No complete compiler count, U9 comparison, universal gate saving or minimum-dimension result is claimed.

## 7. Binding and execution limits

The frozen parent proof SHA256 is9a5a060c7212af751d4df901eec50c07704beac8148e160cd578f868a9b2cfb3; its metadata SHA256 isa99d30fb2ae515294075f5fc55ed41e68d25db7f51e2f23fe177046ceff4f896. Both files were fully read inertly for this extension. The metadata records the exact earlier Gram, fixed-program group, capped-reachability and Markov proof scopes. Their accepted external group foundations and unmaterialized universal alphabet are inherited without a new external or implementation audit.

All new algebra and eighteen source-row checks above are handwritten. No supplied, archived, committed, predecessor or frozen program was executed or imported; no saved source array was evaluated or used for degree propagation; no scientific checks or builds were run. Only fresh byte/metadata work is used for binding. This separate note and its metadata are written in/tmp; neither the frozen parent nor repository files are modified.
