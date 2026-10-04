# Atomic synchronized matrices in one fixed-arity history kernel

The complete uniform atomic source has **4,155 operations = 1,529M + 2,626A**, **460 positive integer witnesses**, and exact degree **34,045**. It replaces 19,611 unit-shear steps in the fixed table by 97 atomic paired matrix actions, with a separate matrix SWITCH and an identity IDLE. Its finite controller has **99 edges, two states and m=128**. The ordinary input remains x, with no external Pell index or supplied duration.

The source uses 340 selected-source lanes and four history-range lanes. It does not pad the physical block to 512 lanes; neither native typing nor the coefficient-recovery proof requires that padding. A second complete diagnostic source has 227 operations, 31 positive witnesses and exact degree 1,357. Both are fully emitted arrays. The uniform count is substantially below the preceding 176,586-operation construction, but remains above the universal 84-operation frontier.

The eight context parameters remain fixed coefficients prepared by a valid program recipe. They are not existential witnesses or freely varying program-input coordinates. The instruction array and witness count are uniform over those valid numerical specializations; arbitrary assignments to the coefficient ports need not represent a program.

## 1. The unchanged matrix and ordinary-input theorem

Retain the original Gamma1 table and the exact right-action frame proved in [uniform context packing](matrix193_uniform_context_packing.md). Its fixed matrices are

    K_i=C0^(-1) H_i C0, G_i,       for the 96 retained tiles,
    B0=[[-52109,29036],[-94920,52891]].

For program contexts U,V, set L=Psi(V#)^(-1), R=Psi(U)^(-1). Start

    X=e1 L^(-1) C0,       Y=e1.

The controller has these atomic edges:

* edge 0: LOAD, from state 0 to 0, applying Y -> Y B0^(-1);
* edge 1: SWITCH, from state 0 to 1, applying Y -> Y R;
* edges 2 through 97: the 96 paired TILEs in retained tile-ID order, from state 1 to 1, applying (X,Y) -> (X K_i,Y G_i);
* edge 98: identity IDLE, from state 1 to 1.

Every other row is left unchanged by LOAD and SWITCH. Start in state 0, end in state 1 and require X=Y. A chronological accepted path therefore has LOAD* SWITCH followed by TILEs and IDLEs. The marked LOAD edge itself now counts LOADs; no private macro path is needed.

After k LOADs and tile word s, the terminal rows are

    e1 L^(-1) H(s) C0,       e1 B0^(-k) R G(s).

The inherited first-row injectivity on H' makes their equality equivalent to

    H(s) C0 G(s)^(-1)=L B0^(-k) R.                 (1)

This is the original directed193 membership target in the correct multiplication order. The original fixed-program unary initialization applies when k=x. An empty tile word means the central generator alone, not an empty semigroup product. The source does not assume universality of the particular saved illustrative contexts.

Atomic updates preserve exactly the same matrix products as their signed-unit expansions. Their intermediate unit-shear states are simply no longer part of the certificate. The large but fixed entries of K_i,G_i are used as paid coefficients in the atomic update arithmetic below.

## 2. Why 340 selection lanes suffice

The actual 96 fixed K_i matrices have 72 distinct values, while all 96 G_i matrices are distinct. Group the K_i by full matrix equality in first-appearance order. If g is one such group, define

    S_g=sum_(TILE edge e in group g) E_e.

For the Y row use one group for each G_i, then one LOAD group and one SWITCH group. Thus there are 72 X groups and 98 Y groups, 170 groups in total. Each group selects the two coordinates of its row, giving 340 selected-source words. The X-group edge sets partition the 96 TILE edges; the Y groups are singleton edges. Grouping identical K_i changes no branch choice or matrix product.

The lane order is:

* lanes 0 through 143: the two X coordinates for each of the 72 groups;
* lanes 144 through 335: the two Y coordinates for each of the 96 TILE groups;
* lanes 336,337: the LOAD Y coordinates;
* lanes 338,339: the SWITCH Y coordinates.

Before native typing each group selector is a nonnegative sum over a subset of edge words, so S_g<=J. After one-hot controller recovery, it is a Boolean word. At a TILE cell exactly one X group and one Y group are active; at a LOAD or SWITCH cell only its Y group is active; IDLE activates none. There are therefore at most four active selection lanes in any cell.

The ungrouped coordinate-selection scheme would use 388 lanes. All 384 TILE source-coordinate rows of M-I are nonzero in the actual table, so that ungrouped count has no omissions from zero coefficients. The saving to 340 is the exact sharing of identical K actions. Neither count is claimed minimal among arbitrary linear-function selectors, coefficient bucketings or other encodings.

## 3. Fixed coefficients and safe radix

The eight fixed coefficient ports are the same as in the preceding uniform source:

    initial_X0, initial_X1,
    R00_minus_one, R10, R01, R11_minus_one,
    radix_multiplier, Hfix.

A valid program recipe supplies initial X=e1 L^(-1) C0 and the indicated entries of R. All fixed K_i,G_i and B0^(-1) are reconstructed from the original frozen matrix table. Let

    Lambda=max_(all fixed K_i,G_i,B0^-1,R)
              max(|M00|+|M10|, |M01|+|M11|).

Choose a fixed power of two K>=32 with K>Lambda+1. Set

    Hfix>=max(m,340),
    Hfix>every absolute initial signed coordinate,
    D=x+Hfix+height_slack, c0=D-1, B=K D.          (2)

The slack is strictly positive and x is natural, or restricted to positive input. Thus D>x, B>m, and every initial shifted coordinate lies strictly between 0 and 2D. Coefficient magnitudes can grow with the program; the runtime operation and witness counts do not. No determinant test or variable matrix inverse is supplied for free: the fixed recipe supplies valid matrices, and all runtime coefficient multiplications are included in the source.

The largest column absolute sum in the original fixed table, including LOAD, is 20,190,363,719,353,740,312,042,533. For the saved context instance it is also larger than the R-switch bound, so K=2^85 suffices. A different valid program may require a larger fixed dyadic K.

## 4. Exact packing without physical power-of-two padding

Let ell=340 and m=128. Supply positive edge hats and compute

    E_e=Ehat_e-1, J=sum_e E_e, P=(B-1)J+1.

Let the 170 groups have selectors S_g and row types j_g=0 for X, j_g=2 for Y. Supply two positive selected-output hats per group and put

    Z_g0=Zhat_g0-1, Z_g1=Zhat_g1-1.

With R_a(P)=1+P+...+P^(a-1), define

    Hphys=sum_(g=0)^169 P^(2g)(H_(j_g)+P H_(j_g+1)),
    Mphys=(B-1)(1+P)sum_(g=0)^169 S_g P^(2g),
    Zphys=sum_(g=0)^169 P^(2g)(Z_g0+P Z_g1),
    Hrange=H0+P H1+P² H2+P³ H3,
    C=sum_(e=0)^98 E_e P^e,
    O=J R_m(P), O4=J R_4(P), M4=(2D-1)O4,
    T=P^(ell+m), T2=P^(ell+m+4),
    H=Hphys+P^ell C+T Hrange+B T2,
    M=Mphys+P^ell O+T M4+T2,
    Z=Zphys+P^ell C+T Hrange,
    q=32 B T2.                                    (3)

All powers, repunits and products are computed by finite paid schedules. The controller occupies the next m lanes after the ell physical lanes. The four range lanes occupy the next four lanes, and T2 is the top position. There is no overlap. P^ell is a valid lane shift regardless of whether ell is a power of two.

Bind the same literal 63-row native cone to q,16H+13,16M+10,16Z+8,P and

    G=sum_i H_i+sum_(all340 hats) Zhat+bound_global.

The output includes the native/joint product multiplied by one plus the squares of all six outer residuals, followed by subtraction of one. At a positive integer zero the square sum vanishes, the native product is one and every native factor is a sign. The joint factor G-P gives P>=344, bounds each H_i and unshifted Z below P, and forces J>=1 and B<=P.

Pretyping does not use a bound on the sum of all group selectors. Each physical mask lane separately satisfies (B-1)S_g<=P-1, so Mphys<P^ell. The other physical words are also below P^ell; C<P^m and (2D-1)J<P. Therefore all three bodies below the top terms lie below T2. The four native truth fields are positive, sum to q-1, and have residues 1,4,2,8 modulo 16, exactly as in the inherited bootstrap.

That unchanged bootstrap handles both native index signs and yields positive unit factors and dyadic q. Equation (3) gives dyadic B,P; fixed dyadic K makes D dyadic. The computed repunit gives P=B^t for some integer t>=1. The joined AND separates the physical, controller, four-range and top blocks. The top condition is B AND 1=0. Four range lanes suffice because they contain each independent history field once. Thus each history digit h_i(j) satisfies

    0<=h_i(j)<=2D-1,
    -(D-1)<=h_i(j)-c0<=D.                         (4)

The controller AND and checksum give exactly one edge per cell. The group selectors are now Boolean indicators and each selected word is the exact selected source digit. A TILE may select four digits without compromising either pretyping or this decoding.

## 5. Atomic corrections, chronology and exact input

For each group with fixed row matrix M_g, compute

    shift_g=c0 S_g,
    u_g=Z_g0-shift_g, v_g=Z_g1-shift_g,
    a_g=(M00-1)u_g+M10 v_g,
    b_g=M01 u_g+(M11-1)v_g.                       (5)

This costs at most nine operations per group before fixed zero/one folds. Sum a_g,b_g over X groups to obtain delta_0,delta_1; sum over Y groups to obtain delta_2,delta_3. At each typed cell at most one group for each row is active. Hence (5) gives exactly the chosen atomic matrix increment, and IDLE has zero increment. In particular a group shared by several TILE edges still applies the same fixed matrix only once at a cell.

Retain four aggregate history equations with shared positive terminal fields:

    B(H_i+delta_i)=H_i+F_i P-I_i,
    I_i=c0+initial_i,
    F_i=F_even for even i and F_odd for odd i.

At a first unrecovered interior coefficient the signed discrepancy is bounded in absolute value by (Lambda+1)D<B. The initial discrepancy is below 2D. Successive reduction modulo B therefore recovers the initial state and every entire matrix update; no intermediate unit-shear states are assumed. The top coefficient recovers the actual terminal value, so sharing the two F fields forces row equality. Their soundness does not require a separate terminal range bound.

The two-state controller flow can be computed in four operations:

    target_word=J-E_LOAD,
    source_word=target_word-E_SWITCH,
    source_word+P=B target_word.                  (6)

This is the full weighted open-end flow equation, simplified using the actual edge table. Together with one-hot indicators it gives exactly the chronological two-phase controller. In particular SWITCH occurs once, and its pre-state is typed before the R action.

At that pre-state Y=e1 B0^(-k), where k is the number of LOAD edges. The first coordinate satisfies a0=1,a1=52891 and a(k+2)=782a(k+1)-a(k), hence a_k>=k+1. Equation (4) gives k<D. Finally retain

    (B-1)Q=E_LOAD+(B-1)-x.                        (7)

Population modulo B-1 gives k congruent to x. Since both are in [0,D) and D<B-1, k=x. Combining this with (1) proves soundness for the ordinary-input language, with no duration parameter or independently supplied Pell index.

## 6. Positive completeness

For an accepted finite tile word, run x LOADs, SWITCH, that tile word and optional IDLEs. Choose a sufficiently large dyadic D above x+Hfix and every absolute coordinate of this atomic trajectory, including the endpoint, plus one. Set height_slack=D-x-Hfix and construct the exact radix-B edge, history and selection words.

There are at most four selected digits per cell, so

    sum H_i+sum Z_gj <= (16D-8)J,
    bound_global=P+1-sum H_i-sum Z_gj-ell
                >=((K-16)D+7)J-ell+2 >0.          (8)

Here J>=1,K>=32 and D>Hfix>=ell make the final inequality immediate. All supplied history and terminal fields are strictly positive after the chosen shift; absent selections have positive hat 1. The population quotient is

    Q=1+sum_(LOAD cells j)(B^j-1)/(B-1)>0.

The six outer comparisons and the joined AND hold at exactly the q in (3). The inherited native converse supplies fresh positive native coordinates. This proves equality of the full positive-zero input projection with the fixed-program matrix language. It is not a polynomial identity with the unit-shear source and does not assert a bijection between native witness tuples.

Zero input and an empty tile word are allowed precisely as in the parent interface. A compulsory switch guarantees at least one cell. Ordinary positive input follows by restricting x>0.

## 7. Complete source ledger and exact degree

The uniform source has 99 edge hats, four histories, 340 selected-source hats, twelve native coordinates, one height slack, one joint-bound slack, two shared terminal fields and one population quotient: 460 positive witnesses. The external input x and eight fixed coefficient ports are excluded from that witness count.

| Full array | Packing | Native | Outer producers | Finalizer | Total | M,A | Positive witnesses |
|---|---:|---:|---:|---:|---:|---|---:|
| Atomic diagnostic |99|63|45|20|227|101M,126A|31|
| Original fixed-table atomic grammar |2,235|63|1,837|20|4,155|1,529M,2,626A|460|

Every fixed-coefficient multiplication, selected-source product, residual, square and final addition is included. The source uses fixed zero/one folds and literal common expressions; no branch test or whole matrix action is assigned a free runtime cost. All rows and ports are structurally live in the parameterized grammar. Particular coefficient specializations may admit further simplification; no optimality is asserted.

For the original table, ell=340,m=128 and the top exponent is ell+m+4=472. Counting fixed coefficients as degree zero, the actual leading degrees are

    deg q=945, deg F3=943.

The term T Hrange uniquely leads F3; its highest form is a nonzero multiple of P^(ell+m+3) H3. The inherited all-value main-norm cancellation and the seven native factor leaders therefore give degrees

    4727,8506,5684,3780,3780,7560,2.

Their sum is 34,039. The outer square sum has exact degree six: an independent shared terminal field times P supplies a nonzero cubic coefficient in a history residual, and a sum of real squares cannot cancel that highest form. Thus the complete exact degree is 34,045. Generally this grammar has degree

    72(ell+m+4)+61,

provided the independent source ports are retained and the fixed radix is positive. This uses only polynomial identities, not native unit equations valid on zeros. Valid changes to the program R or initial coefficients do not remove the nonzero native or terminal-field leaders.

The diagnostic has four edges, m=8 and ell=6: one X TILE group, no identity Y TILE group, one LOAD group and one SWITCH group. Its initial X=(2,1),Y=(1,0), TILE matrix [[0,-1],[1,2]], LOAD Y1-=Y0 and switch R=[[2,1],[1,1]] accept every natural input with exactly x TILEs. Its exact degree is 72(6+8+4)+61=1,357. It is deliberately not a universal-program example. Its six-hat joint sum is at least 11, so initially P>=10; J=0 would give P=1 and is excluded. Therefore J>=1 and P>=B>=320, which supplies the same native bootstrap threshold as the larger source.

## 8. Frozen source and bounded verification

The [fresh emitter](matrix193_atomic_context_packing.py) and [saved receipt](matrix193_atomic_context_packing.json) contain both complete arrays, their literal controller and group registries, all witness and fixed-coefficient ports, stage ledgers, native cut bindings and finite evidence. Their frozen SHA-256 values are:

| Artifact | SHA-256 |
|---|---|
| Python | `18ed65a37a471a17b31245b237b7e3b987c4cef58fcbd3c9dfb4b6d0c67daa32` |
| JSON | `7f9f9614f3862d08fa2645a5944a4567f4f268e4e93a57c5dec6e59d5a9fe8c9` |

All 14 dependency hashes declared in both files were authenticated while preparing this companion. They pin the synchronized-row data, original unit-shear table and its source/proof, marked-loader native source/proof, uniform context proof, and the inherited range, projective-tail, unary initialization, Gamma1 and context-absorption proofs. These predecessors are read as inert bytes or JSON; the new emitter does not import or execute predecessor Python. The native Pell/AND converse and the original universal initialization remain inherited mathematical dependencies. This note proves the changed atomic packing and its interface to those results; it does not independently recertify every predecessor construction.

The frozen receipt records:

* all 4,155 uniform rows and all 227 diagnostic rows, with every row live;
* 32 modular comparisons, 16 per array over two primes, checking the complete output, native cuts, native factors and six residuals against direct formulas;
* ten fully materialized diagnostic outer histories, for x=0 through 4 and zero or two IDLEs, including the joined AND, positive fields, input count and six zero residuals;
* a dense univariate specialization of the complete diagnostic polynomial with degree 1,357 and leading coefficient 864,850,896 modulo 1,000,000,007;
* the actual saved 83-TILE trajectory preceded by SWITCH, giving 84 atomic cells at x=0. Its largest signed coordinate has 475 bits; D has 476 bits, B has 561 bits, and q has 22,203,446 bits. The outer history, all group selections, joined AND, positive slacks and native input fields, terminal equality and all six residuals are computed exactly. The recorded outer-field digest is `4a9126fee26facb9ca3c7b6e235bac98445802121a5f58bbaea01f3f3c2d97ef`.

The last fixture is explicitly a zero-input boundary example in the saved illustrative context. Its enormous native Pell witnesses are not materialized. Positive native extension is supplied by the theorem in §6, rather than inferred from these finite checks. The general degree 34,045 follows from §7; the receipt's diagnostic dense expansion does not expand the full uniform polynomial.

Aristotle independently reconstructed the actual 84-cell outer fixture from the saved matrices and tile sequence without executing author or predecessor code, obtaining the same outer-field digest and all the stated outer checks. His full companion proof read and three fresh leading-form assignments found no discrepancy. Root separately read the complete source and proof, corrected the pre-freeze prose edge numbering to match the unchanged registry, and completed fresh normal and optimized exact receipt replays from `/`. These are complementary finite and proof checks, with the native-extension scope unchanged.

After the files and their pinned dependencies are installed together, the frozen replay interface is:

```sh
replay_wip=/absolute/path/to/native-stream-queue
python3 "$replay_wip/matrix193_atomic_context_packing.py" \
  --root "$replay_wip" --expect "$replay_wip/matrix193_atomic_context_packing.json"
python3 -O "$replay_wip/matrix193_atomic_context_packing.py" \
  --root "$replay_wip" --expect "$replay_wip/matrix193_atomic_context_packing.json"
```

The 4,155-operation result is a complete, uniform, fixed-program ordinary-input upper construction using valid fixed coefficients and 460 positive witnesses. It reduces the earlier matrix construction substantially but does not improve the universal 84-operation arithmetic bound. Neither the diagnostic nor arbitrary assignments to the eight fixed coefficient ports are asserted to be universal programs.
