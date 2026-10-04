# A uniform matrix-history grammar with a paid context switch

The complete emitted uniform grammar has **176,586 operations = 58,770M + 117,816A**, **19,644 positive integer witnesses**, and exact degree **2,360,653**. Its input is the ordinary integer x; valid program recipes supply eight fixed coefficients. This is an explicit uniform construction upper bound, still far above the current universal 84-operation frontier.

The repeated matrix actions can be fixed independently of the chosen program. One program context moves to the initial row; the other is applied once by a paid matrix switch. The resulting four-coordinate packed history retains ordinary input x, the exact marked-LOAD count and a single native range/AND kernel. Its controller, source grammar and number of witnesses are independent of the lengths of the two program contexts.

This statement concerns a family of numerical polynomials obtained by a valid fixed-program coefficient recipe. The matrix-switch coefficients, initial coordinates and safe radix/height constants are fixed coefficient ports in the emitted grammar, not supplied existential witnesses. Arbitrary values of those ports need not describe a program. The switch matrix itself depends on the program; the repeated LOAD/TILE alphabet and the complete finite controller do not. No variable matrix product, arbitrary context-length expansion or external Pell index is hidden in the interface.

## 1. Exact right-action identity before context absorption

Use the original complete [Gamma1(5) recoding](matrix193_gamma1_recode.md), before [context absorption](matrix193_context_absorption.md). Let the original upper blocks be

    A_i : H_i,       B_i : G_i^(-1),       C : C0.

There are 96 fixed pairs. Every displayed matrix belongs to the inherited group H', whose first-row map is injective. Define once and for all

    K_i = C0^(-1) H_i C0.

These matrices depend only on the original fixed tile table. For a selected program, its finite context words U,V give fixed matrices

    L = Psi(V#)^(-1),       R = Psi(U)^(-1).

The ordinary-input target is L B0^(-x) R, where the fixed even block is

    B0 = [[-52109,29036],[-94920,52891]].

Start two signed rows at

    X = e1 L^(-1) C0,       Y = e1.

Use the following macro controller:

1. At hub 0, repeat the fixed LOAD action Y -> Y B0^(-1), leaving X unchanged.
2. Apply exactly one SWITCH action Y -> Y R, leaving X unchanged, and move to hub 1.
3. At hub 1, repeat any fixed synchronized tile action (X,Y) -> (X K_i,Y G_i), and optionally an identity IDLE.
4. End at hub 1 with X=Y.

For a tile word s, exact right multiplication gives

    X_final = e1 L^(-1) H(s) C0,
    Y_final = e1 B0^(-k) R G(s),

where k is the number of LOADs. Both represented matrices lie in H'. Therefore first-row equality is equivalent to

    H(s) C0 G(s)^(-1) = L B0^(-k) R.             (1)

The unchanged lower-marker theorem identifies the left side with precisely the upper block of A_s C B_reverse(s). Thus, when k=x, (1) is the original directed193 membership predicate. The empty tile word is included and corresponds to the single central generator, not an empty semigroup product.

The use of L^(-1) on the left is essential. It changes the initial row while commuting past no tile matrix. The right context R is applied at the switch, before all G_i actions. This avoids the context-dependent conjugated tile alphabet of the previous absorbed construction. No commutativity assumption or change of multiplication convention is used.

The original unary initialization theorem supplies appropriate fixed U,V for each selected program and ordinary positive input x. Its inherited hypotheses remain in force. Only those fixed contexts are evaluated into coefficients. No arithmetic preprocessing of the varying x is introduced.

## 2. One fixed controller and one non-shear switch

Expand the fixed 97 paired actions—96 tiles and one LOAD—into signed unit shears, using finite integer Euclidean reduction. This expansion is performed once on the original table. Give each macro its own private path. Mark the first edge ID of the LOAD path. Add one SWITCH edge 0->1 and one hub-1 IDLE edge; all internal states are private. The controller has n edges, with a power-of-two lane bound m at least n and larger than every state code. Start and terminal hubs are 0 and 1.

The switch is not expanded into a program-dependent shear word. It has physical label 0 for the ordinary eight shear selectors, and a separate edge-ID selector for the matrix correction below. IDLE has label 0 and no correction. Private-path chronology forces LOAD* SWITCH TILE*, with IDLEs allowed at hub 1. In particular exactly one switch occurs. A marked physical letter would not suffice; the marked LOAD edge ID is what counts complete LOAD macros.

Intermediate unit-shear states need not represent elements of H'. The row-injectivity argument is applied only at the macro endpoint, where the exact fixed matrix products give membership in H'.

Choose fixed integers

    Hfix >= m,   Hfix > max absolute initial signed coordinate,
    K a power of two, K >= 16,
    K > 1 + max(|R00|+|R10|, |R01|+|R11|).

Compute, from ordinary x and one positive height slack,

    D = x + Hfix + height_slack,
    c0 = D-1,       B = K D.

K and Hfix may grow with the fixed context coefficients; their magnitudes do not change the emitted operation count. Their recipe is finite and uses no input-dependent choice. B>m and the initial shifted coordinates lie strictly between 0 and 2D before native typing.

## 3. Ten physical selection lanes and eight range lanes

Retain positive edge hats Ehat_e and compute

    E_e=Ehat_e-1,  J=sum E_e,  P=(B-1)J+1.

Let E_sw be the distinct SWITCH edge word. Retain the eight unit-shear selectors S_1,...,S_8 and their selected-source words Z_1,...,Z_8. Supply two additional positive hats for Z_sw0 and Z_sw1, intended to select the shifted Y0 and Y1 coordinates at the switch. The ten physical mask lanes are

    S_1,...,S_8,E_sw,E_sw,

and the ten selected-output lanes are

    Z_1,...,Z_8,Z_sw0,Z_sw1.

Put

    Hb8=(1+P)(H1+P² H0+P⁴ H3+P⁶ H2),
    Hb10=Hb8+P⁸ H2+P⁹ H3,
    Mb10=(B-1)(sum_(l=1)^8 S_l P^(l-1)+E_sw P⁸+E_sw P⁹),
    Zb10=sum_(l=1)^8 Z_l P^(l-1)+Z_sw0 P⁸+Z_sw1 P⁹,
    C=sum_(e=0)^(n-1) E_e P^e,
    O=J R_m(P), O8=J R_8(P),
    T=P^(m+10), T2=P^(m+18), M8=(2D-1)O8,
    H=Hb10+P^10 C+T Hb8+B T2,
    M=Mb10+P^10 O+T M8+T2,
    Z=Zb10+P^10 C+T Hb8,
    q=32 B T2.                                      (2)

The range block remains eight lanes because Hb8 already contains all four history fields. The two switch selections only enlarge the physical block. The controller is shifted by P^10, and its top is below T; the eight-lane history-range block ends below T2.

Bind the same 63-row native cone as in [marked-loader packing](matrix193_marked_loader_packing.md) to q, 16H+13, 16M+10, 16Z+8, P, and the joint bound

    G=sum_i H_i+sum_(the ten hats) Zhat+bound_global.

The native product includes G-P. All twelve independent native ports and every native factor remain present. At a full positive integer zero the final sum-of-squares multiplier is 1, all outer residuals vanish and the native product is 1. Its integral factors are signs. The joint bound gives P>=14, and each history or unshifted selected word is below P. Nonnegative edge words then give J>=1 and B<=P.

The old inequality sum S_l<=J does not hold for the enlarged set: the switch occupies two lanes. The required scalar bounds are instead proved lane by lane. Each of the ten selectors is at most J, so each mask lane is at most (B-1)J=P-1 and Mb10<P^10. Likewise Hb10,Zb10<P^10, C<P^m, and (2D-1)J<P. Hence the bodies of H,M,Z below their top terms are all below T2, exactly as needed for the inherited positive truth-field argument. The four truth fields remain positive with residues 1,4,2,8 modulo 16 and sum q-1.

The unchanged tail bootstrap therefore recovers the positive unit signs and dyadic q. Equation (2) makes B and P dyadic. Since K is a fixed power of two, D is dyadic; the computed repunit gives P=B^t for an integer t>=1. The joined AND now separates the ten physical lanes, m controller lanes and eight range lanes. All ten selected-source words have their intended meaning, the controller is one-hot, and the range digits satisfy

    0<=X_i(j)<=2D-1,     -(D-1)<=X_i(j)-c0<=D.       (3)

## 4. Paid switch correction and chronology

Let delta_i^unit denote the usual signed unit-shear increments. The matrix switch requires only the following extra source:

    shift = c0 * E_sw;                             # 1M
    u = Z_sw0 - shift;                            # 1A
    v = Z_sw1 - shift;                            # 1A
    p0 = (R00-1) * u;                             # 1M
    p1 = R10 * v;                                 # 1M
    correction0 = p0+p1;                         # 1A
    p2 = R01 * u;                                 # 1M
    p3 = (R11-1) * v;                             # 1M
    correction1 = p2+p3;                         # 1A
    delta_2 = delta_2^unit + correction0;          # 1A
    delta_3 = delta_3^unit + correction1.          # 1A

This is 11=5M+6A operations. R00-1 and R11-1 are fixed coefficients prepared by the program recipe. The two other coordinates keep their unit increments. No determinant division or dynamic matrix inverse is used. At the unique switch cell the unshifted selected values u,v are precisely Y0,Y1, so the two corrections equal YR-Y; away from that cell they vanish.

Retain four history comparisons

    B(H_i+delta_i)=H_i+F_i P-I_i,

with I_i=c0+initial_i and shared positive terminal fields F_even,F_odd. Retain the weighted open-end controller flow and marked LOAD population comparison. There are still six comparisons and the same 20-gate finalizer.

To justify coefficient recovery, a matrix-switch discrepancy in a coordinate is at most

    (max column absolute sum of R +1)D < K D=B

in absolute value, once preceding digits have been recovered. Unit-shear and identity discrepancies are also below B because K>=16. Initial discrepancies are below 2D. Reduction modulo B therefore recovers chronology cell by cell, including the non-shear switch. The final coefficient forces the actual terminal values; no independent final range bound is required.

At the typed pre-state of the compulsory switch, Y=e1 B0^(-k). The switch may itself apply R; it need not be a separate identity edge. Its pre-state is still stored and typed. The first coordinate obeys a0=1, a1=52891 and a(k+2)=782a(k+1)-a(k), hence a_k>=k+1. Equation (3) gives k<D. The marked edge word E_load satisfies

    (B-1)Q=E_load+(B-1)-x,

so k is congruent to x modulo B-1. Since 0<=x<D<B-1, this forces k=x. Thus the exact right-action theorem (1) has the required ordinary input.

## 5. Positive completeness

Given a genuine finite accepted tile word, run exactly x LOADs, the switch, that tile word and optional IDLEs. Choose a power-of-two D above x+Hfix and every absolute coordinate of the finite shear-expanded trajectory, including the switch output and endpoint, plus one. All history and shared terminal fields become positive after shifting. Choose the exact radix-B edge and selection words.

At any cell at most two physical selection lanes are active. Thus

    sum H_i+sum Z_l <= (12D-6)J,
    bound_global=P+1-sum H_i-sum Z_l-10
                >=((K-12)D+5)J-8 >0.              (4)

The population quotient is again

    Q=1+sum_(marked cells j)(B^j-1)/(B-1)>0.

The controller, all six comparisons and the joined AND hold. The inherited converse supplies fresh positive native witnesses at the exact q in (2). This proves equality of positive-zero input projections; it does not assert equality of native witness tuples or polynomial identity with the old packing. Zero input and an empty tile suffix retain the same meanings as in the parent; ordinary positive input is obtained by restricting x>0.

## 6. Uniform resource schedule

The construction has n+31 positive existential witnesses: n edge hats, four history fields, ten selected-source hats, twelve native coordinates, one height slack, one joint-bound slack, two shared terminal fields and one population quotient. This count is independent of duration and of program context length.

Relative to the previous conservative 9n+3log2(m)+210 schedule, the ten/eight layout adds at most sixteen packing operations: P^10 needs one product; Hb10 adds four gates; the physical-mask extension adds three; Zb10 adds four; two hat decrements add two; and the joint sum adds two. Its matrix-switch correction adds eleven. The complete conservative bound is therefore

    9n+3log2(m)+237.

Both SWITCH and IDLE are absent from the eight ordinary shear-selector sums, so the predecessor's grouping bound still applies. The two duplicated switch selectors are explicitly charged in the extra physical-mask expression. Fixed coefficient multiplications are paid even though the coefficients depend only on the selected program. Shared products and zero coefficients may reduce a numerical fixture but are not required for the uniform bound.

The guarded degree calculation also transfers. For the computed-P grammar,

    deg q=2m+37, deg F3=2m+35.

The unchanged seven native leaders and a degree-six outer sum of squares give exact degree 72m+1357 when all supplied ports remain independent. The terminal field times P yields a nonzero outer cubic leader, so arbitrary legal context coefficients cannot cancel the square sum. The other highest forms remain nonzero through the independent native coordinates and positive fixed K. This is a polynomial degree statement in input and existential coordinates, with coefficient ports fixed at valid program numerals.

## 7. Authenticated fixed table and emitted grammar

The separately frozen [unit-shear controller](matrix193_unit_shear_controller.md) supplies 97 original-table macros, 19,611 unit steps, 19,613 total edges, 19,516 states and m=32,768. Its source/receipt/note pins are respectively:

    a1023d53f49a087c1861a67ceeb1a5c7de46ee59bccf62acaa49cacb8c2f1866
    9c48903d2bb227169d9984d24230e9dfcd46cf03b89511bf29dd0347284c9cbc
    303ae00247cf5d05f6509e86ca2acf520b7354541a493d41442ccebef11dad59

In addition to reading that complete proof, a fresh data-only check reconstructed all 193 original matrix factorizations from the pinned Gamma1 array, multiplied every one of the 19,611 unit steps, and checked the full private-path edge table and distinct internal states. No factorization helper was imported or executed for that independent check. The resulting generic construction bound is 176,799 operations with 19,644 positive witnesses and exact degree 2,360,653.

The new emitter uses precisely eight fixed coefficient ports:

    initial_X0, initial_X1,
    R00_minus_one, R10, R01, R11_minus_one,
    radix_multiplier, Hfix.

A valid program recipe supplies the two entries of e1 L^(-1) C0, the four indicated entries of R, and the constants K,Hfix required in Section 2. They have polynomial degree zero and are excluded from the existential-witness count. Their values may have arbitrarily many bits as the program varies; no uniform coefficient-height bound is claimed. The source performs each fixed-coefficient multiplication at its listed gate. The same instruction array is used for every valid coefficient specialization, even if some specializations admit additional zero/one simplifications.

The frozen receipt emits both complete arrays:

| Array | n,m | Complete paid gates | M,A | Positive witnesses | Exact degree |
|---|---|---:|---|---:|---:|
| Small matrix-switch diagnostic |6,8|274|113M,161A|37|1,933|
| Fixed original-table grammar |19,613;32,768|176,586|58,770M,117,816A|19,644|2,360,653|

The optimized emitted ledger is smaller than the conservative construction bound. It counts all packing, fixed coefficients, native factors, six comparisons and the finalizer. Its stages are 98,201 packing gates, 63 native gates, 78,302 outer producers and 20 finalizer gates. The diagnostic stages are 130,63,61,20. All source rows and coefficient/input/witness ports are structurally live in the parameterized grammar. This does not claim that every numerical specialization is operation-minimal.

The diagnostic has initial X=(2,1), Y=(1,0), switch R=[[2,1],[1,1]], LOAD Y1-=Y0, and the three-shear TILE word labels 2,4,1. After x LOADs and the switch, Y=(2-x,1-x). A TILE changes X=(2-j,1-j) to (1-j,-j), so x TILEs reach equality. It therefore accepts every natural input and is deliberately not a universal-program example.

The original-table recipe is different: the inherited unary initialization selects valid program contexts, and Sections 1–5 prove the exact ordinary-input language for each such coefficient instance. The actual saved contexts remain an illustrative machine fixture. The finite checks below are not treated as native positive Pell witnesses; the unbounded projection theorem is proved in Sections 1–5.


## 8. Frozen source, evidence and reproduction

The complete [source](matrix193_uniform_context_packing.py) and [receipt](matrix193_uniform_context_packing.json) are pinned at:

| File | SHA256 |
|---|---|
| `matrix193_uniform_context_packing.py` | `db6c6789fcc55bace75a8a4fd5b51cd474a6899c480f7eef34e8d538a2c76b5e` |
| `matrix193_uniform_context_packing.json` | `3515e9d99da7f744d3dff2f46c6f63c3ce50d063df4f8f090dd3d3213fcc307e` |

All twelve declared predecessor source/data/proof pins are strict and were independently authenticated. The helper reads predecessor JSON and proof bytes but imports or executes no predecessor Python. It regenerates both complete arrays, checks closure and structural liveness, and recounts all fixed-coefficient operations and witnesses.

There are 32 whole-source modular comparisons, sixteen for each graph over two primes. Separate direct formulas check the scalar packing values, seven native factors, six outer residuals and final output. Half the tests in each modulus use the declared numerical fixture coefficients; the others also vary the fixed ports off the program recipe to test algebra. Those tests are all-value implementation diagnostics, not soundness claims for arbitrary coefficient ports.

Ten fully materialized small diagnostic outer histories use x=0,1,2,3,4 and either zero or two IDLEs. They verify all six exact comparisons, all positive outer witnesses, the joined bitwise AND and the positive native truth fields. No native positive Pell tuple is materialized. The actual original-table accepted matrix trajectory is checked in the factorization packet; its enormous joined packed history and native extension are not falsely reported as materialized here.

A full dense coefficient expansion of the diagnostic along the recorded affine line has exact degree 1,933 and leading coefficient 91,995,320 modulo 1,000,000,007. The full original-table degree 2,360,653 uses the uniform homogeneous proof in Section 6, not a sampled large polynomial or a dense expansion. The raw gate-propagation bounds, 1,987 and 2,426,227, are retained in the receipt and distinguished from the exact degrees.

The complete helper and this companion proof were cross-read. The independent source review is separate from the proof-only challenge of the right-action, switch-range and positive-extension arguments. Neither finite evaluation nor a review message replaces the inherited native converse or the fixed-program initialization theorem.

With the pinned predecessors installed, the frozen CLI is:

    python3 /absolute/path/matrix193_uniform_context_packing.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/matrix193_uniform_context_packing.json

The mutually exclusive `--output FILE` regenerates the receipt. During staging, `--factor-root DIRECTORY` selects the same strictly pinned factorization receipt; it is not an unpinned replacement table. Fresh normal and optimized exact replays from `/` both passed. All substantive checks use explicit exceptions and remain active under `python3 -O`.
