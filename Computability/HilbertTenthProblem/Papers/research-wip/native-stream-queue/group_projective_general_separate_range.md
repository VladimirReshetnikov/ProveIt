# A general paid eight-lane range transfer

For the canonical computed-P projective compiler, a separate eight-lane history range and the unit top mask never increase the complete arithmetic count relative to the reused-m-lane, top-mask2 source. They lower its exact degree by `58(m−8)` under the explicit free-coordinate hypotheses below. The controller can branch arbitrarily; inverse closure is needed only for a subgroup interpretation of its macro table, not for this source transformation.

The [helper](group_projective_general_separate_range.py) and [receipt](group_projective_general_separate_range.json) emit seven complete arrays from actual saved predecessors. They authenticate54 dependency files, read saved JSON and execute no historical Python, compiler or test suite. All predecessors remain unchanged. This packet gives a general arithmetic transfer and seven concrete audits, **not a numerical universal improvement from this transformation**.

| Complete source | Padded m | Certificate | Full polynomial | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| Inverse private controller |64|475|492=191M+301A|74|5821|
| Exact-language shared controller |32|415|432=178M+254A|56|3517|
| Nielsen private controller |32|354|371=150M+221A|54|3517|
| Folded inverse controller |32|359|376=147M+229A|54|3517|
| Earlier private m8 controller |8|218|235=98M+137A|34|1789|
| Earlier shared m8 controller |8|212|229=97M+132A|33|1789|
| Ten-letter tail source |16|227|244=103M+141A|36|2365|

Every row retains six comparisons and the same seventeen-gate finalizer, costing6M+11A. The four inverse parents come from [inverse macro sharing](group_projective_inverse_macro_sharing.md); the two m8 parents from [shared macro automata](group_projective_shared_macro_automaton.md); and the m16 parent from [the tail quotient source](group_projective_tail_quotient_shift.md). Their historical degrees were9069,4909,4909,4909,1789,1789,2829 respectively. No claim is made that these seven graphs form a search census or that their counts are optimal.

## 1. Family hypotheses and the retained input margin

Fix a finite nonempty directed controller with n nonidle edges, physical labels in1..8, injective edge lanes and `1≤n≤m`, where m is a power of two at least8. Its state codes must fit the existing paid radix margin; canonical renumbering with codes below m suffices. The source must use the correct general weighted flow for branching graphs. The sparse private-path formula is not a valid replacement merely because a graph is finite.

Use the canonical positive edge hats, computed checksum `J=sum_e(edge_hat_e−1)`, computed `P=(B−1)J+1`, four independent positive history fields H0..H3 and the eight canonical selected-source hats. Retain the full joint bound, the tail-shifted native kernel, every positive native coordinate and all five outer residuals. In particular no coordinate is identified, specialized, removed or constrained to be a newly positive intermediate by this transfer. The fixed ordinary-input prefix and height remain

    u=alpha*x+gamma, D=u+height_slack, B=16D,

with fixed positive alpha,gamma and positive ordinary x and height_slack. A sufficient fixed-data test is

    16*(alpha+gamma+1)>m.

This proves B>m before native typing. In all seven literal sources alpha24,gamma13 give B≥608, covering m≤64. The older stronger table-margin test is not silently applied to the m64 example.

For a different table failing this fixed-data test, its margin must still be paid or proved. Retaining `D=u+height_slack+m` costs one additional addition and gives the margin directly. Alternatively, the particular [padded universal enumeration](group_projective_padded_program_margin.md#4-one-explicitly-padded-universal-enumeration) chooses equivalent fixed program numerals after its fixed alphabet and m have been constructed. The present transfer changes neither that program-selection theorem nor the already-paid height mechanism. It does not remove D>u or replace an arbitrary enumeration by an assumed padding property.

## 2. Complete operation change

Write `R_k(P)=1+P+...+P^(k−1)`. The canonical reused-range parent already pays for P8,R8,Pm,Rm and

    O=J*R_m(P), T=P^(m+8), T2=T*P^m=P^(2m+8).

The controller keeps O and T. The successor uses

    O8=J*R_8(P), T2=T*P^8=P^(m+16)

only for the history-range mask and its scale. Reuse an existing O8 multiplication if available; otherwise add exactly one. The private top-mask2 row `range_Bminus_shift=2*T2` is deleted and its sole consumer uses T2 directly, as justified by the [unit-top-mask theorem](group_projective_unit_top_mask.md).

Pm remains live in T and Rm in O. P8 and R8 were already paid by the physical eight-lane construction. No uncharged power or repunit is introduced. Therefore

    delta_M=−1+indicator(J*R8 was not already paid)≤0,
    delta_A=0.

For m8, O8 is O and the complete source saves1M. For each of the five larger saved sources, the new product costs1M and exactly offsets the deleted top product. The checker proves closure and liveness of every entire emitted array, including the ordinary input and finalizer. This is a cost theorem for the stated literal source grammar, not a lower bound against other compilers.

## 3. Exact scalar interfaces and positive-domain transfer

Let Hb,Mb,Zb denote the canonical physical history, selector mask and selected-source word; let C denote the controller edge word. The new complete joined scalars are

    O=J*R_m(P), T=P^(m+8), T2=P^(m+16),
    M8=(2D−1)*J*R_8(P),
    H=Hb+P^8*C+T*Hb+B*T2,
    M=Mb+P^8*O+T*M8+T2,
    Z=Zb+P^8*C+T*Hb,
    q=32*B*T2.

The helper proves these as exact integer coefficient polynomials from each literal source. It also proves the entire checksum polynomial and physical history polynomial, then compares every retained register after treating the three explicitly changed scalar ports as common cuts. All comparisons and all finalizer instructions agree literally. This is a complete interface proof; the old and new whole polynomials are **not** equal on the same arbitrary supplied tuple.

At a positive full zero, the unchanged output is

    U*(1+R0²+R1²+R2²+R3²+Rflow²)−1.

It forces all outer residuals to zero and every integer unit factor to a sign. The unchanged joint bound gives P≥12 and bounds each history field and unshifted selected-source word below P. The nonnegative edge words and computed repunit then force J≥1 and B≤P. The literal height prefix proves B>m independently of any native interpretation.

The physical words lie below P8; `0≤C≤J*R_m(P)<P^m`; and `(2D−1)J<P`. Thus the separate eight-lane mask and history occupy less than P8 at their position, so

    H=H0+B*T2, M=M0+T2, Z=Z0,
    0≤H0,M0,Z0<T2.

In particular

    H−Z≥(B−1)T2+1,
    M−Z≥1,
    2B*T2−H−M+Z≥(B−3)T2+2.

The four actual native truth fields

    q−16H−16M+16Z−15, 16(H−Z)+4,
    16(M−Z)+2, 16Z+8

are strictly positive, sum to q−1 and have residues1,4,2,8 modulo16. The [tail bootstrap](group_projective_tail_quotient_shift.md#3-native-recovery-including-both-index-signs) consequently applies with its original order of hypotheses: both index signs are treated before recovery of the large X bound. It forces every native/joint factor to1 and q to be dyadic. From `q=32B*P^(m+16)` and the computed repunit, B and P are dyadic and `P=B^t` for an integer t≥1.

Now the joined AND separates into its physical, controller, range and top blocks. The top unit mask is valid because `B AND1=0`. Since P is dyadic and `(2D−1)J<P`,

    ((2D−1)*J*R_m(P)) mod P^8
      = (2D−1)*J*R_8(P).

As Hb<P8, the reused-range equation `Hb AND mask=Hb` is equivalent to its eight-lane version. Physical and controller blocks are unchanged. Hence the existing one-hot typing, correct general flow, selected-source equations and retained height bound recover exactly the same chronological projective histories.

Conversely, retain all outer coordinates of a positive zero of either source. Its recovered dyadic data satisfy the other range recipe by the low-eight identity and both top masks because `B AND1=B AND2=0`. The displayed bounds give positive native truth fields at the changed q. The prescribed native converse, followed by the tail-coordinate construction, supplies fresh positive native coordinates. The joint bound and all outer equations remain true.

This proves equality of the complete positive-zero projections onto the ordinary input and all retained outer history/controller/height/global-slack coordinates. It proves the same unbounded represented input relation for each fixed valid controller. It does not give a full native-witness bijection, a signed-zero theorem or a polynomial identity between the old and new joined kernels.

## 4. Exact degree and its specialization boundary

Every supplied coordinate, including x, has degree1. All fixed graph labels, lane positions, state codes and compiler numerals have degree0. This section concerns the canonical computed-P family with independent supplied coordinates and the literal physical packing; it does not assert exactness after arbitrary further variable specialization.

Let a_scale be `2m+8` in the old reused-range source or `m+16` in the new separate-range source. Put

    Q=1+2*a_scale, F=1+2*(m+15), R=3Q+F.

The checksum leader `J*=sum_e edge_hat_e` is nonzero because the graph is nonempty. Let `D*=alpha*x+height_slack`, `B*=16D*`, and `P*=B*J*`. These are nonzero at every fixed positive alpha. In the actual physical packing,

    Hb=H1*(1+P)+H0*(P²+P³)+H3*(P⁴+P⁵)+H2*(P⁶+P⁷),
    Hb*=(P*)^7*H2.

Consequently the unique highest term of F3 is

    F3*=16*(P*)^(m+8)*Hb*,
    q*=32*B* (P*)^a_scale.

The competing controller and physical terms have lower degrees. These leaders have positive coefficients, so fixed lane or macro choices cannot cancel them. Q>F, including `Q−F=2` for the separate-range source. With the independent native ports `s*=2*odd_half`, `k*=eta+zeta`, the tail-shifted source has

    X*=(q*)²*F3*, a*=s*(q*)³*F3*, c*=k*s*q*.

Its seven nonzero unit leaders are the literal ones proved in [the tail degree argument](group_projective_tail_quotient_shift.md#5-exact-degree-with-no-on-zero-substitution):

| Unit | Highest homogeneous form | Degree |
|---|---|---:|
| First | `4(a*)(c*)(g−k*)` |R+Q+4|
| Main | `8*ga*(a*)²*c*` |2R+Q+5|
| Auxiliary | `i²*(c*)⁶` |6Q+14|
| Index | `−h*a*` |R+2|
| Linear | `−2h*a*` |R+2|
| Strong | `−(a*)²*f²` |2R+4|
| Joint bound | `−P*` |2|

Here g is the supplied `selection__tau_gap`; ga is the separate supplied main-root slack. In particular `g−eta−zeta` is not the zero polynomial. The main leader uses only the all-value identity

    (X+ac+gamma)^2−(a²+4a+3)c²
      =X²+2Xac+2Xgamma+2acgamma+gamma²−(4a+3)c².

The helper checks every actual gate in this cone before applying the degree cancellation. It never substitutes a unit equation or a power identity that holds only on zeros.

The four history residuals have degree3 leaders `−B*D*(dS_i*+J*)`. For an edge with physical label l, its hat coefficient in `dS_i*+J*` is

    1+indicator(l=2i+1)−indicator(l=2i+2).

Three of these four coefficients are1. Thus at least one history leader is nonzero for every nonempty fixed graph, regardless of its label distribution or lane order. The sum of their squares is nonzero over the reals. The flow residual has degree at most2 and cannot cancel this degree6 sum. The product of the seven nonzero unit leaders is nonzero in the polynomial ring. Therefore the complete finalizer has exact degree

    73+2*(29*a_scale+7m+106),
    old: 130m+749, new: 72m+1213,
    exact decrease: 58(m−8).

This establishes uniform exactness for the stated independent-coordinate source family, not just the seven benchmarks. Fixed numerical graph data cannot remove the positive checksum/history leaders. If supplied coordinates are subsequently identified, eliminated or specialized, this noncancellation argument may cease to apply; the corresponding propagated degree bound remains an upper bound, and exactness requires a new proof. Supplied-P or differently optimized native kernels are outside the emitted family here.

For each of the seven full literal arrays, the receipt additionally records a weighted-indeterminate homogeneous-component witness modulo1000000007. Its nonzero coefficient at the guarded upper degree independently certifies attainment for that fixed-numeral source. These finite certificates supplement the family argument rather than infer it from examples.

## 5. What remains before a numerical universal matrix table

The present arithmetic transformation applies to any actual fixed controller satisfying the preceding hypotheses. The earlier [commutator construction](group_commutator_universal_substrate.md) and [projective matrix interface](group_projective_zero_mortality6.md) give a route from one fixed universal c.e. set to such a finite alphabet, but the repository has not executed its finite-presentation embedding on a concrete universal enumerator.

The missing compiler data are a finite presentation `H0=<Y|R>` together with words A0(Y),B0(Y) giving the injective images of the two recursive-presentation letters. A general explicit construction exists: Mikaelian’s Algorithm1.1 builds the finite overgroup and named embedding from a recursive presentation, using its sequence construction, finite Higman-operation description and recursively assembled benign pairs. Its optional final step yields a two-generator finite presentation. This is an effective route, not a small output-size promise. [Mikaelian, Algorithm1.1](https://arxiv.org/html/2507.04347v8).

Once those actual words exist, adjoin fresh named a,b with relations `a=A0,b=B0`. The finite fibre-product generators are `(z_i,z_i)` and `(1,R_j)`; conjugate by `(a,1)` to obtain `(a z_i a^-1,z_i)` and `(1,R_j)`, then include inverses. This finite-generation recipe has no asphericity hypothesis; the additional hypotheses in the cited paper concern its later recursive-presentation result. [Bogopolski–Ventura, Section1](https://arxiv.org/pdf/0810.0690).

The frozen matrix interface then replaces the four free letters by its explicit fixed shear words, reflects the matrices to the current projective convention and supplies the affine ordinary-input decoder. One may perform proved generator changes or inverse-graph folds, choose the actual n,m,state codes and lane assignment, and enforce the margin from Section1. Only then can an actual complete universal source be counted with this range transfer.

Thus the current barrier is the **unexecuted finite presentation and named-word output for that particular universal recursive presentation**, followed by its explicit finite word expansion. It is not a lack of an embedding algorithm or a missing unbounded-history theorem. An arbitrary group with undecidable word problem would not by itself supply the exact commutator/input contract. Neither the existence theorem nor this general degree formula supplies a numerical universal alphabet size, a competitive operation count or new ordinary-input loader for free.

The four inverse benchmarks retain their known proper, nonempty predicate; the earlier m8 fixture retains its empty positive-input relation. These are source audits, not additional universal examples. No complete native Pell zero is materialized in this packet. Native extension is the proved component converse, and computation length remains existential rather than an external horizon.

## 6. Reproduction and finite evidence

The saved receipt contains all seven complete sources, coordinate domains, comparison lists, old-source hashes, current ledgers and degree certificates. It verifies2,379 live paid gates;61 exact scalar polynomials;14 exact checksum/history polynomials;2,374 retained-register identities under the explicitly changed interfaces;42 comparisons; and all seven finalizers. It evaluates35 full outputs, including14 rational tuples, and checks150 typed low-eight range cases plus180 scalar positivity cases without assuming binary typing. Eight literal physical-label coefficient checks support the general nonzero outer leader argument.

The m8 sources equal the frozen unit-top-mask sources instruction for instruction. The Nielsen separate8 source likewise equals the frozen [nonempty mask source](group_projective_nonempty_mask_frontier.md), whose [independent review](review_group_projective_nonempty_mask_frontier.md) checked actual accepted outer histories and the positive transfer. No new historical suite is rerun here.

Run from any working directory:

    python3 group_projective_general_separate_range.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/to/group_projective_general_separate_range.json

Use `--output` to write the deterministic receipt. Each execution authenticates every pinned dependency anew, preferring the specified root and using the script directory only when a relative root file is absent. The receipt pins the current helper bytes. This is a bounded standalone source/proof CLI, not a maintained arbitrary-graph or hostile-packet API.
