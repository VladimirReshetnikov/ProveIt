# Corrected 2-tag candidate: exact bounded semantic contract

This is a new, explicitly specified compiler schema and proof sketch, supported by independent small tests. It is not a claimed certified transcription of every printed Cocke–Minsky rule, a finished numerical Grill table, or a measured universal polynomial.

## 1. Frozen input convention and U15 control

Use the fixed 15-state, 2-symbol U15 table from the repository's audited `neary_woods_explicit_universal_tm.md`, with c=0 and b=1. Its only missing instruction is (u10,b). Refine each control into an already-read state i=(u,a), numbered 2(u-1)+a. There are 30 such states, of which h=19=(u10,1) is accepting. Start i0=0=(u1,0).

If the ordinary U15 instruction is (u,a)->(v,s,D), the refined state i writes s, moves D, then selects j_r=2(v-1)+r after reading the new square r. All 29 nonaccepting refined states have one such instruction. This finite state refinement changes no tape or head move. Acceptance occurs on entering h, before another write or move.

External input is x>0. Pay u=x+1 and use its canonical LSB-first bits w0,...,w(n-1), with n=bit_length(u)>=2. For each c.e. set S, choose the finite represented program to decode this LSB-first positive integer, subtract one, and recognize S. This is a fixed semidecider for S; it is not an external algorithm applied to each x.

The U15 head is on the final c of the fixed `bc` start marker. With A_i=(01)^(8i-5)11, its ordinary input bit blocks are B0=A2 A1 and B1=A1 A2, both length 32. To the head's right is

    R_e(w) = P_e B_w0 ... B_w(n-1) S_e,
    P_e=(01)^(8 q_B), S_e=A_right A_left.

To the left is the finite program word followed by b. Everything outside these finite words is blank 0. Define M_e as the LSB-first value of the left word reversed, so that the square nearest the head is its low bit. Define N_e(x)=val_LSB(R_e(w)). The scanned 0 is omitted from both integers, since i0 remembers it. N_e(x)>0: S_e ends in 11. M_e is constant for the represented program, while N_e(x) is paid below.

This uses the primary machine's finite-tape convention, not weak universality on an infinite periodic background. The repository's finite U15 initialization theorem is the imported universality premise. The present pass specifies how to adapt its represented semidecider's bit order; no new claim about the malformed-input behavior of U15 is needed.

## 2. A complete right-move macro

For each refined nonhalt state i create canonical symbols A_i,a_i,B_i,b_i,xi_i and internal symbols C_i,c_i,S_i,s_i,D_i0,D_i1,d_i0,d_i1,T_i0,T_i1,t_i0,t_i1. The canonical configuration is

    C(i,M,N)=A_i xi_i (a_i xi_i)^M B_i xi_i (b_i xi_i)^N.

Every displayed tag step deletes two symbols and appends the production of the first. Suppress subscript i on internal symbols. If i writes epsilon in {0,1}, moves right and selects successor j_r on bit r, prescribe

    A_i -> C xi_i (c xi_i)^epsilon
    a_i -> c xi_i c xi_i
    B_i -> S                   b_i -> s
    C -> D1 D0                 c -> d1 d0
    S -> T1 T0                 s -> t1 t0
    D1 -> A_j1 xi_j1            d1 -> a_j1 xi_j1
    D0 -> xi_j0 A_j0 xi_j0      d0 -> a_j0 xi_j0
    T1 -> B_j1 xi_j1            t1 -> b_j1 xi_j1
    T0 -> B_j0 xi_j0            t0 -> b_j0 xi_j0.

Put M'=2M+epsilon. The successive exact queue cuts are

    B_i xi_i (b_i xi_i)^N C xi_i (c xi_i)^M'
    C xi_i (c xi_i)^M' S s^N
    S s^N D1 D0 (d1 d0)^M'.

If N=2k+1, processing S and every other s leaves

    D1 D0 (d1 d0)^M' T1 T0 (t1 t0)^k,

which becomes

    T1 T0 (t1 t0)^k A_j1 xi_j1 (a_j1 xi_j1)^M',

then exactly C(j1,M',k).

If N=2k, the final deletion while processing S/s also consumes D1, leaving

    D0 (d1 d0)^M' T1 T0 (t1 t0)^k.

Processing D0 and d0 consumes T1 at its last deletion (including M'=0), leaving

    T0 (t1 t0)^k xi_j0 A_j0 xi_j0 (a_j0 xi_j0)^M'.

The last T0/t0 deletion consumes the extra xi_j0, giving exactly C(j0,M',k). This includes k=0. Thus the macro exactly performs (i,M,N)->(j_(N mod2),2M+epsilon,floor(N/2)).

### Primary source discrepancy, not an asserted author erratum

The manually inspected image of printed p.19 displays t0->beta0, with no xi0, while its next displayed configuration has paired (beta0 xi0) repeats. The image is preserved in `cm-page5.png`; printed p.18 is `cm-page4.png`, and the original six-page PDF is preserved too. This is not based on OCR alone.

On M=0,N=2,epsilon=0,right, the printed production gives A_j0 xi_j0 B_j0 xi_j0 b_j0 after ten tag steps. The claimed target has one further xi_j0. The new schema explicitly uses t0->b_j0 xi_j0. The preceding parity calculation proves this corrected local macro independently; it does not silently attribute a corrected table to the paper. All productions still have length at most four.

## 3. Explicit left-move macro

For a left-moving state replace only its initial four rules by

    A_i -> L_i xi_i             a_i -> l_i xi_i
    B_i -> C xi_i (c xi_i)^epsilon
    b_i -> c xi_i c xi_i
    L_i -> S                   l_i -> s.

One traversal gives L_i xi_i (l_i xi_i)^M C xi_i (c xi_i)^(2N+epsilon), exactly the right macro's first cut with the tape integers exchanged. Keep the C/c/S/s rules. In D/d outputs replace target A_j,a_j by temporary Bprime_j,bprime_j. In T/t outputs replace target B_j,b_j by actual A_j,a_j. Include

    Bprime_j -> B_j xi_j,
    bprime_j -> b_j xi_j.

The right-macro proof, with M,N exchanged, yields

    Bprime_j xi_j (bprime_j xi_j)^(2N+epsilon)
    A_j xi_j (a_j xi_j)^floor(M/2),

where j=j_(M mod2). Copying the leading prime block to the tail leaves exactly C(j,floor(M/2),2N+epsilon). This explicit finite rotation avoids relying on an unspecified left/right symmetry or an unproved cyclic cut.

## 4. No premature short queue and one accepting event

Every canonical word has at least four symbols. Except for B_i/b_i->S/s (right) or L_i/l_i->S/s (left), all preacceptance productions have length at least two, and cannot reduce queue length. During that only shrinking phase, the untouched C xi_i (c xi_i)^M' has length at least two; when the shrinking phase finishes, at least one S remains as well. Every intermediate queue in that phase therefore has length at least three. Prime rotation preserves length. Thus all rejecting as well as accepting valid runs avoid queues of length below two before the designated accepting event.

In each macro, the exact cuts above create one target A_j (or one A_j behind a prime block in the left case). The target A_j is not read until every old-macro symbol preceding it is consumed. At that moment the queue is exactly C(j,M_next,N_next). In particular, if j=h, the first read of A_h is at a canonical boundary, with no old C/D lineage pending anywhere in the queue.

Define A_h->H, where H is a fresh symbol used nowhere else. Give a_h,B_h,b_h,xi_h the inert production ZZ and give Z->ZZ; arbitrary otherwise-unused filler rules can also be inert. No nonhalt rule emits H. When A_h is read, its suffix contains only xi_h,a_h,B_h,b_h, and their filler copies, none of which can create A_h or H. Exactly one H is emitted, and no second H can be emitted while the remaining original-generation suffix is processed. Conversely, a fresh H requires an actual A_h head read, and the no-short-queue and macro invariants identify this with U15 acceptance.

This concerns emitting a fresh H from the accepting head, not treating an arbitrary occurrence of a tag symbol as acceptance. A symbol in the second deleted position is never treated as a head event.

## 5. Exact Genera normalization and halt convention

Give every original tag symbol width one and set its unnormalized Genera production to its tag production at phase 0 and empty at phase 1. Two FIFO symbol reads are exactly one deletion-2 tag step. The no-short-queue lemma makes this safe on the whole valid input slice. Persistent phase handles generations that end between the two reads.

Introduce a fresh width-zero dummy d with d->dd. Pad every original production to four symbols with trailing d, then replace its two consecutive pairs by fresh pair symbols. Each pair [u,v] has width zero and produces u v at both phases. All productions now have exactly two outputs. H is emitted only when a pair containing H expands.

Erasing d after two normalized generations gives one original generation with exactly its final phase: only the original-symbol layer changes phase; the pair/dummy layer has zero width. The first H generation has exactly one H by Section 4. Its preceding prefix contains only original symbols and d. Their next normalized productions have pair symbols and d, never H. Hence the additional Genera hypothetical-prefix condition is satisfied. This establishes the semantic prerequisites of the corrected Grill halt bridge without weakening its halt convention.

The existing bridge now applies to the exact E word: phase alignment, nonemptiness at all nonhalting E boundaries, and the exact three cleanup lengths and first-empty time are inherited unchanged.

## 6. Finite ordinary-input arithmetic

Let K0=2^32, m0=K0-1. The canonical recoder at width 32 supplies q0=2^n, Q0=q0^32, R0=sum_i bit_i(x+1) K0^i. The literal LSB values of the two physical U15 blocks are

    c0=3941247658, c1=3937053418, c1-c0=-4194240.

Let p_e=2^|P_e|, a_e=val_LSB(P_e), s_e=val_LSB(S_e). Introduce a positive N and pay

    m0 N = m0 a_e + p_e c0 (Q0-1)
             + p_e m0(c1-c0) R0 + p_e m0 s_e Q0.

This forces exactly N=N_e(x). The negative fixed coefficient is retained explicitly; no off-zero positivity of a computed difference is assumed. N is a positive supplied witness, and its genuine value is positive because the literal suffix is nonzero. No leading or trailing source blocks are silently discarded.

### Exact exponent graph, distinct from bit-length selection

Specialize a second complete generic-width recoder, at fixed k>=4, to input 1 and spread output 1. Its full theorem gives h>=2, q1=2^h, B=2^(k-1)q1^k, P=B^h, J=sum_(j<h)B^j. Here h is a new history-independent exponent, not n and not a machine running time.

Add positive ell,v,g with

    (B-1)v+ell=J, ell+g=B-1, ell=N+1.

The range proof is explicit: B=2^(kh+k-1)>=2^(4h+3), and for h>=2 this is greater than h+1. Thus 2<=h<=B-2. Positivity gives 1<=ell<=B-2. Since J is congruent to h modulo B-1, these two representatives in [1,B-2] are equal. There is no modular alias.

Conversely, for every genuine N>=1 choose h=N+1>=2. The complete recoder provides its positive extension, and

    v=sum_(j=1)^(h-1) sum_(i=0)^(j-1) B^i > 0,
    g=B-1-h > 0.

All added coordinates are positive. The h=0 and h=1 cases are excluded by the inherited complete recoder theorem and are not needed on this input slice, because N>0 was proved. An extension to arbitrary N>=0 would use h=N+2 and an explicit nonnegative/positive-offset interface. No dyadic restriction is imposed on h: the dyadic-duration variant's extra low-block AND test is deliberately not used.

### Exact unary E loading

Let b=196(N_G+1) be the corrected E length of one width-one original symbol in the now fixed normalized source alphabet. Set k=2b in the second recoder and K=2^k. Its Q1=q1^k=K^(N+1). Supply positive T and pay K*T=Q1, so T=K^N.

For the fixed program e define the source prefix F_e=A_i0 xi_i0 (a_i0 xi_i0)^M_e B_i0 xi_i0. Let C_e=val_LSB(E(F_e)), L_e=2^|E(F_e)|, and V=val_LSB(E(b_i0 xi_i0)). The exact source word is F_e(b_i0 xi_i0)^N, and its Grill queue is forced by

    (K-1) X=(K-1)C_e+L_e V(T-1),
    P0=L_e T.

C_e,L_e are finite program constants, or supplied program coordinates restricted to these valid slices. Their dependence on e is permitted program coding; they have no varying dependence on x. The table is fixed from U15. All multiplications, comparisons, positive witnesses, and finalizer residuals remain to be literally emitted and counted. The positive native width slack is retained and bound to this exact P0. The literal E word gives 3X<P0, supplying the strong converse at the same width; no optional queue padding is used.

## 7. Narrow proved outcome and remaining work

The bounded mathematical result is the corrected right/left tag macro, its no-short-queue and unique-head adapter, the two-generation exact-output normalization, and the exact-duration/unary-loader formulas, conditional on the already established U15 finite-frame universality theorem and complete recoder theorem.

The own independent checker exercised 4,356 right/left/write/M/N macro cases (M,N=0..32), 626,241 tag steps, 1,156 whole unnormalized Genera runs with exactly one H, and 65 exponent-extraction outer cases. Every tested preacceptance word had length at least three. It also reproduces the five-letter printed-rule discrepancy. These tests support the parametric proofs; they do not replace universality or construct full positive Pell witnesses.

An independent checker separately verified the right/left parity calculations, unique accepting-head boundary, no-short-queue argument, and normalization/exponent lemmas. Its 3,600 cases (both directions and writes, M,N=0..29) all reached the exact canonical target, with no unexpected active filler and minimum queue length three. This remains mathematical/source review with bounded tests, not proof-assistant certification. Give otherwise unspecified nonhalt symbols explicit inert rules for table totality; H's rule and width are irrelevant in the published halt semantics.

Remaining: independently review this complete compiler schema against the primary U15 and Cocke–Minsky conventions; make the fixed 29-state-refinement production table and exact pair alphabet literal; compose and review the two paid recoders, input equations, unary E width binding and complete native Grill history; then obtain its actual new operation/witness/degree ledger. None of these costs can be read off the reject-all example.

This route does not prove that some table recognizes arbitrary c.e. sets on the old bare source word binary(x+1). It instead supplies a concrete, potentially payable finite input transformation for one fixed universal source and program-parameter slices. That is the explicit scope change needed for a universal polynomial through this substrate.
