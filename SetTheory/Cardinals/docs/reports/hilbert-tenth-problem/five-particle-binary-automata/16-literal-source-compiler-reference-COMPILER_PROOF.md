# Five binary particles: a reversible guarded-swap compiler

Status: mathematical construction with completed independent audits of the all-input swap lemma and full compiler. This is not a machine-checked proof, novelty claim, or materialized literal universal table. The separate API audit covers executable release behavior, not the cited universal-source theorem.

## 1. Source interface

Fix a finite partial-injective deterministic two-natural-counter machine. Its m controls include a designated halt control h with NO outgoing branch. Other controls may also be stuck on some IDs; that is not a halt observation. Each transition branch e has source q, target q', selected counter j in {left,right}, update Delta in {-1,0,+1}, and a Boolean guard made from finitely many tests c_j=k or c_j>k. Guards enforce natural counter outputs. Branch domains are disjoint at each source control; actual branch image domains are disjoint at each target control. These are semantic requirements on ALL source IDs, not just a promised computation. Let p be the number of nonzero-update branches and a the number of zero-update branches.

For each branch e write G_e(c) for its domain and I_e(c') = G_e(c'-Delta e_j) AND (c'-Delta e_j is natural) for its exact image predicate. Fix J such that all domain and image predicates are determined by each counter's class 0,1,...,J,>J. For Morita's original Z/P/+/-/0 interface, J=1 suffices; no normalization splitting is needed.

A reversible two-counter source with effective finite-input universality exists by Morita 1996, Definitions 2.1--2.3 and Theorems 4.1--4.2; see literature/reversible-two-counter-source.md. That definition designates a single final control but does not syntactically forbid its outgoing rows. Delete all outgoing rows at the designated final control: this restricts a partial injection and preserves first reachability of that control on every input. This is our normalization, not an attributed clause of Morita's definition. Morita--Imai 2001, Lemma 3.5, gives a reversible CM(2)-to-CM(2) normalization with no incoming initial-control row; it can be applied before deleting final-control exits when the finite-cycle statement is desired. The prime-code simulation visits original controls only at genuine simulated boundaries, so its designated final-control observation is sound on its computable input family. A literal instantiated universal table is a separate deliverable; Report 14's nonreversible 8408-row source is NOT used as a reversible source here.

## 2. An all-input swap lemma

Fix k>=2, B>=1, and two supports P,Q subset [-B,B] with k sites each, which are not translates of one another. Their assigned keys are the coordinate 0 in the displayed supports; neither support need have leftmost site 0. A raw key u is present if the ones in [u-B,u+B] are exactly u+P or exactly u+Q. Let T be a contextual read radius (T=0 for no context),

    L_B = 3B+1,
    M_B = max(L_B+B,T+B)+1,
    r_B = M_B+2B.

A raw key u is eligible if all ones in [u-L_B,u+L_B] are its displayed k particles, there is no other raw key within distance M_B, and a contextual predicate holds. The predicate must have the same truth value on the P and Q endpoints when their other bits are fixed. Simultaneously swap P and Q at every eligible key.

This is an involutive binary CA of radius at most r_B, conserving particle number on every finite configuration. Proof: eligible keys are more than M_B apart. Every raw test window affected by the rewrite at u has its key within 2B and all possible particles within 3B of u. Isolation leaves just the k rewritten particles. A raw match must therefore use all k; nontranslation of P,Q forces key u. Thus the ENTIRE raw-key set is invariant, not just active keys. Any other raw key whose isolation or contextual test could change is within max(L_B+B,T+B)<M_B of an active key and is blocked both before and after. Farther tests are unchanged. Active keys retain isolation and their paired predicate. Eligibility is invariant and the second application restores the configuration. This proof applies to arbitrary dense and infinite configurations. At output site i only keys within B can write; each eligibility check sees radius at most M_B+B about its key, giving r_B. Disjoint equal-cardinality rewrites prove finite mass conservation. See lemma-audit/proof.md for the independent full argument.

Call this finite-rule CA Swap(P,Q;B,G,T). We only use two-pattern gates, with the SAME contextual predicate at both endpoints. A finite composition of such gates is a reversible, mass-conserving full-shift CA; inverse gates occur in reverse order. A whole gate block need not itself be an involution on malformed inputs.

## 3. Constants, shapes, and encoding

There are n=m+2p unsigned head modes: H_q for every control, and O_e,I_e for each nonzero branch. Give each signed mode u^+,u^- a DISTINCT gap d in 1,...,D, where

    D=2m+4p, S=2D+2,
    B2=D+1, L=3B2+1=3D+4,
    B3=L+D+1=4D+5,
    Z=10B3+10+2J.

A head of signed mode u at anchor x is the TWO particles {x,x+d(u)}. The leftmost head particle is always the anchor, including when the head moves left. A home ID (q,c_left,c_right) has exactly FIVE particles:

    { -(Z+c_left), 0, Z+c_right, S, S+d(H_q^+) }.

The three singletons are endpoints and origin; they have no extra labels. The background and alphabet are exactly 0 and {0,1}. Markers are always separated by at least Z. The unique close pair has gap <=D, while its distance to a marker is >=S-D=D+2. No extra clock, spatial parity, track, or mass-free phase is used.

## 4. The underlying partial micro-path

First describe the desired unsigned partial-injective micrograph. Each source edge of update zero is one home-to-home edge guarded by G_e. A nonzero branch e of sign-side v=-1 (left counter) or +1 (right counter) is subdivided into:

1. Dispatch at origin o: H_q at x=o+S becomes O_e at x=o+v*S, with guard G_e on the old counters.
2. Outbound travel: anchor x advances by v at each edge, starting at o+v*S and ending at target marker m minus v*S.
3. Endpoint: replace m by m'=m+v*Delta and O_e by I_e at anchor m'-v*S.
4. Return travel: anchor advances by -v until x=o+v*S.
5. Commit: I_e at that anchor becomes H_q' at o+S, with guard I_e on the post counters.

For a moving mode with direction w, a marker behind the head has x=m+w*t; travel is allowed for integer t>=S. A marker ahead has x=m-w*t; travel is allowed for t>S, with arrival instead at t=S. There is no travel from behind distance S-1 into a dispatched/reversed state. Other marker separations ensure travel corridors are nonempty.

Formally, the admissible unsigned node set consists of (i) every home ID in Q times N^2 and (ii) ONLY the strict intermediate configurations on the displayed finite subdivision of an ENABLED source edge e,c with G_e(c) true. Arbitrary geometric O/I packets whose branch domain or image condition is false are excluded. A plus/minus copy of exactly this set is the admissible doubled set. Source IDs outside every outgoing guard remain homes with no outgoing edge, and IDs outside every incoming image have no predecessor.

Intermediate geometry retains the branch label e. Distinct source edges cannot share an intermediate ID: O retains old counters and e, I retains post counters and e, and each anchor identifies its position in the unique corridor. Home merging is injective precisely because the source branch images are disjoint. Thus subdivision is again a partial injection on the admissible microstates.

For e at old selected counter c the exact number of microedges is

    tau_e(c)=3+2(Z+c)+Delta-4S.

The two travel counts are Z+c-2S and Z+c+Delta-2S. A zero-update edge takes one microedge.

## 5. Realizing edge transpositions E

For every unsigned microedge c -> c', its desired doubled edge swaps c^+ with c'^-. Implement the following finite list of individual Swap gates, in any one fixed order.

(a) For each moving mode u of direction w, one TWO-particle free-flight gate, with B=B2,T=0:

    P={0,d(u^+)}, Q={w,w+d(u^-)}.

Its invariant key is the PREDECESSOR anchor. On an admissible state this gate is eligible exactly when no marker lies within [x-L,x+L] of that predecessor anchor. The only raw key is the head key: marker separations and head/marker gaps exceed D. The output reverse guard is centered on x, not on the new anchor x+w.

(b) For each moving mode u, add THREE-particle travel gates anchored at the contacted marker 0, using B=B3,T=0:

    behind t=S,...,L: P={0,w*t,w*t+d(u^+)},
                       Q={0,w*(t+1),w*(t+1)+d(u^-)};
    ahead t=S+1,...,L: P={0,-w*t,-w*t+d(u^+)},
                       Q={0,-w*(t-1),-w*(t-1)+d(u^-)}.

These are exactly the complement of free flight on valid predecessors near a marker. In particular, departure from t=L is a triple gate; its output at t=L+1 cannot also be the inverse endpoint of a free gate, whose invariant predecessor key still sees the marker at L. Arrival from t=L+1 is a free gate; no triple gate with predecessor t=L+1 exists. This explicitly resolves the free/contact boundary.

(c) For each nonzero e, add three THREE-particle gates with B3:

    dispatch: {0,S,S+d(H_q^+)} <-> {0,v*S,v*S+d(O_e^-)};
    endpoint: {0,-v*S,-v*S+d(O_e^+)}
                <-> {v*Delta,v*Delta-v*S,v*Delta-v*S+d(I_e^-)};
    commit: {0,v*S,v*S+d(I_e^+)} <-> {0,S,S+d(H_q'^-)}.

Dispatch uses G_e, commit uses I_e, and endpoint has no contextual predicate. The endpoint gate's invariant key is the OLD endpoint coordinate, even on its reverse endpoint.

(d) Each zero-update source branch has one THREE-particle gate

    {0,S,S+d(H_q^+)} <-> {0,S,S+d(H_q'^-)}

guarded by G_e=I_e.

For home gates, predicates read counter class k by bits at -(Z+k) and Z+k, for k=0,...,J, relative to the origin key. All-zero reads mean >J; multiple-one reads can simply make the predicate false. This reads only a bounded word, T=Z+J. These bits are outside both swapped supports and hence the SAME predicate is invariant at the two endpoints. Do not substitute the forward predicate for the commit's exact image predicate.

Each displayed gate pair has three distinct sites, one uniquely close gap <=D, and all other gaps >D; its plus and minus close gaps are distinct. Its P,Q are therefore not translates. All supports lie in [-B3,B3]. On admissible configurations the other two markers lie outside the gate's particle-isolation window because Z>3B3+1. A raw triple in any gate must contain the unique close pair and its nearby marker; thus there is only one raw key, regardless of the much larger contextual key-isolation radius.

On the admissible doubled graph these E gates constitute a matching. A plus state is incident only to its outgoing microedge; a minus state only to its incoming microedge. Endpoint disjointness at home follows from the actual image predicates, including counter class 1 when needed. Conversely, a minus-home endpoint satisfying I_e is the image of the unique natural predecessor c=c'-Delta e_j with G_e(c) true, so its inverse commit/direct gate enters an admissible subdivision rather than a spurious O/I geometry. Forward dispatch similarly tests the exact source domain. Thus every incident gate stays inside the precisely defined admissible set, and no gate adds an incident edge there. Consequently applying all gates once realizes that matching regardless of their order. This matching statement is asserted on admissible configurations only; global reversibility instead follows gate by gate from Section 2.

## 6. Realizing the signed phase flip P

For each moving mode u add one TWO-particle phase gate

    {0,d(u^+)} <-> {0,d(u^-)}  (B2,T=0).

For each moving u, each side s in {-1,+1}, and t=S,...,L add one THREE-particle gate

    {0,s*t,s*t+d(u^+)} <-> {0,s*t,s*t+d(u^-)} (B3,T=0).

Finally add a THREE-particle home gate for each q,

    {0,S,S+d(H_q^+)} <-> {0,S,S+d(H_q^-)} (B3,T=0).

On admissible configurations exactly one phase gate is active: the pair gate when no marker is within L of the unchanged head anchor, and the unique triple gate otherwise. The home head is always within L of its origin. The gate swap cannot change which case holds, because the anchor stays fixed. Thus their fixed-order product P acts as the sign flip on the entire admissible graph. Again P need not be an involution on all malformed configurations; each factor is.

## 7. Global map, observation, and reflection

Define one CA time step as F=P after E. It is a finite composition of translation-equivariant local involutions on the BINARY full shift. This proves full-shift bijectivity and finite numerical conservation independently of the encoded simulation. No finite-support injectivity argument substitutes for the full-shift proof.

On an admissible + state with successor, F advances one microedge while retaining +. On a - state with predecessor, it moves one edge backward while retaining -. At a missing outgoing/incoming edge it changes sign in one step. From a source-start + home configuration it therefore follows the entire source computation up to its halt home before turning around. If the start ID has no predecessor and the computation takes T microedges to halt, the orbit is a cycle of exactly 2T+2 states containing the complete forward and reverse history. It never enters a separate periodic attractor. This no-incoming normal form is available classically but is unnecessary merely to establish forward halt-pattern occurrence.

The finite anchored halt word on [0,S+D] has ones exactly at 0,S,S+d(H_h^+) and zeros elsewhere. Its length is S+D+1=3D+3. The endpoints lie outside the word and no other mode has that close gap. It is observed on the valid orbit from a plus home iff the simulated source forward run reaches h. To check the converse even when a different stuck home triggers reflection: a backward traversal cannot reach a new h-home, since that would require an outgoing microedge from h, which has none. Reflection at the other end only retraces the same component. Nothing freezes at halt; the minus halt code is different.

## 8. Exact symbolic resource ledger

Each factor has alphabet {0,1}; valid configurations have exactly five particles. Gate contexts contain no stored mass or changing background. Put b=B3=4D+5. There are:

    pair gates: 4p
    unguarded triple gates: 8pD+23p+m
    contextual triple gates: 2p+a
    total factors: 8pD+29p+m+a.

Indeed each of 2p moving modes has L-S+1 behind and L-S ahead travel positions, plus two sides of L-S+1 phase positions, and L-S=D+2. The p nonzero branches contribute three interaction gates; a zero branches contribute a direct gate; m controls contribute a home phase gate.

Individual radius bounds are

    r2=6D+8,
    r3=24D+32,
    rc=Z+J+12D+16.

The composition is therefore a radius-R CA for the explicit bound

    R=4p(6D+8)+(8pD+23p+m)(24D+32)+(2p+a)(Z+J+12D+16).

Its local binary truth table can be generated by composing these finite-radius algorithms and has 2^(2R+1) entries. This is a symbolic effective compiler and counted existence upper bound, not a printed astronomical truth table or an optimized radius. The values m,p,a of a literal universal reversible source remain unmaterialized here.

## 9. Clean exact targets with the same five particles

Assume now the source has a distinguished initial CONTROL q0 with NO incoming branch at any counter values, and final control h with no outgoing branch. This is a control-wide hypothesis: the weaker assertion that one particular input ID has no predecessor does NOT suffice for the unconditional bridge below. Morita--Imai 2001, Lemma 3.5, supplies the needed CM(2)-to-CM(2) control-wide initial normalization while preserving reversibility; delete final-control outgoing rows afterward as already explained.

Construct a new two-counter source with controls F(q),B(q) for all original q and one new terminal control H. For each original branch e:q->q' of update Delta and domain G_e, include

    F(q) -> F(q'), update Delta, domain G_e;
    B(q') -> B(q), update -Delta, domain I_e.

Here I_e is the EXACT original image predicate, including natural pre-counters. Add the two zero-update, true-guard bridges

    F(h) -> B(h),
    B(q0) -> H.

The reverse rows' domains are the original branch images and their images are the original branch domains; therefore their disjointness conditions are exactly exchanged. The first bridge fills a missing outgoing slot at F(h) and a missing incoming slot at B(h), because h has no original outgoing rows. The second fills the missing outgoing slot at B(q0), because q0 has no original incoming rows, and enters the otherwise unused H control. Thus the wrapped source is deterministic and partial-injective on ALL natural IDs. Its initial F(q0) has no incoming row and H has no outgoing row.

Its exact source counts are

    m'=2m+1, p'=2p, a'=2a+2.

The same J suffices: reverse domains are old images and reverse images are old domains. The counters are never augmented. On input c0=(a0,b0), the wrapped source first follows the original computation forward, crosses the first bridge iff the original h is reached, reverses that entire finite history, then crosses the second bridge into (H,a0,b0). If the original run does not reach h, the wrapped forward run cannot reach H. On the valid halting path, original q0 cannot reoccur internally because it has no incoming row, so the reverse bridge fires exactly after all original work is undone.

Apply Sections 1--8 to THIS enlarged source, recomputing D,S,Z and all radius counts with m',p',a'. The exact whole-configuration target is

    Enc(H,a0,b0)^+ = {-(Z+a0),0,Z+b0,S,S+d(H_H^+)}.

This is a computable INPUT-DEPENDENT five-particle target, not one universal constant target. Its occurrence is equivalent to original source halting. The CA's own later sign reflection does not introduce spurious reachability, by Section 7. Hence the attributed universal reversible source supplies fixed-CA, mass-five exact-target undecidability as well as finite-pattern undecidability.

Let Theta be the original forward computation's physical microedge count computed using the ENLARGED compiler constants. For a nonzero original branch,

    tau(c,Delta)=3+2(Z+c)+Delta-4S
                =tau(c+Delta,-Delta).

Zero-update branch clocks are one in both directions. Therefore the first clean-target time is exactly 2*Theta+2, including the two bridge steps. The CA's full reflected cycle then has length 2*(2*Theta+2)+2=4*Theta+6.

A fully materialized accepting example is supplied in clean-target-sample-source.json: the forward program increments the left counter once, the backward program decrements it, and the two bridges lead to CLEAN-HALT. Here m'=5,p'=2,a'=2,J=1,D=18,S=38,Z=782, with 353 local involution factors, composed radius 164314, and observer length 57. Input counters (0,0) give initial ones {-782,0,38,39,782} and exact target {-782,0,38,47,782}. Theta=1416, first target time=2834, and full reflected period=5670. The entire raw orbit is clean-target-sample-orbit.json. This example is a checked accepting test, not a literal universal source.

## 10. Conditional periodicity/return corollary

For a predecessor-free start ID, the reflected CA initial configuration returns to itself at a positive time if and only if the unsigned source micro-path is FINITE. In that case its least period is 2T+2, where T is the number of forward microedges to the terminal home. If the forward path were infinite and repeated a node, partial injectivity would propagate that repetition backward to give the initial node a predecessor, a contradiction. Thus an infinite forward path has distinct plus configurations forever and no return.

This is equivalent to designated-source halting only under an additional source-family hypothesis: every valid nonhalting input must yield an INFINITE source path, with no nonfinal blocking. Under that hypothesis, any computable universal predecessor-free input family supplies undecidable periodicity/positive return for fixed five-particle configurations of the binary reversible CA. Arbitrary guarded counter sources do not satisfy this automatically: a nonfinal stuck source input also produces a finite reflected cycle. The periodicity universality conclusion is stated conditionally here; the finite-pattern and clean exact-target results above do not require the extra infinite-continuation premise.
