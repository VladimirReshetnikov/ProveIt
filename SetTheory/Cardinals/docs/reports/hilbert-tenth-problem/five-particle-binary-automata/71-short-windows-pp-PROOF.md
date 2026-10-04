# Short exactness windows for a new two-block conservative rule

Date: 2026-10-04 UTC. Status: source proof completed; independent review pending.

## 1. Result and exact scope

The proposed shortening is valid. Retain the authenticated literal template families, signed-gap encoding, source interface, and geometric constants, but use pair exactness L and triple exactness b in BOTH newly defined blocks below. The resulting binary full-shift CA

    F_s = P_s after E_s

has two individually number-conserving full-shift involutions and sufficient radius

    R(F_s) <= 19b+10+3J = 76D+105+3J,
    D=2m+4p, b=4D+5.

It and its inverse agree on the entire inherited admissible doubled micrograph with both Report26 and the accepted two-scale construction subsequently used for Report70. The latter's edge and phase blocks are both replaced here. This is a new full-shift rule, not a correction to either predecessor's claimed radius or rule. Section 8 gives direct malformed-input inequalities for both blocks and their composition. No external-priority, minimal-radius, implementation, or proof-assistant claim is made.

For the inherited universal ledger D=509508,J=0, the sufficient bound is 38,722,713. This is conditional on exactly the inherited universal-source dependency, not a newly executed or independently established universal source. The precise source table remains absent. The main reduction is from 55,027,013 for the accepted two-scale rule, and from 91,711,698 for Report26.

Section 10 separately gives a one-site radius refinement for this SAME new rule, using the fact that its phase updates cannot change the endpoints of the common write interval. The headline bound above is the directly requested, simpler bound.

## 2. Fixed source data and literal endpoints

Write I_t(u)=[u-t,u+t] intersect the integers, with both endpoints included. A binary configuration is an arbitrary element of {0,1}^Z; finite supports are used only for the ordinary particle-count assertion and explicit witnesses.

Use the finite partial-injective deterministic two-natural-counter source of the authenticated COMPILER_PROOF.md. Controls have distinct home modes H_q. Each nonzero branch e has outbound/inbound modes O_e,I_e, side v in {-1,+1}, update Delta in {-1,+1}, domain G_e, and exact actual-image predicate I_e. All signed modes have pairwise distinct gaps d(u^sigma) in {1,...,D}. Domain and image guards depend only on counter classes 0,...,J,>J. Domain disjointness and actual-image disjointness hold on ALL natural-counter IDs, and enabled outputs are natural. The designated halt control has no outgoing branch.

Constants remain exactly

    S=2D+2, B2=D+1, L=3D+4,
    b=B3=L+D+1=4D+5, Z=10b+10+2J,
    r=Z+J=10b+10+3J.

A head at x has occupied sites x,x+d, so its anchor is always the leftmost particle, even for leftward motion. The other three particles are the origin and two counter markers, with separations at least Z. The admissible set consists of all natural-counter homes and ONLY strict intermediates in enabled source-edge subdivisions, both signs and every translate. Guard-invalid moving packets are excluded.

For clarity, the complete endpoint families used here are restated. Every set below is relative to its displayed invariant anchor. Write d+ and d- for the appropriate mode's distinct signed gaps.

Edge family:

- Free moving mode u, direction w: {0,d+} <-> {w,w+d-}
- Behind travel, t=S,...,L: {0,wt,wt+d+} <-> {0,w(t+1),w(t+1)+d-}
- Ahead travel, t=S+1,...,L: {0,-wt,-wt+d+} <-> {0,-w(t-1),-w(t-1)+d-}
- Dispatch e: {0,S,S+d(H_q+)} <-> {0,vS,vS+d(O_e-)}, guard G_e
- Endpoint e: {0,-vS,-vS+d(O_e+)} <-> {vDelta,vDelta-vS,vDelta-vS+d(I_e-)}, no guard
- Commit e: {0,vS,vS+d(I_e+)} <-> {0,S,S+d(H_q'-)}, guard I_e
- Zero-update direct e: {0,S,S+d(H_q+)} <-> {0,S,S+d(H_q'-)}, guard G_e=I_e

Outbound direction is w=v and inbound direction is w=-v.

Phase family:

- Free moving mode u: {0,d+} <-> {0,d-}
- Near moving mode u, side s in {-1,+1}, t=S,...,L: {0,st,st+d+} <-> {0,st,st+d-}
- Home q: {0,S,S+d(H_q+)} <-> {0,S,S+d(H_q-)}

No phase template has a contextual guard. Retain every type separately, even when distinct branches share a geometric home endpoint. No priority ordering is used.

For either family let B_g=B2 for pairs and B_g=b for triples. On the type-specific interval W_g=[-B_g,B_g], tau_(g,u) exchanges the two complete endpoint words at u and is identity on all other words and off u+W_g. Endpoint words are distinct, have equal weight, and fit their write windows. Each tau is therefore an everywhere-defined conservative involution. A pair swap preserves arbitrary bits outside I_B2(u), including bits between radii L and b. It must NOT zero-fill or erase the whole common I_b(u).

Define the new exactness radius ell_g by

    ell_g=L for a pair, and ell_g=b for a triple.

Let rho_g(x,u) mean that the occupied sites in I_ell_g(u) are exactly u+P_g or u+Q_g. Let c_g add the type's contextual guard, when present. The class reads are at u±(Z+k), 0<=k<=J; multiple occupied class sites may reject the guard and no occupied class site means >J. These sites are outside every rewrite. Thus all c_g are finite, everywhere-defined, translation-covariant predicates; c_g is invariant under its own tau. Pair exactness implies the endpoint word on I_B2, and triple exactness is exactly the endpoint word on I_b. Guard reads are unchanged by each paired swap, including on malformed inputs.

## 3. The new edge block: full-shift proof

### 3.1 Same-anchor control is an involution

At a fixed integer anchor u define the FULL guarded type set

    C_u(x)={g in the edge family: c_g(x,u)}.

Define T_u(x)=tau_(g,u)x if C_u(x)={g}=C_u(tau_(g,u)x); otherwise define T_u(x)=x. This includes all types in both tests. If it acts, the same unique g passes in the image and the second application reverses it. If it does not act, x is fixed. Hence T_u is an everywhere-defined involution, irrespective of zero, multiple, conflicting, or newly enabled types. It writes only I_b(u), preserves weight there, and its replacement word is determined by I_r(u). Testing a hypothetical candidate adds no radius: replacement bits are already computed inside the known I_r word, and all unchanged candidate input bits remain in that word.

Define the edge RAW ANCHOR set

    R(x)={u: some rho_g(x,u) holds}.

Types at the SAME integer anchor coalesce here, but they do not coalesce in C_u. Since L<=b, raw recognition reads radius a=b. A nonidentity T_u implies a guarded type and hence raw recognition at u. This verifies every control/recognition assumption needed below.

### 3.2 Selection

Set

    H=max(2(b+a),b+r)=b+r,

where the last equality follows from r>=3b. Select u exactly when u belongs to R(x), no other v in R(x) has |v-u|<=H, and

    R(T_u x)=R(x).

Apply the selected T_u simultaneously, leaving every other coordinate fixed. The equality is a finite prospective RAW-ANCHOR test, not a guarded-type or eligibility comparison. Only anchors |v-u|<=b+a=2b can change their recognition; their windows are contained in I_(b+2a)(u)=I_3b(u). Computing T_u additionally uses I_r(u). Thus the whole prospective test reads only I_r(u), because r>=3b.

### 3.3 Recognition, rejected statuses, and inverse

Distinct selected centers are farther apart than H, so their write intervals are disjoint. If a recognition window I_a(v) met two selected write intervals at u,w, then |u-w|<=2(b+a)<=H, a contradiction. Its post-update word therefore agrees with its old word or its word after exactly one selected T_u. That T_u passed the complete prospective equality. Hence R(E_s x)=R(x) for EVERY anchor on EVERY bi-infinite binary input. This explicitly includes absent anchors, dense malformed inputs, and possible cooperative births or deaths.

Now fix any recognized isolated u, whether selected or rejected. Every other selected w has |w-u|>H=b+r; its write interval therefore misses I_r(u), which contains all local control and prospective-decision data. An unselected u's data do not change, so its failed prospective test stays failed. For a selected u, its new data agree with those in T_u x. Its own prospective equality remains true because T_u^2=id interchanges the two compared recognized sets. Recognition-set invariance preserves isolation. Nonisolated anchors remain blocked and absent anchors remain absent. Recognized identity controls pass prospectivity harmlessly and remain identities because their entire control words are protected. Thus the COMPLETE selected-anchor set is invariant.

On reapplication the same selected local controls see precisely their own previous image, with no changes from other selected anchors inside their control windows, and undo it. Therefore E_s^2=id on the full shift. Equal-weight changes on disjoint blocks conserve the ordinary number of ones for finite-support inputs. There can be only finitely many nontrivial selected changes on a finite-support input because each uses at least one original occupied site. This also proves finite support is preserved. Infinite configurations require no comparison of divergent total sums.

### 3.4 Edge radius

An output coordinate can change only from a selected anchor at distance at most b. Isolation reads H+a about that anchor; control and prospectivity read r, which H+a dominates. Therefore

    R(E_s)<=b+a+H=3b+r=13b+10+3J.

This is a finite Boolean definition even for arbitrary infinite inputs. Translation covariance gives a binary CA. Closed intervals and exclusion at distances <=H are used throughout; equality is never silently treated as safe separation.

## 4. The new phase block: full-shift proof

This block is newly defined, not the old phase block with its radius relabeled. Let

    C_P(x)={(g,u): rho_g(x,u), g in the phase family}.

Keep type and anchor, but not endpoint orientation. Here every candidate reads radius at most r_P=b; every transposition writes radius at most b and its candidate predicate is endpoint-symmetric. Select k=(g,u) when it belongs to C_P(x), no OTHER candidate key (including another type at u) has anchor within H_P=2(b+r_P)=4b of u, and

    C_P(tau_k x)=C_P(x).

It suffices to compare all phase types at anchors within b+r_P=2b of u; this reads at most b+2r_P=3b. Define P_s by all selected transpositions simultaneously.

The selected supports are disjoint. A radius-b candidate window cannot see two selected write intervals because that would put their centers within 4b. Every candidate predicate therefore sees no rewrite or exactly one individually prospectively stable rewrite, proving complete candidate-key invariance, including initially absent keys and keys of other types. For every isolated candidate, all other selected writes miss its radius-3b prospective-decision window: their anchors are farther than 4b and their support radius is b. A rejected candidate's prospective failure is unchanged; a selected candidate's own involution interchanges the two compared key sets, preserving its success. Nonisolated keys remain nonisolated and noncandidates remain absent. Hence the entire selected-key set is invariant. A second application uses the same disjoint involutions and restores x.

Therefore P_s is a full-shift conservative involution. Isolation reads radius H_P+r_P=5b about a candidate anchor; prospectivity reads 3b. An output site needs only possible writing anchors within b. Thus

    R(P_s)<=6b.

No same-anchor uniqueness theorem for malformed phase inputs is assumed. If several types occur at a home or anywhere else on malformed inputs, typed-key isolation rejects them, and the full candidate/prospective argument above still applies.

## 5. Why shortening triples preserves ALL admissible recognition

This is the separate geometric obligation; full-shift safety alone would not prove simulation preservation.

### 5.1 Every raw match uses the real head pair

An admissible configuration has one and only one occupied pair with distance <=D: the head. Head-marker distances are >=S-D=D+2>D, and marker-marker distances are >=Z. Every literal pair endpoint is a head pair. Every triple endpoint has one close pair and a singleton whose distance to each head site exceeds D, including the extreme reverse travel endpoint and the translated endpoint interaction. Thus every new raw match must use the actual head pair, its actual signed gap identifies mode and orientation, and any third displayed site must be an actual marker. This argument ranges over ALL integer anchors, not only the intended anchor.

Every literal triple's singleton lies within L+1 of its head anchor. This follows directly from the travel ranges S..L and S+1..L+1, home/dispatch/commit distance S, and endpoint actual-singleton distance S. Since Z>2(L+1), at most one actual marker can support ANY raw triple using that head; two different types cannot use different nearby markers. Merely noting that one template's diameter is less than Z would not suffice for this cross-template conclusion.

For a fixed signed endpoint and actual head pair, its offsets force the invariant anchor. Ordinary triples anchor at their actual singleton marker. The only exception is the reverse endpoint interaction, whose anchor is one site from its actual marker and is handled in Section 5.4. Other markers lie at least Z away from an ordinary marker anchor, and at least Z-1 away from that old endpoint anchor. In particular they lie outside BOTH I_b and the OLD I_(3b+1).

Consequently every geometric triple match on an admissible input satisfies the old large exactness test if and only if it satisfies the new test: both windows contain exactly its three displayed particles. Shrinking the window admits no extra admissible type or anchor. Pair tests are literally unchanged. This is a direct all-anchor equivalence of the old and new geometric recognition sets on the admissible set; the detailed type/anchor classification follows next to expose every boundary used in preservation.

### 5.2 Homes, including multiple raw types at one anchor

At plus H_q only outgoing dispatch/direct forward endpoints contain its gap; all force the origin as anchor. At minus H_q only incoming commit/direct reverse endpoints contain its gap, again at the origin. There are no moving-mode free or travel templates with a home gap. Raw edge recognition is empty or the singleton origin, although several branch types may contribute there. Guarded types are empty or singleton by source-domain disjointness at plus homes and EXACT actual-image disjointness at minus homes. The guard reads faithfully detect old or post counter classes and cannot be contaminated by the head, whose sites are inside b<Z. A home with no incident edge has T_u=id everywhere, even if it has raw recognition.

The selected outgoing/incoming edge enters exactly an enabled subdivision: the image guard includes existence of natural pre-counters. Substituting a forward guard at a minus home would invalidate this conclusion and is not done.

### 5.3 Both signed corridors, including equality cases

Let w be the moving mode's direction, A its departure marker, C its destination marker, N=w(C-A)>=Z, and t=w(x-A), where x is the always-leftmost head anchor. Then S<=t<=N-S. The third marker is remote. Since N>2(L+1), the following intervals do not overlap.

For PLUS states the free key is x. Pair exactness requires L<t<N-L. The complete raw partition is

    behind travel:       S<=t<=L,             key A
    free travel:         L+1<=t<=N-L-1,       key x
    ahead travel:        N-L<=t<=N-S-1,       key C
    forward interaction: t=N-S.

For MINUS states the free key is x-w, NOT x. Pair exactness requires L<t-1<N-L. The complete raw partition is

    reverse interaction: t=S
    behind inverse:      S+1<=t<=L+1,         key A
    free inverse:        L+2<=t<=N-L,         key x-w
    ahead inverse:       N-L+1<=t<=N-S,       key C.

A behind triple takes plus distance L to minus distance L+1. At that minus endpoint, the free predecessor key still sees the departure marker at distance L, so free inverse recognition fails. An ahead free move takes plus distance L+1 from the arrival marker to minus distance L; its predecessor key still sees the marker at L+1, so free inverse succeeds, while the reverse ahead-triple range ends at current distance L-1. These arguments include w=-1, without reflecting the order of the two head particles. At a plus arrival wall, travel ends one step before distance S. At a minus departure wall, inverse travel begins only at S+1. Thus neither interaction wall acquires a competing travel key.

Within a triple range, the signed gap, uniquely possible marker, side, and distance determine exactly one type. Shrinking triple exactness cannot create another candidate because Section 5.1 already enumerated every possible marker and anchor, and all endpoint offsets are unchanged.

### 5.4 Interactions and the old endpoint key

The full interaction list is:

- Outbound minus at departure wall: reverse dispatch, origin key, true domain guard because the corridor is enabled
- Outbound plus at arrival wall: forward endpoint, old selected marker key m
- Inbound minus at departure wall: reverse endpoint, OLD key m=m'-vDelta, where m' is the current updated marker
- Inbound plus at arrival wall: forward commit, origin key, true exact image guard because the post-counters come from the enabled branch

In the reverse endpoint word, the actual singleton has offset vDelta and the head anchor has offset vDelta-vS. Therefore both components force u=m'-vDelta=m; using current marker m' as key is wrong when Delta is nonzero. The actual marker-head distance remains S. Its other markers remain beyond Z-1>3b+1>b from this invariant old key. Thus the shortened exactness test still holds in both orientations, for both update signs and both physical sides.

Distinct branch-specific O/I signed gaps exclude other branch interactions. The same branch's interaction can use an actual marker only at the stated wall, and the corridor partition excludes travel there. The third marker is outside the L+1 matching range. Together these facts prove moving admissible states have exactly one raw type-anchor, with its interaction guard true when needed.

### 5.5 Every desired edge passes the new tests

For each intended edge, the reverse endpoint stays admissible, has the SAME raw anchor, and the guarded set at that anchor is the SAME singleton {g}. The key is the predecessor head anchor for free travel, contacted marker for near travel, origin for dispatch/commit/direct, and OLD selected marker for endpoint interaction. Hence T_u is precisely the intended transposition and

    R(x)={u}=R(T_u x).

Isolation and the complete prospective equality pass. At missing edges all local controls are identities and E_s fixes the state. This includes every natural-counter home, every strict enabled intermediate, every source branch, both signs, all counter sizes, all translations, and both reflection ends.

## 6. Phase candidate set on every admissible state

At a home the sole phase type is phase-home:q at the origin, with no free-home phase template. At a moving state the free phase key is the unchanged head anchor x for BOTH signs. It is a candidate exactly when every marker is farther than L from x. Otherwise exactly one marker is at distance in S..L, and its side and distance choose exactly one near-phase triple. The other marker candidates are excluded by Z>2(L+1); wrong modes and alternate pairs are excluded by the unique signed gap and close pair. Section 5.1 proves shortening exactness causes no additional phase candidates at other anchors.

A phase swap fixes every marker, the head anchor, and the unsigned mode; it only changes the signed gap. Its free/near/home case, type, and invariant key therefore do not change. The full typed candidate set is the same singleton before and after. Typed isolation and prospective stability both pass automatically. Thus P_s is exactly the phase flip on the entire admissible doubled graph.

## 7. Composition, clocks, and dependency limits

Both restricted blocks preserve the admissible graph and equal its edge matching and sign flip. Consequently F_s=P_s E_s agrees step for step there with both predecessors, and its inverse E_s P_s agrees there as well. Its sufficient radius is

    R(E_s)+R(P_s) <= (13b+10+3J)+6b
                  =19b+10+3J
                  =76D+105+3J.

The original binary alphabet and exactly five-particle encoding, observer length 3D+3, and nonzero-source clock 3+2(Z+c)+Delta-4S are unchanged; a zero-update source edge still takes one step. Reflections, first clean-target time 2Theta+2, and reflected period 4Theta+6 transfer on their original hypotheses. Control-wide predecessor-free initial normalization is still required by the unconditional clean-target bridge. Equivalence of periodicity/return with designated halting still additionally requires no nonfinal blocking on the claimed source-input family.

The template count remains 8pD+29p+m+a_source. Two mathematical involutions do not imply two cheap arithmetic factors, and no template-independent Boolean evaluation cost is claimed. The old arbitrary-malformed interpreters, source programs, trajectory verifiers, circuit counts, and schedules are not new-rule implementations or certificates. Semantic admissible witnesses transfer; malformed certificates do not transfer automatically.

Numerical substitutions (sufficient bounds, not measured radii):

    D=8, J=0:       edge 491, phase 222, total 713
    D=18, J=1:      edge 1014, phase 462, total 1476
    D=509508, J=0:  edge 26494491, phase 12228222, total 38722713.

The universal-source receipt uses m=122622,p=66066 and source SHA-256 fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3. Its source table and universality are inherited dependencies, not refreshed evidence here.

## 8. Direct malformed witness: both blocks and the composition differ

Use ordered controls (q,h), one true-guard right-increment branch q->h, and J=0. Its exact image is right-counter positivity, expressible by classes 0,>0. Literal gap order is

    Hq+=1,Hq-=2,Hh+=3,Hh-=4,O+=5,O-=6,I+=7,I-=8.

Thus D=8,S=18,B2=9,L=28,b=37,K_old=112,Z=r=380. Consider the FOUR-particle input

    X={0,18,23,80}.

The only close pair is {18,23}, gap 5, so every possible edge or phase match uses this O-plus head. Only marker 0 is within L+1=29 of its anchor 18; particle 80 is 62 away. A free pair candidate fails because its radius-28 exactness window contains marker 0. The sole geometric edge type is behind O at t=18, key 0; the sole geometric phase type is near O at distance 18 on the positive side, key 0. Both old triple predicates fail because their radius-112 window includes the extra particle 80. Therefore the Report26 edge, the accepted two-scale edge, and the old shared phase block all FIX X.

With the new radius-37 triple exactness, the edge type is the sole raw anchor/type. Its paired endpoint is {0,19,25,80}; it has O-minus gap 6 and the sole inverse-behind type at current distance 19, again key 0. The free inverse key is 18 and still sees marker 0. No other triple can use particle 80. Guarded mutual uniqueness, isolation, and raw prospectivity therefore pass:

    E_s(X)={0,19,25,80} != X.

For the new phase applied directly to X, its sole near type swaps O-plus gap 5 to O-minus gap 6 with head anchor 18 and keeps the same unique typed key:

    P_s(X)={0,18,24,80} != X.

This proves EACH new block differs from its predecessor, not merely that their definitions were changed. On E_s(X), the sole phase key is near O at distance 19; it flips gap 6 to gap 5 and passes the same prospective test. Hence

    F_s(X)={0,19,24,80},
    F_26(X)=F_accepted_two_scale(X)=X.

These are direct endpoint-word deductions, not simulator outputs. X is outside the five-particle admissible set.

A separate separation witness isolates the phase-filter change: Y={0,5,200,205} has exactly two free O phase keys, at 0 and 200. Each individual flip preserves those keys. New H_P=148 permits both; old H_P=298 rejects both. Edge isolation rejects both anchors for all three rules (200<=417<=834). Thus F_s(Y)={0,6,200,206}, while both predecessor maps fix Y. No triple exists because each cluster has two particles and intercluster distances exceed 2b.

## 9. Why pair exactness cannot simply be shortened too

The triple-window proof did not make pair padding dispensable. Suppose the unchanged pair template used exactness ell with B2<=ell<L. In an enabled sufficiently long corridor, consider a plus head at departure distance t=L. The behind triple at the departure marker is still recognized. The free pair centered at the head would now also be recognized, because the departure marker at distance L lies outside I_ell and the arrival/third markers are far away. The two distinct raw anchors are only L apart, well inside H. Thus the new selection rejects the intended travel edge. This is a symbolic admissible counterexample to that further shrink with unchanged template ranges and selection.

Likewise enlarging the pair radius to an integer >L can suppress the intended free move at departure distance L+1 while no behind triple is available there. The exact retained radius L is dictated by the literal free/contact subdivision. This section is about the unchanged families and this safety filter, not a universal lower bound over different encodings or rules.

## 10. Corollary: one-site improvement for the exact same new rule

Every PHASE endpoint support lies in I_(L+D)=I_(b-1). For the positive-side extreme t=L with maximum signed gap D, the rightmost site is L+D=b-1, so this equality case is included, not bounded by a strict inequality. For negative-side triples the leftmost possible site is -L and the remaining head site is -t+d; both have absolute value at most L+D=b-1. Home supports lie even closer, and pair supports lie in I_D. Thus both complete endpoint words have bit zero at +b and -b. On a non-endpoint word the transposition is identity; on an endpoint word it changes each boundary zero to the same zero. No phase transposition can therefore change either boundary coordinate on ANY input.

The recognition predicates STILL inspect zeros at offsets +b and -b for triples, and the endpoint-word transposition STILL reads the complete I_b word. Only the set of output coordinates that can actually change is sharpened. No predicate, transposition, isolation threshold H_P=4b, or prospective test changes, hence P_s itself is unchanged.

In the established phase radius proof, a coordinate can actually change only from an anchor within b-1 rather than b. Its eligibility still reads at most 5b and its local endpoint substitution at most b. All other anchors leave that coordinate fixed. Therefore, for the SAME newly defined map,

    R(P_s)<=6b-1,
    R(F_s)<=19b+9+3J=76D+104+3J.

The three example totals become 712,1475,38,722,712. This is a small upper-bound refinement, not a claim that either bound is exact. More ambitious reductions of phase windows or exclusion thresholds would define or analyze another rule and are not pursued here.

## 11. Evidence and preservation statement

The accepted source packet manifest is pinned by SHA-256 f1c19ca86641cbf5ebaed81d0c78e82563258753bbf8f38f2f46229247b71fa0; the combined independent-audit manifest by 3bfe65db1ad9c0aab9fd13641cfbad843a292d2c2dbec444fa0f7ebb856876b1. Complete relevant source proofs and audits were read, along with the original archive's all-input lemma audit and literal compiler endpoint formulas as INERT TEXT. Fresh hashing verified all 21 packet manifest entries and all 17 audit manifest entries, including the audit's recorded modes and modification times.

No upstream or author program, source interpreter, physical/CA/trajectory simulator, saved schedule, or Lean was run. Only fresh inspected static hashing/JSON processing and affine integer arithmetic were executed. This packet contains no CA evaluator. No external publication, upload, or public mutation occurred. Original source bytes, modes, and mtimes are checked against separate before/after snapshots; see PRESERVATION.md for exact timing and any concurrent changes in the separately observed live Report70 tree. Endpoint equality is not described as proof of a continuously static interval.
