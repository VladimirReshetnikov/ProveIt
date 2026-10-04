# Independent mathematical audit: separated recognition and contextual control

Date: 2026-10-04

## Result

**PASS**, as a mathematical construction using the endpoint families and admissible-set hypotheses stated below. The proposed full-shift involution lemma is valid, the mutually unique local type construction is an everywhere-defined involution, and the new edge block preserves the entire Report26 admissible doubled micrograph. The sufficient composite radius is

    R <= 108D + 149 + 3J.

The arithmetic substitution at D=509508, J=0 is 55,027,013. This audit does not independently establish that universal-source ledger or its universality theorem, produce an implementation, certify existing new-rule executable code, or assert radius optimality or external novelty.

Only text was inspected. No upstream scientific code, interpreter, simulator, schedule, or Lean was executed. The parent supplied authentication of the extracted archive by ZIP SHA-256

    20a23b1ee22aed461942da4def6bade2bd55d777fce1fe49b6ff83248b7442e4.

## Inspected sources

- `recognition_guard_radius_lemma.md`, the newly proposed lemma and specialization
- Extracted `parallel-involution-report26/scientific/PROOF.md`
- Extracted `parallel-involution-report26/scientific/COMPILER_PROOF.md`
- Extracted `parallel-involution-report26/scientific/audit-preservation.md`

All facts about literal compiler templates below refer to the explicit formulas in COMPILER_PROOF Sections 3--6, rather than an inference that guarded uniqueness automatically gives unguarded uniqueness.

## 1. Full-shift lemma

Interpret “T_u reads radius r and writes radius b” precisely as follows: its replacement word on I_b(u) is determined by the input on I_r(u), and it fixes every coordinate outside I_b(u). Let

    h = max(2(b+a), b+r),
    s = max(r, b+2a).

Let R(x) be the set recognized by the radius-a Boolean predicate. Select recognized anchors with no other recognized anchor within distance h and with R(T_u x)=R(x).

### Finiteness and locality of prospectivity

Only recognition predicates at anchors v with |v-u| <= b+a can change under T_u. Their input windows together lie in I_(b+2a)(u). Constructing the hypothetical replacement additionally reads I_r(u). Thus the global equality test is genuinely a finite radius-s test, including the case T_u is the identity.

### Arbitrarily overlapping candidates and infinite configurations

Selected anchors are at distance greater than h, so their write intervals are pairwise disjoint. A recognition window I_a(v) cannot intersect two selected write intervals: that would put their anchors at distance at most 2(b+a) <= h. For each v, its post-update recognition word therefore equals either its original word or its word after one particular selected T_u. Each selected T_u preserves the entire raw recognized-anchor set by its prospective test. Consequently

    R(Ax) = R(x)

for every bi-infinite x. This rules out cooperative raw-anchor births and deaths; it is not a finite-support argument.

### All isolated recognized anchors retain their selection decision

Consider every recognized anchor u that is isolated in R(x), not only those initially selected. Every other selected anchor v obeys |v-u|>h. Its write interval misses both I_r(u) and I_(b+2a)(u), since h>=b+r and h>=2b+2a. Hence all other simultaneous updates leave the radius-s decision data at u unchanged.

If u is not selected, no update occurs at u, so its prospective test remains false. If u is selected, the data used to test it after the simultaneous update agree with those in T_u x. Since T_u is an involution,

    R(T_u(T_u x)) = R(T_u x)

is exactly the original prospective equality with its two sides interchanged. Its truth value is unchanged. This also covers selected anchors for which T_u x=x. An isolated recognized anchor with an identity local map is selected, but writes nothing; it remains an identity update afterward.

R-invariance preserves both recognition and isolation. Nonisolated anchors remain nonisolated, and absent anchors remain absent. Therefore the entire selected-anchor set is invariant. On the second application each selected map sees its own first image on I_r(u), with all other selected writes outside that window, and reverses it. Thus A squared is the identity.

This argument also handles guarded-candidate births at already recognized anchors. A nonisolated raw anchor cannot become selected, while every isolated raw anchor has all of its radius-r control protected. The theorem does not claim that every guarded candidate type is globally preserved.

### Output radius and conservation

For output coordinate i, only anchors in I_b(i) can write. Recognition plus isolation reads radius h+a about such an anchor, and its local map and prospective test read at most s. The inequalities

    h+a >= r,   h+a >= b+2a

give output radius b+h+a. The selected disjoint replacements preserve their finite-window weights, hence the number of ones on every finite-support configuration. Shift covariance and the finite-radius formula yield a binary CA. None of these steps assumes sparse, admissible, or finite input.

## 2. Mutually unique type selection

At a fixed anchor u, put C_u(x)={g:c_g(x,u)}. For C_u(x)={g}, apply the endpoint involution tau_(g,u) only if C_u(tau_(g,u)x)={g}; otherwise fix x.

If the map acts, its image y has the same unique type g and tau_(g,u)y=x, so the exact same symmetric test acts in reverse. If the map does not act, its output is x and applying it again also fixes x. Thus T_u is an everywhere-defined involution even with competing types, overlapping endpoints, malformed contextual reads, or a type birth/death in the hypothetical image. In particular, no choice of an irreversible priority order is involved.

Every candidate c_g reads inside I_r(u), and its type-specific transposition reads and writes within I_b(u), with b<=r. Evaluating every candidate on a hypothetical transposition uses only the original I_r(u) word with the known internal replacement. There is no addition of radii here. The union-of-types recognition predicate omits the contextual guards but retains each type's own exactness radius 3B_g+1, so it has radius at most 3b+1. Any nonidentity T_u begins at a raw recognized anchor.

The endpoint involutions must use their type-specific write windows. In particular, a free pair type does not erase arbitrary bits in the larger common I_b(u) interval. This is the common-window caveat already established in Report26.

For an empty edge family, take C_u and R empty and T_u the identity. The stated uniform radius remains an upper bound; no maximum over an empty set needs to be defined.

## 3. Guard-free anchor uniqueness on the entire admissible set

Write

    S=2D+2,  L=3D+4,  b=4D+5,
    K=3b+1,  Z=10b+10+2J.

All signed gaps are distinct. On every admissible configuration the head particles form the unique occupied pair with separation <=D; all other particle-pair distances exceed D. Every endpoint template has exactly one such close pair. Any raw geometric match must therefore use the actual head pair, and its gap fixes the signed mode and hence the relevant orientation of an edge template.

For a triple template, the remaining displayed particle must be an actual marker. The explicit templates put that marker at head-anchor distance at most L+1, including the reverse endpoint whose anchor itself can differ from the actual marker by one. Marker separations are >=Z>2(L+1), so at most one actual marker can be in this range. The other markers are outside the intended triple exactness window: they are at least Z from a marker anchor, or at least Z-1>K from a reverse-endpoint old-marker anchor.

The bare statement that one template's diameter is less than Z is not by itself the complete cross-template uniqueness argument; the explicit head-to-marker range and signed-mode restrictions supply that argument here.

### Homes: several raw types, only one possible anchor

At H_q plus, only the forward dispatch/direct endpoints for source control q contain the correct signed gap. Their head anchor is u+S and their singleton is u, forcing u to be the origin. At H_q minus, only reverse commit/direct endpoints for target q contain that gap, and again u is the origin.

Omitting guards can therefore introduce several raw types at a home, but every one is at that same integer origin anchor. The raw recognized-anchor set is either empty or {origin}. Source-domain disjointness gives at most one enabled guarded type at home plus; exact-image disjointness gives at most one at home minus. A blocked home can still possess raw recognition, which is harmless: all T_u are the identity if no guarded edge exists.

### Moving modes: raw travel partition before any guard

Use forward direction w, departure marker A, destination marker C, N=w(C-A)>=Z, and t=w(x-A), where x is the head anchor and S<=t<=N-S. For outbound, w=v; for inbound, w=-v. The third marker cannot lie in any relevant near-marker range.

For plus sign, the free template key is x. Exactness requires L<t<N-L. The literal triple endpoints and free range give:

    behind:       S <= t <= L,             anchor A
    free:         L+1 <= t <= N-L-1,       anchor x
    ahead:        N-L <= t <= N-S-1,       anchor C
    interaction:  t=N-S

For minus sign, the free template key is x-w, so exactness requires L<t-1<N-L. The literal reversed endpoints give:

    interaction:  t=S
    behind:       S+1 <= t <= L+1,         anchor A
    free:         L+2 <= t <= N-L,         anchor x-w
    ahead:        N-L+1 <= t <= N-S,       anchor C

Within a triple range the signed gap, side of the one possible marker, and integer distance fix its type. These intervals are disjoint and cover the corridor with its indicated interactions. In particular, the behind L-to-L+1 crossing is a triple on both ends, whereas the ahead L+1-to-L crossing is free on both ends. The free inverse is centered on the predecessor, which is essential to both conclusions.

### Interaction endpoints and absence of remote raw alternatives

- Outbound minus at t=S: reverse dispatch, anchored at the origin A
- Outbound plus at t=N-S: forward endpoint, anchored at the old destination marker C
- Inbound plus at t=N-S: forward commit, anchored at the origin C
- Inbound minus at t=S: reverse endpoint, anchored at u=m'-v*Delta, where m' is the actual updated departure marker

For reverse endpoint, the literal offsets are singleton v*Delta and head anchor v*Delta-v*S. Both force this same old-marker anchor u; using m' as the key would be wrong when Delta is nonzero.

Other interaction types are excluded by distinct branch-specific signed gaps. For the matching signed mode, its interaction template can fit an actual marker only at the stated boundary. For example, outbound reverse dispatch requires marker u=x-v*S and hence t=S; outbound forward endpoint requires u=x+v*S and hence t=N-S. Inbound commit requires u=x-v*S and hence its ahead wall; reverse endpoint requires an actual singleton m'=x+v*S and hence its behind wall. Throughout the admissible corridor these hypothetical singleton locations cannot be the third marker. Travel is absent at the corresponding wall by the interval partition, independent of guards.

Therefore moving admissible nodes have exactly one raw type-anchor. On reverse dispatch and forward commit, the remaining contextual guard is true because admissible intermediates belong to an enabled source-edge subdivision and retain its old/post counters. The definition of the admissible set is essential here; arbitrary guard-invalid moving geometry is not included.

### Paired endpoints preserve the raw singleton anchor

Every intended edge joins two admissible endpoints. Their raw anchors coincide:

- Free travel: the shared predecessor head anchor
- Triple travel: the unchanged contacted marker
- Dispatch, commit, direct: the unchanged origin
- Endpoint: the old endpoint marker coordinate on both orientations

Thus if the intended local edge at u exists, R(x)={u}=R(tau_(g,u)x). The guarded candidates at both endpoints are the same singleton g by the domain/image conditions and the preceding geometric audit. Consequently the local mutual-uniqueness condition, raw isolation, and outer prospective equality all pass. At a missing edge the new edge block fixes the admissible state. This proves agreement on every admissible doubled state, not merely one forward run.

## 4. Radius algebra and composition

Use a=3b+1 and r=Z+J=10b+10+3J. Then

    r-(b+2a)=3b+8+3J >= 0,
    h=b+r,
    R_edge <= b+a+h = 15b+11+3J.

The retained Report26 phase block has radius at most 12b+3. Thus its composition after the new edge block has

    R <= 27b+14+3J =108D+149+3J.

The substitutions are:

    D=509508, J=0: 55,027,013
    D=8,      J=0: 1,013
    D=18,     J=1: 2,096.

The old Report26 bound at the universal-ledger substitution was

    180*509508+258 = 91,711,698.

These are sufficient bounds, not measured or minimal radii. The two blocks remain full-shift involutions, so their composition has inverse given by the opposite block order. Admissible trajectory equality transfers the same five-particle encoding, observation, microedge clock, reflections, and source-specific clean targets.

## 5. Exact dependencies and limits

The new source-uniform radius theorem depends on:

1. Finite accepted source data with deterministic disjoint branch domains, disjoint actual branch images, natural-output guards, distinct signed-mode gaps, and a common nonnegative class bound J
2. The literal edge endpoint templates, type-specific write windows, and unchanged geometric constants in COMPILER_PROOF Sections 3--5
3. The exact admissible set: all natural-counter homes and both signs of strict intermediate nodes of enabled source-edge subdivisions
4. The original guard reads at origin-relative sites plus/minus (Z+k), k=0,...,J; exact image guards at commit rather than substituted forward guards
5. The new abstract lemma and mutual-unique local construction proved above, plus the separate guard-free admissible audit above
6. The unchanged Report26 phase block and its full-shift proof/radius bound, together with its admissible sign-flip behavior

The universal numerical corollary additionally depends on the inherited Report19 ledger D=509508, J=0 being the appropriate accepted universal source and on the attributed source universality/normalization claims. The inspected Report26 PROOF itself calls that line a symbolic ledger substitution and does not independently re-prove the source theorem; this audit preserves that boundary.

No equality with Report26 is asserted on malformed configurations. No old malformed-state certificate, ordered-factor arithmetic verifier, circuit count, runtime bound, or existing executable evaluator automatically transfers to this new rule. No implementation of this new definition was inspected or executed. A periodicity/return universality claim still needs the separate no-nonfinal-blocking infinite-continuation hypothesis already identified in COMPILER_PROOF Section 10.

## 6. Concrete static witness that the full-shift rules differ

The following witness was checked by direct finite-word reasoning, with no simulator or upstream program execution. The literal signed-mode ordering was inspected as inert text using `unzip -p` on the authenticated archive's `scientific/frozen_reversible_binary.py`, specifically its `_compile_validated` definition. It lists home modes in control order, followed by O then I for each nonzero branch, assigning plus then minus consecutive gaps starting at one.

Take the source with ordered controls (q,h), one true-guard right increment q to h, and J=0. The exact image guard is positivity of the right counter, which is determined by classes 0 and >0, so J=0 suffices. Its constants are

    D=8, S=18, B2=9, L=28,
    b=37, a=112, Z=r=380.

The signed gaps are

    H_q+:1, H_q-:2, H_h+:3, H_h-:4,
    O+:5, O-:6, I+:7, I-:8.

Let

    X={0,5,500,505}.

All geometric triple templates are impossible: each cluster has only two occupied sites, while the two clusters are separated by at least 495>2b. The only close pairs have gap 5, so the only edge candidates are the O free type at anchors 0 and 500. Their exactness windows of radius L=28 contain precisely their own pair. Its endpoint transposition is

    {0,5} <-> {1,7}

relative to its invariant predecessor key.

For Report26, H_E=2(b+r)=834. Each candidate sees the other within distance 500, so neither is selected and

    E26(X)=X.

For the new edge block, H=b+r=417. Each raw recognized anchor is isolated. The guarded local set at each of these anchors is the singleton O free type, both before and after its hypothetical swap. After either individual hypothetical swap, its new O-minus pair still has the same reverse free key: the leftmost occupied site is u+1, while the reverse predecessor key is (u+1)-1=u. The other pair is unchanged, and no triple or cross-cluster close pair can arise. Thus the entire raw recognized-anchor set remains {0,500} in each prospective test. Both new updates are selected, giving

    E*(X)={1,7,501,507}.

For the unchanged phase block, r_P=3b+1=112 and H_P=2(b+r_P)=298. On X its only phase candidates are free O at anchors 0 and 500; on E*(X) they are free O at anchors 1 and 501. Their separation 500 exceeds H_P. The phase transposition is {0,5}<->{0,6} relative to the leftmost head anchor. Every individual hypothetical phase swap preserves the same phase type-anchor set; exactness remains valid and no triple or cross-cluster pair appears. Hence

    F26(X)=P26(E26(X))={0,6,500,506},
    F*(X)=P26(E*(X))={1,6,501,506}.

These outputs differ, establishing that the proposed construction is a genuinely different full-shift rule for this accepted small source, while the admissible five-particle simulation remains unchanged. This witness uses four particles and is outside the admissible set.

## 7. Review of the expanded proof packet

The expanded `/workspace/shared/radius-frontier-20261004/proof-packet/PROOF.md` was read on 2026-10-04 after the first audit. Its full-shift lemma, mutual-uniqueness construction, radius calculation, and admissible preservation argument agree with this audit. No new mathematical defect was found.

The recommended clarification in Section 6.1 has now been inserted and re-read: every triple's singleton lies within L+1 of the head anchor, and Z>2(L+1), so different triple types cannot use different nearby markers. This resolves the exposition issue identified in the initial review. The updated expanded proof passes this audit with no outstanding mathematical correction.
