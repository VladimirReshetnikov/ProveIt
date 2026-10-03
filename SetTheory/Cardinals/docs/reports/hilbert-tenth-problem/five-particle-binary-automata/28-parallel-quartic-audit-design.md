# Independent audit: finite-horizon certificates for the new parallel CA

Date: 2026-10-03. Scope: mathematical design audit, based on reading the pinned sparse evaluator, its source metadata, `PROOF.md`, and `PARALLEL_RULE_PROOF.md`. No frozen source packet was changed or executed. The conclusions below concern the new E/P parallel blocks on every finite support, including malformed/multihead supports. They do not reuse the ordered-factor certificate semantics.

## Main findings

1. A fixed, source-sized, duplicate-free raw-occurrence circuit can enumerate source records, occupied pairs, distinct marker particles, endpoint orientations, and a constant number of template families. It need not enumerate the travel range or all F types.
2. With explicit phase-near side and explicit orientation, a safe total width across both families is

   K = binom(n,2) [8p + (22p+2a+2m) max(n-2,0)].

   The E block alone needs K_E = binom(n,2)[4p+(14p+2a)max(n-2,0)] slots. The P block alone needs K_P = binom(n,2)[4p+(8p+2m)max(n-2,0)] slots. Slots are fixed syntax; a raw bit masks invalid matches.
3. At an isolated candidate k, the before-key set inside radius b+r is exactly {k}. Therefore its prospective test can check that the recomputed after-key set inside that radius is exactly {k}; it need not perform a quadratic all-before/all-after membership comparison for every k. This reduction is valid only after isolation against all raw keys.
4. The two nontrivial anchor corrections are free-E reverse u=h-w and endpoint-interaction reverse u=z-v*delta. Losing either correction certifies the wrong rule.
5. Deterministic total gates, deterministic lane compaction/padding, and canonical signed natural pairs give a unique complete natural witness. Merely masking equations of inactive branches does not.

## 1. Notation and raw predicate

Use the source's immutable partition into m controls, p moving branches, and a direct branches. D=2m+4p, S=2D+2, Ltravel=3D+4, b=4D+5, Z=10b+10+2J. A block has r_E=Z+J or r_P=3b+1, and H=2(b+r). The gate's own exactness radius is ell_g=3B_g+1, where B_g=D+1 for pair templates and B_g=b for triples. In particular pair exactness uses Ltravel, not the triple radius.

Store the input support canonically as strictly increasing x_0<...<x_(n-1). For each candidate descriptor (ID,u,label,old,new,B,guard), its raw bit means:

- all two or three old endpoint sites are present;
- exactly that many particles lie in the closed interval [u-(3B+1),u+(3B+1)];
- the descriptor's fixed contextual guard, if present, holds;
- its family-specific gap, range, and incidence predicates hold.

The last line ensures the descriptor really denotes the intended source type. It is not an admissible-encoding assumption. No global unique-head or five-particle assumption is used.

Guard checks scan the n occupied coordinates in the two detector intervals [u-Z-J,u-Z] and [u+Z,u+Z+J]. A side with zero particles has class J+1; with one particle, its offset is the class; with more than one, the raw bit is false. Mask a rejecting class to a fixed valid dummy before table selection. The selected truth table is charged at its explicit (J+2)^2 size. There is no need to scan the physical J+1 sites.

The guard table belongs to the type, not the current orientation: dispatch uses the branch domain table on both orientations; commit uses the image table on both; direct uses the domain table on both; all remaining families are unguarded. In particular a minus-oriented dispatch does not switch to the image table.

## 2. Direct source-record generation and all anchor formulas

For an occupied pair h=x_i<h+d=x_j, i<j, let z=x_k for a distinct index k when a third particle is needed. Let e be one fixed moving branch, v=e.side, delta=e.delta, and w=v in mode O or -v in mode I. Let ell=0 denote the plus endpoint and ell=1 the minus endpoint. The matching gap must be the fixed signed gap for that endpoint's head mode/control. Every orientation-zero endpoint has odd gap; every orientation-one endpoint has even gap.

For each family below, generate at most one record for its fixed source record, pair, marker, and orientation. Travel t is computed from h-z; it is never a loop variable ranging over [S,Ltravel].

- Free-E, each moving mode: u=h for ell=0; u=h-w for ell=1. The endpoints are pair+(0) and pair-(w). No marker slot is used.
- Behind, each moving mode: u=z; t=w(h-z)-ell; require S<=t<=Ltravel. The endpoint head locations relative to u are wt and w(t+1).
- Ahead, each moving mode: u=z; t=-w(h-z)+ell; require S+1<=t<=Ltravel. The endpoint head locations are -wt and -w(t-1).
- Dispatch, each moving branch: u=z. At ell=0 match H_source+ with h-z=S. At ell=1 match O_e- with h-z=vS.
- Endpoint interaction, each moving branch: at ell=0 match O_e+ and use u=z; at ell=1 match I_e- and use u=z-v*delta. Both orientations require h-z=-vS. The reverse marker is z=u+v*delta, not u.
- Commit, each moving branch: u=z. At ell=0 match I_e+ with h-z=vS. At ell=1 match H_target- with h-z=S.
- Direct, each direct branch: u=z and h-z=S. Match H_source+ at ell=0 and H_target- at ell=1.
- Phase-free, each moving mode: u=h for both orientations. No marker slot is used.
- Phase-near, each moving mode and side s in {-1,+1}: u=z; t=s(h-z); require S<=t<=Ltravel. The endpoint head position is st in both orientations.
- Phase-home, each control: u=z and h-z=S; match H_q+ or H_q- according to ell.

Use the frozen arithmetic type-ID formulas so that the same (family,source record,travel t,side) retains its ID after the swap. The witness identity is (ID,u), not (family,u), not the current head location, and not the current marker location. Distinct types at one anchor remain distinct competitors.

For invalid range predicates, it is convenient to replace t by a fixed in-range dummy before constructing its ID and endpoint coordinates, while retaining the original false enabling bit. This keeps every descriptor total and bounded. Disabled records must never invoke a nonexistent source-table row. A literal constant dummy descriptor handles empty families.

### Proof of completeness and duplicate-freeness

Every endpoint has exactly one pair whose gap is at most D. For a triple, its remaining particle is farther than D from both pair particles; this remains true at the shifted endpoint-interaction reverse shape. Consequently a raw endpoint uniquely determines its occupied pair indices i,j and, for triples, its remaining marker index k. The listed formulas recover its t, side, orientation, and invariant anchor. Thus every true raw key is generated.

Conversely every record with raw bit one passes the literal endpoint/ell_g/guard definition and therefore is a genuine raw key. For one fixed (ID,u,label), the distinguished pair and marker make the generating slots unique. The nontranslation/distinctness of the two endpoints, together with exactness, prevents both orientations being raw at the same (ID,u). Thus true raw slots are duplicate-free, even on malformed input.

This proof relies on enumerating each family/source-record/orientation exactly once. Generating the same endpoint through both the generic discovery emitter and the direct family emitter would invalidate duplicate-freeness. If multiple routes are retained, canonical first-valid-occurrence deduplication by (ID,u) is required before any exclusion test.

### Width calculation

For every occupied pair:

- E pair slots: two modes times two orientations per moving branch = 4p
- E triple slots per distinct marker: behind/ahead (8p), dispatch/endpoint/commit (6p), direct (2a), total 14p+2a
- P pair slots: two modes times two orientations per moving branch = 4p
- P triple slots per distinct marker: two modes times two sides times two orientations (8p), plus home phase (2m)

There are binom(n,2) pairs and max(n-2,0) marker choices per pair. This proves K_E, K_P, and K above. If phase-near side is derived deterministically as sign(h-z) rather than enumerated twice, replace 8p by 4p in the P triple coefficient and 22p by 18p in K. Since t>=S>0, no zero-sign ambiguity arises for an enabled slot.

This source-enumerating width is intentionally looser in source size than dynamic metadata lookup. It is still O((m+p+a)n^3) and is not an F-entry template enumeration: no loop visits the Theta(D) travel positions per moving branch.

## 3. Alternative tighter dynamic-emission width

The frozen candidate-discovery formulas have exactly

C = binom(n,2)[Delta+3+4 max(n-2,0)]

fixed ID-emission slots: one home phase, Delta home incidences, two free moving slots, and four slots per distinct third particle. For every emission retain its originating occupied pair h<h+d. Its gap determines orientation ell=1-(d mod 2). Decode only that ID; find the unique close pair in the decoded endpoint by a constant-size scan of its at most three pairs; if its lower offset is a_g, set u=h-a_g. Requiring the decoded gap to equal d is a useful explicit check. The literal raw predicate then gives a correct occurrence slot.

This retains completeness and uses C occurrence slots, rather than the safe but much larger 2nC obtained by trying every first particle in both endpoint shapes. Duplicated emissions may produce the same raw key. Define the canonical raw bit at slot j as raw_j AND the negation of any earlier raw_i with (ID_i,u_i)=(ID_j,u_j). All duplicate slots remain fully determined internally. Only canonical raw bits participate in exclusion, prospectivity, and writes.

This option requires paid dynamic source lookups and a paid ID decoder. The source-enumerating construction in section 2 avoids those complications and is a reasonable first concrete implementation.

## 4. Isolation and prospective equality

For each true raw key k=(ID,u), compute isolation against every other true raw key in the same E or P family:

isolated_k = raw_k AND NOT EXISTS j: raw_j AND key_j != key_k AND |u_j-u|<=H.

The equality here includes type ID. Keys at the same anchor but with different IDs are different and conflict. A raw key that later fails prospectivity still participates in this isolation test. E and P do not compete with each other.

For an isolated k, form the hypothetical single-swap support Y_k and recompute the entire raw candidate circuit on Y_k. Do not restrict to IDs discovered on X. Newly born raw keys are exactly the obstruction prospectivity must detect.

Let q=b+r. Since q<=H and k is isolated, the initial raw key set restricted to |anchor-u|<=q is exactly {k}. Thus prospectivity is equivalent to both:

- the after raw map contains k in that closed interval;
- no after raw key distinct from k has anchor in that interval.

The endpoint-symmetry theorem guarantees k remains present with opposite orientation, but explicitly checking that fact is a useful binding/implementation safeguard. Orientation is excluded from the set equality itself. Comparing oriented triples would reject every genuine swap. Checking only absence of new keys without preserving the own key requires an explicit appeal to the endpoint-symmetry proof.

This shortcut does not weaken the full malformed-input rule; it uses a consequence of the full all-type isolation already tested. A literal general before/after set comparison is also sound, but should be counted honestly.

## 5. Hypothetical lanes, padding, and simultaneous output

Every raw endpoint contains at least two particles. Isolated keys have centers farther apart than H>=2b, so their endpoint supports are disjoint. There are therefore at most floor(n/2) isolated keys before prospective rejection.

Two sound circuit architectures are available:

1. All-slot architecture: for every fixed slot, hypothetically swap when its raw bit is true and otherwise use X; alternatively enable only when isolated. Compute every downstream circuit even if its result will not be selected. This is simple but pays a hypothetical discovery circuit per slot.
2. Compacted architecture: compute isolated bits for all slots, prefix-sum them in fixed slot order, and route the rank-r isolated descriptor to lane r for r<floor(n/2). Set absent lane presence to zero, descriptor fields to fixed dummies, and its support to X. Do not leave lane occupancy, source-slot index, or unused coordinates existentially arbitrary.

A literal source-slot scan with deterministic Boolean selects suffices for the routing; no sorting/set/permutation oracle is needed. The rank is a determined prefix sum. At most one source slot routes to each live rank. The mathematical isolated-count bound justifies the fixed number of lanes.

For every single hypothetical and the final simultaneous block, pair old/new endpoint sites in a fixed deterministic order. They need not be sorted if the fixed lists are already distinct and of equal length. Each original particle acquires the displacement of the unique selected old endpoint site it occupies, or zero otherwise. Common old/new sites need not be paired to themselves: the resulting set is still the endpoint replacement. Exactness prevents target collisions with unchanged particles; separation prevents collisions between selected keys.

Sort the resulting n coordinates by a fixed compare-exchange network with deterministic tie rules. This yields the canonical support for the next discovery circuit. Do not use an arbitrary existential permutation, because that would destroy unique witnesses. With genuine selected swaps the values are distinct; tie behavior nevertheless makes every gate total.

Every selection decision must be computed from the same immutable X. Updating X while scanning selected slots gives the old cascade behavior rather than the new parallel rule.

## 6. Natural witnesses and quartic conversion

An implementation can reuse the general primitive arithmetic method, but must bind the new parallel circuit rather than the old ordered scheduler.

Represent each signed wire v by natural v+,v- with v=v+-v- and v+v-=0. For a deterministic quadratic assignment v=f(previous wires), impose v+-v--f=0 and v+v-=0. The canonical signed pair is unique.

For comparison y>=x use natural beta,d and residuals

beta(beta-1)=0,
y-x-(2beta-1)d-beta+1=0.

They uniquely force beta=1,d=y-x when y>=x, and beta=0,d=x-y-1 otherwise. Equality, strict comparison, Boolean folds, arithmetic masks, and compare-exchanges reduce to bounded-fanin deterministic gates. Constant division, if used, needs canonical Euclidean quotient/remainder constraints; it is not a free primitive. The direct source-record design can avoid most or all such divisions.

Fully constrain all gates, including inactive branches, rejected raw slots, failed prospective lanes, and padding. A false mask only controls a downstream output; it must not remove internal defining equations. Never use one-sided implication constraints as a replacement for deterministic gate definitions when claiming a unique complete witness.

For fixed source, n, horizon T, and direction, compose exactly 2T block circuits (E then P forward, P then E backward). No event budget or ordered-factor cursor is required. Add initial-domain and requested endpoint equations. By topological induction every pre-acceptance wire has one natural value; endpoint acceptance keeps that complete assignment or rejects it. Summing squares of the degree-at-most-two residuals yields an ordinary integer polynomial of degree at most four with exactly one complete natural witness on the accepted input fiber and none otherwise.

A bounded horizon is fixed compiler syntax. This is not a single fixed-arity polynomial over an unknown horizon, a fixed number of existential variables for all n/T, or a claim about infinite-support inputs.

## 7. Coordinate bounds and paid resources

Let A=max |x_i|, or zero at mass zero. A block admits a particle transport of length at most 2b, since old/new sites lie in one common interval of radius b. Every true snapshot through T full steps therefore lies inside [-(A+4bT),A+4bT]. A hypothetical single swap from any such snapshot adds at most 2b. Invariant anchors and context endpoints add at most b+r to these magnitudes. Thus a safe geometric bound for true/hypothetical support, anchors, and detector endpoints is A+(4T+3)b+max(r_E,r_P), up to harmless constant slack.

Raw pair/marker differences can be twice the current coordinate bound. Comparator slack, count accumulators, fixed-source type-ID arithmetic, prefix ranks, and coefficient heights must be charged separately. Range-mask travel t before materializing descriptor shapes if using the preceding simple descriptor bound. Otherwise invalid ghost shapes can scale with the coordinate span and need a correspondingly enlarged, still finite bound.

No finite coordinate bound is necessary in the polynomial syntax when canonical signed natural pairs and exact comparisons are used. The bound is useful for witness bit length and verification cost, not as a hidden assumption restricting accepted supports.

For a source-enumerating block width K_b and c=(J+2)^2, one full raw pass has O(K_b(n+c+1)) bounded-fanin work when table rows are explicitly selected. All-slot isolation is O(K_b^2). With the isolated-before={k} simplification, the all-slot hypothetical design is O(K_b^2(n+c+1)+K_b n^2), apart from constant-sized descriptor arithmetic. Deterministic compaction to floor(n/2) lanes yields a bound of the form O(K_b^2+n K_b(n+c+1)+n^3), including routing/sorting under generous bounds. These are macro estimates, not measured residual counts.

An emitted circuit must report actual arithmetic/comparator/Boolean counts, residual counts, variable counts, and serialized coefficient costs. An F-sized constant packed as one gigantic integer would still need its bit length charged and would defeat the intended source-sized construction. Guard expansion still costs source-times-(J+2)^2; no polynomial-in-log J claim follows.

## 8. Edge cases and verification checklist

- n=0 or n=1: no endpoint is possible, every block is identity; all raw widths are zero. Avoid a nonexistent candidate-zero lookup.
- p=0: there are no moving modes; direct E and home-phase P remain. Empty E is allowed.
- T=0: identity/target checks only; if sorted canonical input is an external promise, no internal sorting witness is needed; otherwise pay its domain checks.
- Empty/inactive lanes must have fixed dummy payloads and X as hypothetical support.
- Closed interval endpoints matter: raw exactness, detector intervals, exclusion <=H, and prospective radius <=b+r must use inclusive bounds.
- Use gate.L=3*gate.B+1, not old raw radius B and not uniform triple L.
- Never restrict prospective discovery to initially seen IDs.
- Always compare candidate keys by both ID and invariant anchor, never orientation.
- Guard-rejected occurrences are not raw; raw-but-nonisolated and raw-but-prospectively-rejected keys still compete.
- Phase-home and direct templates must distinguish source controls even when multiple endpoints look locally similar elsewhere.
- Direct source loops require each family/orientation exactly once; generic emitted-ID duplicates need canonical dedup.
- Check both directions by reversing block order, not by reversing slot order.
- The malformed frozen cascade fixture must remain fixed under the new whole rule; certifying its old ordered image would expose semantic carryover.
- A finite test corpus and one-coordinate witness mutation tests are useful binding checks, but do not replace the all-input raw completeness, duplicate handling, or topological uniqueness proofs.

## Conclusion

No mathematical obstruction was found to the proposed fixed-slot, source-record-enumerating compiler. Its cleanest foundation is the unique-close-pair endpoint parametrization, followed by complete after-swap rediscovery and deterministic arithmetic gates. The main risks are concrete binding mistakes: reverse anchors, template-fixed guards, duplicate self-competition, orientation-sensitive key equality, incomplete prospective candidate sets, and unconstrained ghost/padding witnesses. Exact emitter audits should target those points first.
