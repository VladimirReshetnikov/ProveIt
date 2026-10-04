# Independent audit: short triple exactness with unchanged pair padding

Date: 2026-10-04 UTC. Disposition: **PASS, with the dependency and evidence limits below. No mathematical correction is required.**

## 1. Result and scope

I independently reconstructed the local-involution, admissible-geometry, boundary, and support arguments from the literal endpoint families. I found no defect in shortening triple exactness from `3b+1` to `b=4D+5` in **both newly defined blocks**, retaining pair exactness `L=3D+4`, with `D=2m+4p` and the inherited source-interface assumptions.

The construction is a new binary full-shift map `F_s=P_s E_s`. Both `E_s` and `P_s` are individually full-shift involutions and conserve ordinary finite particle number. They and their inverse composition agree with both predecessors on the entire specified admissible doubled micrograph. The main sufficient radius is

`R(F_s) <= 76D+105+3J`.

For the **same map**, the phase changed-output support yields

`R(P_s) <= 6b-1`, and `R(F_s) <= 76D+104+3J`.

The inherited substitution `D=509508,J=0` gives respectively **38,722,713** and **38,722,712**. These are sufficient bounds. Neither is established as the exact or minimum radius. The universal table with digest `fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3` is absent from the preserved Report26 archive. Its ledger and universality are inherited premises, not freshly proved or executed evidence.

This is a mathematical and static-evidence audit. No author/upstream scientific code, source interpreter, CA/physical/trajectory simulator, saved schedule, or Lean was executed. No publication, upload, source rewrite, permission change to a source object, or Report26/Report70 modification was performed. The predecessor radius-two appendix is outside this continuation's mathematical review; its sealed objects were authenticated because they occur in the accepted audit manifest.

## 2. Authenticated objects and what was read

The supplied roots were `/workspace/shared/short-exactness-radius-20261004/proof-packet` and its ZIP sibling. These exact digests were freshly checked:

| Object | SHA-256 |
|---|---|
| Short-exactness manifest | `72f8024c49a364bfd26ccc9f0e89d128e4390c1bf045477aa3d584bba3eaea31` |
| Short-exactness ZIP | `9bb5e63a780770689a5b7d353a130dee7535330e021202201d5c751d62601d37` |
| Short-exactness PROOF.md | `d2229bcae33affd26eefb513e942891edf1d09c8b8d9e32ab1f8220fd2ea9962` |
| Accepted predecessor manifest | `f1c19ca86641cbf5ebaed81d0c78e82563258753bbf8f38f2f46229247b71fa0` |
| Accepted combined audit manifest | `3bfe65db1ad9c0aab9fd13641cfbad843a292d2c2dbec444fa0f7ebb856876b1` |
| Accepted predecessor ZIP | `a3739bdd0d9015ea4c69f3a0b8b8fb6f0bd6828a6aa5251a08e902a1ca3d04b6` |
| Included/recovered Report26 ZIP | `20a23b1ee22aed461942da4def6bade2bd55d777fce1fe49b6ff83248b7442e4` |
| Literal frozen compiler | `f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f` |
| Report26 parallel implementation | `2c8b639646a587a51bddeaac16e46d2dbd8c4e8138ac67a2601025334d4a64cd` |

All mathematical prose in the current `PROOF.md`, `COMPILER_PROOF.md`, `Report26-PROOF.md`, both Report26 lemma/preservation audits, the accepted two-scale proof, accepted independent audit, and accepted fresh audit was read in full as inert text. I also read the packet README/preservation statement, both supplied helper programs as inert text, and the complete original frozen compiler and Report26 parallel implementation as inert ZIP member text. JSON manifests, dependency origins, preservation records, and arithmetic evidence were parsed as data. No instruction or replay command contained in those inputs was executed.

The fresh `authenticate.py` verifies:

- Both caller-supplied pins and all additional inherited pins above
- All 21 current manifest entries, including their recorded modes and nanosecond mtimes
- All 21 predecessor manifest entries and all 17 accepted-audit entries, including the latter's recorded modes and mtimes
- Exact ZIP and extracted-file inventories, and byte equality for both 22-file packet archives
- All 48 Report26 archive files, its 46 release-manifest entries, 35 mandatory source pins, 26 scientific-manifest entries, and all 27 scientific SHA256SUMS lines
- Duplicate JSON keys, duplicate ZIP member names, unsafe member paths, and symlink entries are rejected
- All 10 current dependency origins and all 9 predecessor copied dependencies match their authenticated origins byte for byte
- The historical current-packet preservation delta is reproduced exactly

`check_original_copies.py` additionally verifies the recovered Report26 archive against the included archive, the preserved **partial** inert extraction's 35 files against their ZIP members and historical inventory, and all 69 original-state entries against the accepted audit's equal before/after snapshots. It found no changes since that audit.

The supplementary check's first development run incorrectly assumed the inert tree was a complete extraction and stopped at its inventory check. Inspection showed the preserved tree intentionally excludes executable/other unextracted members. The revised, fully inspected helper compares its exact historical partial inventory and independently authenticates every present member; the main archive verification still covers all 48 files. This was a checker assumption error, not an input or mathematical defect. No source object was changed to satisfy it.

These hashes authenticate identity relative to supplied pins and mutually consistent manifests. They are not digital signatures, proof of authorship, or proof of the missing universal-source theorem.

## 3. Endpoint, guard, and same-anchor audit

Set `S=2D+2`, `B2=D+1`, `L=3D+4`, `b=L+D+1`, `Z=10b+10+2J`, and `r=Z+J=10b+10+3J`. Every accepted source has at least one control, so `D>=2`; `J>=0`.

The displayed edge endpoints match the inert compiler's literal free, behind, ahead, dispatch, endpoint, commit, and zero-update direct families. The phase endpoints match its free-moving, near-moving on both sides, and home families. In particular, the independent head coordinate remains the leftmost particle even for negative direction. Nothing reflects or reverses the order of the head pair.

The endpoint supports fit their declared write windows. Direct extrema over `1<=d<=D`, both physical signs, and the complete permitted distance ranges give:

| Family | Containing support interval |
|---|---|
| Free edge | `[-1,D+1]`, inside `I_B2` |
| Behind edge, both orientations | `[-(L+1),L+D+1]`, inside `I_b` |
| Ahead edge | `[-L,L+D]`, inside `I_b` |
| Dispatch/commit/direct | `[-S,S+D]`, inside `I_b` |
| Endpoint, both sides and update signs | `[-S-1,S+D+1]`, inside `I_b` |
| Near phase | `[-L,L+D]`, inside `I_(b-1)` |
| Free/home phase | `[0,D]` / `[0,S+D]`, inside `I_(b-1)` |

The two signed gaps are distinct, so each pair of full endpoint words is distinct and has equal weight. Each `tau_(g,u)` is therefore a genuine everywhere-defined word transposition, fixing every other word. For pair types the write interval remains `I_B2(u)`. Bits in the common `I_b(u)` outside that small interval are retained, not zero-filled. This is essential when a marker lies at distance `L+1` from a free key.

New exactness is `L` for pairs, `b` for triples. It implies the corresponding local endpoint word. Class guards retain the finite reads at `u±(Z+k)`, `0<=k<=J`, which lie outside the rewrite window. The inherited concrete class convention rejects multiple occupied sites and maps all-zero reads to the tail class. More generally the full-shift proof only needs a fixed bounded extension that is invariant under its own paired swap. The retained guards satisfy this on arbitrary malformed inputs, not just admissible inputs.

At an edge anchor, the type set `C_u` must contain **all** guarded types. If `C_u(x)={g}=C_u(tau_g x)`, then at the image the same unique type passes and its involution returns `x`. If either uniqueness test fails, `T_u` is identity and remains so on reapplication to that same input. This exhausts zero, multiple, conflicting, and newly enabled-type cases. No priority selection is hidden in the definition.

The replacement word of `T_u` reads only `I_r(u)`. A hypothetical type test uses the already known substituted bits inside the window and unchanged bits elsewhere in that same window; no extra radius is added. Nontrivial action implies unguarded geometric recognition at that integer anchor. Coalescing raw types at one anchor is correct here; coalescing them in `C_u` would not be.

## 4. Full-shift edge proof, including every rejected status

The raw recognition radius is `a=b`. Let `R(x)` be the set of recognized integer anchors. Since `r>=3b`, the required exclusion is

`H=max(4b,b+r)=b+r`.

Only recognition windows centered within `2b` of `u` can be changed by `T_u`. Their input bits lie in `I_3b(u)`, and the local replacement reads `I_r(u)`. Thus the global-looking equality `R(T_u x)=R(x)` is a finite test of `I_r(u)`.

Selected centers are more than `H` apart, so their closed write intervals are disjoint. If a recognition window `I_b(v)` met writes at two selected centers, those centers would be at distance at most `4b<=H`, a contradiction. Every recognition predicate after the simultaneous update therefore sees either its unchanged old word or exactly the word produced by one selected local update. That update passed the entire raw-anchor prospective test. Consequently `R(E_s x)=R(x)` at every integer anchor, including initially absent anchors on dense or infinite inputs. Cooperative births or deaths cannot occur.

It remains necessary to prove invariance of the **whole selected set**, not only of the moves initially chosen. Let `u` be any recognized isolated anchor. Every other selected center `w` satisfies `|w-u|>H=b+r`, so its radius-`b` write is disjoint from `I_r(u)`. This protects all control and prospective data.

1. An isolated but rejected anchor sees no change in its determining word, so its failed prospective test remains failed
2. A selected anchor sees exactly its own `T_u` image, and `T_u^2=id` interchanges the two raw sets in its prospective comparison, so it remains selected
3. A nonisolated recognized anchor remains nonisolated by raw-set invariance, regardless of guard/type changes there
4. An absent anchor remains absent by raw-set invariance
5. A recognized isolated identity control passes prospectivity harmlessly; its protected determining word cannot turn it into a different control on the second application

These cases exhaust all input anchors. The second update uses the same selected controls with no other selected write in any of their control words and undoes each disjoint local change. This proves `E_s^2=id` on the complete binary full shift. Empty edge families cause no exception.

Equal-weight replacement on disjoint blocks conserves ordinary particle number for finite inputs. Only finitely many nontrivial blocks can act on such an input, because each consumes at least one original particle from its disjoint write block. Thus finite support is retained. The proof does not equate divergent infinite sums.

Isolation reads `H+b` about a possible writing anchor; control/prospectivity read `r`. An output site need inspect anchors within `b`, giving

`R(E_s)<=b+(H+b)=3b+r=13b+10+3J`.

All tests are finite Boolean tests and translation-covariant. All intervals are closed and equality at `H` is excluded. No one-site endpoint overlap is silently allowed.

## 5. Full-shift phase proof and typed collisions

The new phase rule uses type-anchor keys `(g,u)`, ignoring endpoint orientation but retaining the type. Its common candidate read radius and write bound are both `b`. Isolation is at `H_P=4b`; prospective equality compares the complete typed candidate set. Only anchors within `2b` can have changed candidate predicates, so the prospective word is `I_3b(u)`.

A candidate window cannot meet two selected writes, because that would put their centers within `4b`. Each post-update candidate predicate is therefore unchanged or agrees with one individually prospectively stable transposition. This proves invariance of the **entire typed candidate set**, including births of another type or keys that were initially absent.

For any isolated candidate, another selected write lies beyond `4b` in center distance and its radius-`b` support misses the candidate's radius-`3b` decision word. Rejected isolated candidates retain their failed prospective test. A selected key's own involution reverses the two sides of its comparison and preserves success. Nonisolated keys stay blocked, and noncandidates stay absent. Thus the full selected-key set is invariant, and the second application restores every selected word.

No uniqueness theorem is assumed on malformed phase configurations. Several types at the same anchor are distinct competing keys and are all rejected by typed isolation. This is different from the edge's raw-anchor coalescing construction, and the proof respects that distinction.

Hence `P_s` is a conservative full-shift involution. Isolation reads `5b` about an anchor, prospective data read `3b`, and a potentially writing anchor lies within `b` of an output site. Therefore `R(P_s)<=6b`.

## 6. All-anchor geometric audit of admissible preservation

Admissible means every natural-counter home and exactly the strict intermediate nodes of enabled source-edge subdivisions, with both signs and all translates. Guard-invalid moving geometry is excluded. Deterministic source domains and exact actual-image domains are disjoint on **all** natural IDs, not merely on a chosen computation.

Every admissible state has one pair of occupied sites at distance at most `D`, namely the head. Every head-marker distance is at least `S-D=D+2`, and marker-marker distances are at least `Z`. Every endpoint template likewise has exactly one close pair. Thus every candidate at **any integer anchor** must use the actual head pair, its distinct signed gap fixes its signed mode, and any singleton displayed by a triple must be an actual marker. No background pair or alternative grouping can match.

Each triple's singleton is within `L+1` of the actual head anchor, even the reverse behind endpoint and translated endpoint interaction. Since `Z>2(L+1)`, two different actual markers cannot support competing raw triple matches of different types. Merely bounding one template's diameter would not establish this cross-template conclusion; the common head-to-marker bound does.

For every ordinary triple its invariant anchor is its singleton marker. The remaining markers are at least `Z` away. At a reverse endpoint the old invariant anchor is one site from the updated singleton, so remaining markers are at least `Z-1` away. Since `Z-1>3b+1>b`, every geometric triple match contains exactly its three displayed particles both in the old large exactness window and in the new one. Pair predicates are unchanged. This proves old/new geometric recognition equivalence over **all anchors** on admissible states, not just existence of the intended match.

### 6.1 Home branch alternatives

At `H_q+`, only outgoing dispatch/direct forward endpoints have the required gap; all force the origin key. At `H_q-`, only incoming commit/direct reverse endpoints have the gap, again forcing the origin. Moving free or travel templates cannot use a home gap.

Raw edge types can be multiple at the origin, but raw **anchors** are empty or singleton. Full guarded types are empty or singleton by source-domain disjointness for plus homes and exact-image disjointness for minus homes. The guard's class reads are faithful: markers encode the classes and the head lies inside `b<Z`. An exact image includes existence of natural pre-counters, ensuring reverse commit enters an enabled subdivision. A forward guard substituted for the image guard would not prove this, and is not used.

If a home has raw branch alternatives but no enabled incident edge, every local control is identity; the new block fixes it. Direct zero-update branches retain the same domain/image predicate because their counters do not change. At a desired home incidence the same unique type is present at its paired endpoint.

### 6.2 Both signed corridor partitions and all equalities

Write moving direction `w`, departure marker `A`, destination marker `C`, `N=w(C-A)>=Z`, and `t=w(x-A)`, with `S<=t<=N-S`. For outbound travel `w=v` and `N=Z+c`; inbound uses `w=-v` and `N=Z+c+Delta`, still at least `Z` because enabled outputs are natural. The third marker is remote.

The exact partitions derived from the literal endpoints are:

| Sign | Type | t interval | Key |
|---|---|---|---|
| plus | behind | `S..L` | `A` |
| plus | free | `L+1..N-L-1` | `x` |
| plus | ahead | `N-L..N-S-1` | `C` |
| plus | forward interaction | `N-S` | interaction key |
| minus | reverse interaction | `S` | interaction key |
| minus | behind inverse | `S+1..L+1` | `A` |
| minus | free inverse | `L+2..N-L` | `x-w` |
| minus | ahead inverse | `N-L+1..N-S` | `C` |

For plus the free predecessor key is `x`, so exactness is `L<t<N-L`. For minus it is `x-w`, not `x`, yielding `L<t-1<N-L`. Integer conversion gives exactly the table. Literal behind endpoints have departure distances `S..L` and `S+1..L+1`; literal ahead endpoints have arrival distances `S+1..L` and `S..L-1`. These ranges and the free ranges are disjoint and exhaustive because `N>2(L+1)`.

- Behind equality `L -> L+1` uses the same triple key. The inverse free predecessor key still sees the departure marker at distance `L`, so it fails exactness
- Ahead equality `L+1 -> L` uses the same free key. That predecessor still sees the arrival marker at `L+1`; reverse ahead triples end at current distance `L-1`, so cannot compete
- At plus arrival distance `S`, forward travel is absent and the forward interaction is the only incidence
- At minus departure distance `S`, inverse travel is absent and the reverse interaction is the only incidence
- The immediately adjacent `S+1` and `N-S-1` states are the stated travel cases; no missing or overlapping integer boundary remains

The same algebra covers `w=-1` without changing the leftmost-head convention. Within a triple range the signed gap, unique possible marker, side, and integer distance determine one type. Hence there is exactly one moving raw type-anchor, not just one intended type among unexamined alternatives.

### 6.3 All interaction types and the old reverse marker

- Outbound minus at its departure wall is reverse dispatch at the origin, with the true domain guard inherited from the enabled corridor
- Outbound plus at arrival is forward endpoint at the old selected marker `m`
- Inbound minus at departure is reverse endpoint at **old** marker key `m=m'-v*Delta`
- Inbound plus at arrival is forward commit at the origin, with the exact image guard true on its post-counters

The reverse endpoint's singleton has offset `v*Delta` and its head anchor has offset `v*Delta-v*S`. Both independently force `u=m'-v*Delta`. Choosing current marker `m'` as key would be wrong for either nonzero update sign. The actual singleton-head distance is `S`; only the invariant key is shifted. Other markers remain beyond `Z-1`, so old and new exactness both hold there. This covers `v=±1` and `Delta=±1`.

Distinct branch-specific O/I gaps exclude all other interactions. For the same branch, a matching actual singleton forces the stated wall, where travel is absent by the table. The remote third marker cannot generate a second interaction anchor.

### 6.4 Intended edges pass all new tests

For each intended edge, both endpoints are admissible, their full guarded set at the invariant key is the same singleton `{g}`, and their raw anchor sets are the same singleton. The key is the predecessor head anchor for free travel, the actual contacted marker for near travel, the origin for home interactions/direct edges, and the old selected marker for endpoint interaction. Thus mutual uniqueness, isolation, and raw prospectivity all pass. At missing edges the block fixes the state. This proves agreement for every source branch, every admissible counter size, both signs, every translate, and both reflection ends.

### 6.5 All phase cases

A home has exactly its home-phase type at the origin; no free-home type exists. A moving state has the free phase type at unchanged head anchor `x` exactly when both corridor markers are farther than `L` from `x`. Otherwise exactly one marker has distance in `S..L`, and its side/distance identify the unique near phase type. Unique close-pair and all-anchor marker arguments exclude every other candidate.

A phase swap fixes markers, head anchor, and unsigned mode; only the signed gap changes. Consequently its entire typed candidate set is the same singleton before and after. This checks both signs at every free/near equality and the home case. Isolation and prospective stability pass automatically.

## 7. Radius refinement is for the exact same rule

For phase near endpoints, `+L+D=b-1` is an attained bound of the containing support calculation, including `t=L,d=D`. Negative-side endpoints lie between `-L` and `-S+ D`; home/free endpoints are closer. Thus every phase endpoint word has zero at both `-b` and `+b`.

On a non-endpoint local word the transposition is identity. On an endpoint it preserves those two boundary zeros. Therefore on **every full-shift input** a phase transposition can change only sites inside `I_(b-1)`.

This does not remove either boundary bit from triple recognition, does not shrink the full endpoint-word read interval, and does not change `H_P=4b`, typed isolation, or prospectivity. The map is unchanged. The established eligibility read radius remains `5b`; only potentially changing anchors for one output site shrink from radius `b` to `b-1`. An output is determined by its old bit and those possible changes, giving `R(P_s)<=5b+(b-1)=6b-1`.

The edge family cannot use this same simple common-support argument: a positive reverse-behind endpoint at `t=L,d=D` reaches `L+1+D=b`. This observation is not a lower bound on the map's true radius; it only explains why the displayed one-site support proof was applied to phase.

Composition radii add, so the main bound is `(13b+10+3J)+6b=76D+105+3J`, and the support corollary is one less. Independently evaluated substitutions are:

| D | J | Edge | Phase main | Composite main | Same-map refined |
|---:|---:|---:|---:|---:|---:|
| 8 | 0 | 491 | 222 | 713 | 712 |
| 18 | 1 | 1014 | 462 | 1476 | 1475 |
| 509508 | 0 | 26494491 | 12228222 | 38722713 | 38722712 |

## 8. Direct malformed inequalities, without a simulator

Use ordered controls `(q,h)` and one true-guard right increment to `h`. This source is deterministic and partial-injective; its exact image is right-counter positivity, so `J=0` suffices. Inert literal gap order gives `Hq±=1,2`, `Hh±=3,4`, `O±=5,6`, and `I±=7,8`. Hence `D=8,S=18,L=28,b=37,K_old=112,Z=r=380`.

### 8.1 The shortening changes each block and the composition

Let `X={0,18,23,80}`. The sole close pair is `{18,23}` with O-plus gap 5. Any match must use that pair. Only particle 0 is within the possible triple singleton distance `L+1=29`; particle 80 is 62 from head anchor 18. The free edge/phase pair fails because marker 0 is in the radius-28 window centered at 18.

The sole geometric edge endpoint is behind O at distance 18, key 0. The sole geometric phase endpoint is near O on the positive side at distance 18, key 0. Both predecessors use radius-112 triple exactness and see the extra particle 80, so both predecessor edges and their common old phase fix `X`.

The new edge sees exactly `{0,18,23}` in `I_37(0)` and exchanges it for `{0,19,25}`, preserving particle 80. At this O-minus endpoint the reverse-behind type is uniquely present at key 0; the free inverse key is 18 and still sees marker 0. No other actual singleton can fit. Both guarded uniqueness tests and the same-singleton raw prospective test pass. Therefore

`E_s(X)={0,19,25,80} != E_26(X)=E_*(X)=X`.

Directly on `X`, the unique new near-phase key exchanges gap 5 for 6 while retaining head anchor 18. Its reverse word has the same sole typed key. Hence

`P_s(X)={0,18,24,80} != P_26(X)=X`.

On `E_s(X)`, phase uses near O at distance 19 and changes gap 6 to 5, again with the same singleton typed key. Thus

`F_s(X)={0,19,24,80}`, whereas `F_26(X)=F_*(X)=X`.

This establishes actual inequality of each new block and of the composition, rather than merely an altered definition or an inferred possibility of differing behavior. It is a four-particle malformed input.

### 8.2 The changed phase filter also matters

For `Y={0,5,200,205}`, there are exactly two free O phase keys at 0 and 200. Any triple would require a singleton within 29 of its head, unavailable in either two-particle cluster. Each individual phase flip preserves the two free keys and creates no cross-cluster close pair.

New phase exclusion is `4b=148`, so both keys are isolated. Old phase exclusion is `2(b+3b+1)=298`, so neither is isolated. All edge versions reject their two edge anchors because `200<=417<=834`. Therefore

`F_s(Y)=P_s(Y)={0,6,200,206}`, while `F_26(Y)=F_*(Y)=Y`.

The fresh certificate checks eleven explicit finite-word intersections and the threshold arithmetic for these literal sets. It contains no template enumerator, generic CA step function, or trajectory loop. Exhaustiveness of the listed candidates is established by the preceding close-pair/singleton reasoning, not by interpreting these data as a simulator.

## 9. Exact scope of the pair-radius failure examples

These examples concern **loss of admissible simulation agreement with unchanged literal template ranges and the stated selector**, not failure of the all-input involution proof and not a universal lower bound for different encodings/rules. They need a source with an enabled nonzero branch, so an admissible moving corridor exists. Sources with no such branch do not supply these examples.

For any integer `B2<=ell<L`, take a plus head at departure distance `t=L` in an enabled corridor. Its intended behind triple at departure marker `A` still matches. The free pair at head key `x` now also passes its shortened exactness: `A` lies at distance `L>ell`, and the other markers are remote. The two distinct raw anchors are at distance `L`, within the fixed `H`. They therefore conflict, and the intended travel edge is rejected. There are no unnoticed same-anchor alternatives: the mode is fixed and the complete all-anchor classification applies. The corridor exists at this position because `N>=Z>2(L+1)`.

For any integer `ell>L`, take a plus head at departure distance `L+1`. Its original free edge is suppressed by the departure marker now lying in the pair exactness window. No behind-plus template extends past `L`; the arrival and third markers are too distant to give any triple, and this is not an interaction wall. Hence no raw edge type can perform the intended free step. This failure persists even if the enlarged predicate's read-radius bookkeeping/exclusion is adjusted: absence of the intended geometry is decisive. If `ell` exceeds the original common read bound, retaining that bound would itself be an additional locality error, but it is unnecessary for the counterexample.

Thus the literal subdivision makes exactly `L` the retained pair padding for this particular unchanged simulation construction. The statement does not prohibit redesigned contact ranges, recognition, encoding, or selection from supporting different padding.

## 10. Transported consequences and limits

The new restricted edge is the same matching and the new phase is the same sign flip. Both preserve the admissible set. Forward compositions therefore agree step by step, and inverse compositions agree in reversed block order. The inherited five-particle encoding, binary alphabet, observer length `3D+3`, clock `3+2(Z+c)+Delta-4S` for a nonzero source edge, and one-step zero-update clock are unchanged.

The clean-target first time `2Theta+2` and reflected period `4Theta+6` transfer on the original hypotheses. The clean-target wrapper still needs a **control-wide** predecessor-free initial normalization and recomputation of enlarged-source constants. Equating positive return/periodicity with designated halting still needs no nonfinal blocking on the claimed input family. A nonfinal stuck home otherwise reflects and cycles too.

The template count remains `8pD+29p+m+a_source`. Two mathematical involutions do not imply two inexpensive arithmetic factors or template-independent Boolean running time. Old source programs, malformed-input traces, ordered-factor verifiers, arithmetic/Diophantine certificates, and circuit counts do not become implementations or certificates of this new full-shift rule. Only admissible semantic witnesses transfer automatically through the proved agreement.

I did not reprove the historical universal source, externally survey priority, test an implementation of the new map, prove radius minimality, or formalize the theorem in a proof assistant.

## 11. Fresh evidence and source preservation

Three fresh helper programs are included and were read in full before execution. They use only standard-library archive/JSON/hash processing, affine integer arithmetic, and fixed finite-word intersections. None imports an input program. `static_certificates.py` independently derives 30 affine assertions using nonnegative variables `(D-2),J`, eight endpoint support envelopes, all three numeric substitutions, and eleven literal word intersections. It also checks the nonnegative affine assertions and record types in the supplied 408-record arithmetic JSON as inert data. The supplied checker was inspected but not run.

The fresh `before.json` snapshot was taken after initial inert textual inspection and authentication-helper preparation; it is not represented as preceding all reads. It records 117 frozen source objects and 204 separately observed live Report70 objects. `after.json` and `preservation.json` record the final comparison of bytes, file sizes, modes, nanosecond mtimes, types, and complete observed object sets. Directory modes/mtimes are included. Atimes are outside this preservation scope and may change through reading. These are endpoint observations, not proof of a continuously unmodified interval or atomic filesystem snapshots.

The final comparison **passed with no differences** in either category: all 117 frozen objects and all 204 live Report70 objects match between this audit's observations, from 2026-10-04 15:39:29.924008 to 15:48:32.615844 UTC. This later equality does not replace or negate the historical live-tree qualification below.

The source packet's historical preservation interval, 2026-10-04 15:24:54.675013 through 15:32:53.244416 UTC, is explicitly **not** a static-live-Report70 claim. Its 49 frozen entries matched, while 49 new live Report70 file/directory entries appeared and the existing `qa` directory mtime changed. The fresh helper exactly reproduces that delta from the authenticated historical before/after records. This qualification remains true even if the later audit's live snapshots match. The mathematical inputs are the pinned frozen sources, not the live Report70 QA tree.

This separate dossier is sealed read-only after review, with its own file manifest, SHA-256 digest, ZIP, and verified archive round trip. Read-only filesystem mode and a digest seal detect/impede accidental edits; they are not cryptographic signatures or a guarantee against an authorized actor deliberately changing permissions and resealing. No source packet or numbered report is included in the set of objects this worker chmods or writes.

**Final mathematical disposition:** accept the new short-exactness construction and the same-map one-site support refinement within the stated source and admissibility hypotheses. Retain all inherited-universality, implementation, certificate-transport, pair-radius-scope, and preservation qualifications above.
