# Fresh independent audit of the frozen two-scale proof packet

Date: 2026-10-04 UTC

## Verdict and precise scope

**PASS: no mathematical defect found in the new two-scale lemma, its literal Report26 specialization, the all-admissible agreement theorem, or the stated sufficient radius.** The separate radius-two classification is also independently certified by a graph-coboundary enumeration, rather than by importing either appendix program or repeating its particular leading-/trailing-zero implementation.

The source-uniform result is a newly defined binary full-shift CA `F*=P26 E*`, with both displayed factors number-conserving full-shift involutions, preserving the entire inherited admissible doubled micrograph and having sufficient radius

`108D + 149 + 3J`, where `D=2m+4p`.

At the inherited universal ledger this is **55,027,013**, versus Report26's **91,711,698**. This is an authenticated ledger substitution in a proved source-uniform theorem. The universal source itself is absent, its universality is not freshly proved, and neither a universal table nor a new-rule executable/evaluator was constructed or run. No minimality or external-priority result follows.

The packet and all inspected upstream artifacts remain byte-, mode-, and modification-time-identical to the audit snapshot. No archive program, author scientific program, source-machine interpreter, CA/physical/trajectory simulator, proof assistant, or Lean was run. The only fresh executions were archive/JSON/hash processing, integer ledger arithmetic, and the separately inspected static finite Boolean/graph certificate checker. There were no uploads.

## 1. Fixed evidence and authentication

The independently checked trusted digests are:

- Frozen outer ZIP, 498,226 bytes: `a3739bdd0d9015ea4c69f3a0b8b8fb6f0bd6828a6aa5251a08e902a1ca3d04b6`
- New `PROOF.md`: `9eb76ef7142a98b67e90cceb209f16af0b1f1057adfb30ddedfcb6e97b6616c2`
- Frozen prior `INDEPENDENT_AUDIT.md`: `076de66d7e6ffba255df3d64f58a0e2df48ac215b6a781718efd070c18b300f6`
- Included original Report26 ZIP, 442,422 bytes: `20a23b1ee22aed461942da4def6bade2bd55d777fce1fe49b6ff83248b7442e4`

Fresh `authenticate_static.py` checks duplicate JSON keys, duplicate archive member names, unsafe member paths, symlink entries, exact file inventory, lengths, and SHA-256 values. It verifies:

- All 21 files listed by the new manifest and the manifest's presence as the 22nd packet ZIP entry
- Byte-for-byte identity of every outer ZIP file and the frozen extracted packet
- Identity of the included Report26 ZIP and the original recovered archive
- All 48 original Report26 ZIP files: the 46 release-manifest entries plus manifest and its digest file
- All 35 original mandatory source pins
- All 26 scientific manifest entries and every scientific SHA256SUMS line
- All 9 copied proof/ledger dependencies against the original ZIP entries
- All example ledger fields by fresh arithmetic
- Unchanged hashes, sizes, modes, and `mtime_ns` over a 69-entry original-file/directory snapshot

The source-template comparison used the actual original ZIP's `scientific/frozen_reversible_binary.py` and `scientific/parallel_particles.py` as inert text, not an assumed reconstruction. Relevant proof sources were the new full proof, original `scientific/COMPILER_PROOF.md`, original `scientific/PROOF.md`, Report26 LaTeX, and the existing preservation audit. The new frozen prior audit was consulted after independently reconstructing the principal proof and boundary arguments.

The outer trusted digest authenticates the exact delivered object relative to that digest. Internal manifests are consistency checks, not digital signatures or independent proof of the historic universal source.

## 2. Independent full-shift proof of the two-scale lemma

Let `I_t(u)=[u-t,u+t]∩Z`. Assume `0<=b<=a<=r`, a radius-`a` translation-covariant recognition predicate `rho`, and everywhere-defined involutions `T_u` that fix the complement of `I_b(u)`, have replacement word determined by `I_r(u)`, preserve the number of bits equal to one in `I_b(u)`, and can act nontrivially only at a recognized anchor.

Set

`q=max(r,b+2a)` and `H=max(2(b+a),b+r)=b+q`.

Recognized anchors are selected precisely when they have no other recognized anchor at distance at most `H` and satisfy the prospective equality `R(T_u x)=R(x)`.

### 2.1 Locality of the global-looking prospective condition

Only predicates centered at distance at most `b+a` from `u` can see a change in `I_b(u)`. Their original input words lie entirely in `I_(b+2a)(u)`. Computing the hypothetical replacement additionally uses `I_r(u)`. The equality of the two entire recognized-anchor sets is therefore determined by `I_q(u)`. The test is finite and is not an eligibility recursion.

This reasoning does not conflate a predicate's input window with the transposition's support. It also does not assume that the guard radius is the short recognition radius.

### 2.2 Simultaneous cooperative births and deaths are excluded

Distinct selected anchors are more than `H` apart, hence their closed write intervals are disjoint. A radius-`a` recognition window intersecting write intervals at `u` and `w` would imply

`|u-w| <= 2(b+a) <= H`,

contradicting isolation. Every recognition window after the simultaneous update thus equals its original window or the window after exactly one selected `T_u`. The prospective equality for that `u` preserves the predicate. Hence `R(Ax)=R(x)` for **all** anchors, initially absent or present.

This is a coordinatewise proof on arbitrary bi-infinite configurations; no finite-support approximation, convergence argument, or density assumption is being used.

### 2.3 Every initially rejected status is protected

Take any initially recognized isolated anchor `u`, selected or rejected. Every other selected anchor `w` is a different recognized anchor, so `|u-w|>H=b+q`. Thus `I_b(w)` is disjoint from all of `I_q(u)`, including both the entire control window and the entire prospective-comparison window.

- If `u` is rejected, its determining word does not change at all. Its prospective test remains false
- If `u` is selected, the determining word after all simultaneous changes agrees exactly with that of `T_u x`. Since `T_u²=id`, evaluating its prospective equality at `T_u x` interchanges the original two recognized sets. It remains true
- If `u` is recognized and nonisolated, recognition-set invariance preserves its failure of isolation, irrespective of any guard/type changes there
- If `u` is absent, recognition-set invariance keeps it absent

Consequently the entire selected-anchor set is invariant. This proves more than preservation of the selected anchors alone. Guarded candidates may change at nonisolated recognized anchors, but these changes cannot activate them; isolated anchors have their full guard reads protected.

Recognized anchors with `T_u=id` are included: prospectivity is true, selection is harmless, and other selected writes cannot turn that identity choice into a different choice. The empty recognition family gives the identity without any exception.

### 2.4 Second application and mass

At every selected anchor, other selected writes miss its radius-`r` control word. On the second application it sees exactly its own local first image and applies the same everywhere-defined involution in reverse. The same disjoint blocks restore the original configuration.

For finite inputs, a nontrivial equal-weight replacement must have at least one original particle in its write block. Disjointness permits only finitely many such nontrivial changes; all-zero blocks are necessarily fixed. Thus finite support is preserved and the sum of ones is exactly conserved. Infinite inputs need no divergent-total-mass assertion.

### 2.5 Radius

For a fixed output coordinate, potentially writing anchors lie within distance `b`. Isolation at one such anchor reads radius `H+a`; local control and prospectivity read radius `q`. Since `H+a>=q`, the composite output radius is

`b+a+H = b+a+max(2(b+a),b+r)`.

All intervals are closed, and selection uses strict separation `>H`, so equality cases cannot produce a hidden one-site overlap. Translation covariance of recognition and the local involutions proves translation covariance of the resulting finite-radius CA.

**Conclusion:** the abstract lemma is sound exactly as stated, including malformed, dense, infinite, multiple-update, absent-anchor, rejected-anchor, and identity-update cases.

## 3. Same-anchor mutually unique transpositions

For each type `g`, the type-specific transposition `tau_(g,u)` exchanges its two distinct equal-weight endpoint words on its own `I_(B_g)(u)` and fixes every other local word and every outside coordinate. It is therefore an everywhere-defined involution.

With `C_u(x)` containing **all edge-template types** whose full guards hold, define a nontrivial `T_u` only when

`C_u(x)={g}=C_u(tau_(g,u)x)`.

If this condition holds and `y=tau_(g,u)x`, exactly the same `g` passes the same test at `y`, returning `x`. If it fails, `T_u x=x`, so reapplication fixes the same input. This exhausts cases. In particular it handles zero types, conflicting types, and a newly enabled different type at the hypothetical image. There is no irreversible priority choice.

Every queried guarded predicate reads at most `I_r(u)` and `B_g<=b<=r`. Testing a hypothetical local replacement requires only replacement bits already computed from that input word; unchanged bits remain available in the same word. The hypothetical test adds no radius.

The new recognition predicate takes the disjunction of unguarded geometric exactness tests, retaining each type's own radius `3B_g+1`; it has common upper bound `a=3b+1`. It is a predicate on integer anchors, not type-anchor pairs. Because every guarded candidate implies its corresponding raw predicate, a nonidentity `T_u` implies recognition.

A free pair's rewrite uses its own smaller write interval. It does **not** erase or impose zero on the rest of the common `I_b`. This distinction is explicitly present in the packet and agrees with the literal old source.

## 4. Literal template-family and anchor audit

### 4.1 Geometry valid for all signed admissible states

The frozen compiler gives

`S=2D+2`, `B2=D+1`, `L=3D+4`, `b=B3=L+D+1=4D+5`, `Z=10b+10+2J`.

Every admissible configuration has exactly three markers and one head pair. The head pair has one globally unique signed-mode gap in `1..D`. Head-to-marker gaps exceed `D`, and all marker separations are at least `Z`. This remains true across endpoint decrements because enabled updates require natural post-counters.

Every literal pair or triple endpoint contains exactly one close pair with gap at most `D`. Hence every raw match must use the actual head pair, and its gap identifies its unsigned mode, sign, and endpoint orientation. No background-marker pair can impersonate a head.

A triple's actual singleton is within `L+1` of the head anchor in every listed orientation, including reverse behind travel and the shifted endpoint. Since `Z>2(L+1)`, two different markers cannot support competing raw triple types. The weaker fact `2b<Z` alone would not establish cross-template uniqueness, but the proof includes the stronger distance argument. At a marker-anchored triple the other markers are farther than `3b+1`; at the reverse endpoint's old anchor they are at least `Z-1>3b+1`. Exactness therefore does not accidentally reject an intended triple.

### 4.2 Home endpoints, including missing and competing branches

A plus home gap appears only in a dispatch or zero-update direct forward endpoint, with head anchor `u+S` and singleton `u`. These force `u` to be the origin. A minus home gap appears only in commit or direct reverse endpoints, again forcing the origin.

There may be many raw types at that **same** origin. The new raw-anchor set nevertheless is either empty or the singleton origin. Distinct branch labels do not create separate recognized anchors.

At a plus home, disjoint source domains give at most one guarded type. At a minus home, disjoint **exact actual image domains** give at most one guarded type. The exact image predicate includes natural pre-counters; substituting the source guard here would be wrong. For zero-update direct edges the source and image guard coincide because counters do not change.

The counter-class read sites `u±(Z+k)`, `0<=k<=J`, lie outside every home/dispatch/commit rewrite. On an admissible such endpoint, they faithfully read the relevant old or post-counter class; all-zero reads give `>J`. Thus guards are unchanged under those particular paired rewrites. A home without an enabled incident edge has `T_u=id`, even if one or many unguarded geometric types recognize the origin.

### 4.3 Moving free, behind, and ahead templates

Fix moving direction `w`, departure marker `A`, arrival marker `C`, separation `N=w(C-A)>=Z`, and current head anchor parameter `t=w(x-A)`, where `S<=t<=N-S`.

The literal free forward endpoint is `{0,d+}` and reverse endpoint `{w,w+d-}`. Its invariant key is the predecessor head anchor: `x` for plus, `x-w` for minus. Its exactness radius is **L**, not the triple common radius.

Literal behind triples have forward distances `S..L` and reverse distances `S+1..L+1`. Literal ahead triples have forward distances `S+1..L` from the arrival marker and reverse distances `S..L-1`. Converting these to the common `t` coordinate gives the following disjoint exhaustive partitions:

| Sign | Kind | t interval | Raw anchor |
|---|---|---|---|
| plus | behind travel | S through L | A |
| plus | free travel | L+1 through N-L-1 | x |
| plus | ahead travel | N-L through N-S-1 | C |
| plus | forward interaction | N-S | interaction anchor |
| minus | reverse interaction | S | interaction anchor |
| minus | behind inverse | S+1 through L+1 | A |
| minus | free inverse | L+2 through N-L | x-w |
| minus | ahead inverse | N-L+1 through N-S | C |

The free inequalities follow directly from requiring both corridor markers to be more than `L` from the free key: `L<t<N-L` in plus, and `L<t-1<N-L` in minus. All finite ranges are nonoverlapping because `N>=Z>2L+2`.

The two sensitive equality boundaries check as follows:

1. Behind `L -> L+1` is a triple. The minus free predecessor key is still at distance `L` from the departure marker, so free inverse recognition fails
2. Ahead `L+1 -> L` is free. The minus free predecessor key remains distance `L+1` from the arrival marker; an ahead inverse triple would require current distance at most `L-1`, so cannot compete

At interaction walls, behind inverse travel begins at `S+1`, and forward ahead travel ends one step before arrival at `S`; no travel template duplicates the interaction. Directions `w=+1` and `w=-1` are handled by the same oriented-distance derivation, while the head pair is always anchored at its leftmost particle, exactly as in the source.

### 4.4 Dispatch, endpoint, commit, and direct interactions

The actual literal edge families and raw anchors are:

- Free O/I travel: predecessor head anchor on both signs
- Behind/ahead O/I travel: unchanged contacted marker on both signs
- Dispatch: plus home to outbound-minus at distance `S` from the origin; origin on both signs; source-domain guard
- Endpoint: outbound-plus arrival to inbound-minus departure; **old selected marker coordinate** on both signs; no contextual guard
- Commit: inbound-plus arrival at origin to minus home; origin on both signs; exact image guard
- Direct zero-update: plus home to minus home; origin on both signs; unchanged-counter guard

For the endpoint, the old marker is `m`, the new marker is `m'=m+v*Delta`, and the reverse word relative to `m` has singleton offset `v*Delta` and head anchor offset `v*Delta-v*S`. Thus both the current head and current singleton force

`u=m'-v*Delta=m`.

Using `m'` as the reverse anchor is incorrect; the packet explicitly avoids that mistake. The current actual marker is at distance `S` from the inbound head, whereas the invariant old key differs by at most one site. Other markers remain outside the old-key exactness window by `Z-1>3b+1`.

Branch-specific signed O/I gaps exclude every other branch's interaction. For the same branch and sign, the singleton offset forces the appropriate departure or arrival wall, where the travel partition has no competing move. The third marker is too distant to support an alternative interaction.

At reverse dispatch and forward commit the guard is true because admissible intermediate configurations are drawn **only** from enabled source-edge subdivisions, with retained old/post counters. Guard-invalid geometric packets are intentionally outside the admissible set. This restriction is needed and is retained in the new theorem.

### 4.5 Passing both uniqueness checks and the outer filter

At any moving admissible state there is exactly one raw type-anchor, and its intended paired endpoint has the same raw anchor. At a home there may be several raw types, but all have the same origin anchor; full guarded uniqueness follows from the source domain/image conditions. At both endpoints of each intended edge, the guarded set at that anchor is precisely the singleton containing that edge type.

Thus the local mutually unique `T_u` is the intended transposition. Its raw set is the same singleton on both endpoints, so its isolation and prospective tests pass. At missing edges `T_u` is identity. This proves agreement for **all** natural-counter homes, all strict enabled intermediates, both signs, all source branches, all counter values, and all translations, not just tested forward trajectories.

### 4.6 Unchanged phase family and inverse agreement

The retained phase block is Report26's parallel full-shift involution, not the earlier ordered product. Its literal phase families are free moving pairs, near-marker moving triples on both sides at distances `S..L`, and one home phase triple for each control. A moving pair is recognized when no marker lies within `L` of its unchanged head anchor; otherwise exactly one near-marker triple is recognized. A home has the unique origin phase triple. The sign changes, but anchor, unsigned mode, and relevant exactness case do not.

Report26's prospective-isolation proof applies to this family with radius `r_P=3b+1`, giving full-shift radius `12b+3`. On the admissible set it is the exact sign flip. Both new E* and retained P26 preserve the admissible graph. Therefore forward compositions agree there, and inverse compositions `E* P26` also agree there. This justifies exact clocks and reflections, not only reachability.

## 5. Radius and resource arithmetic

With `a=3b+1` and `r=Z+J=10b+10+3J`,

`(b+r)-2(b+a)=3b+8+3J >= 0`,

so `H=b+r=11b+10+3J`. Therefore

- Edge radius: `b+a+H=15b+11+3J`
- Retained phase radius: `12b+3`
- Total: `27b+14+3J=108D+149+3J`

Fresh numeric checks reproduce all examples:

| Example | D | J | New edge | Phase | Total new | Report26 |
|---|---:|---:|---:|---:|---:|---:|
| Two-control increment | 8 | 0 | 566 | 447 | 1,013 | 1,698 |
| Clean target | 18 | 1 | 1,169 | 927 | 2,096 | 3,507 |
| Inherited universal ledger | 509,508 | 0 | 30,570,566 | 24,456,447 | 55,027,013 | 91,711,698 |

For the last row, `2*122622+4*66066=509508`, `b=2038037`, `a=6114112`, `r=20380380`, and `H=22418417`. The reduction is `36,684,685`, approximately 40%. The unchanged total template count is `8pD+29p+m+a_source=269,291,358,255` for the inherited counts. None of these counts was generated by executing a source compiler.

The ledger's universal-source digest is `fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`. No original ZIP entry has that digest, and the source table is not bundled. Its historical construction and universality remain inherited assumptions. The symbolic radius is a sufficient upper bound, not the exact/minimum radius and not an evaluation-cost bound.

## 6. Malformed-input distinction, directly checked

For the ordered controls `(q,h)` and one true-guard right increment, the literal inert compiler assigns gaps `Hq+=1,Hq-=2,Hh+=3,Hh-=4,O+=5,O-=6,I+=7,I-=8`. It yields `D=8,b=37,L=28,Z=r=380`. `J=0` suffices because the exact increment image is right-counter positivity, represented by classes `0,>0`.

For `X={0,5,500,505}`, no triple template fits: each cluster has only two particles and intercluster distance at least 495 exceeds every triple diameter. The only raw/guarded edge occurrences are free O at anchors 0 and 500, with local word exchange `{0,5}<->{1,7}`.

Report26 excludes two keys within `2(b+r)=834`, so E26 fixes X. New E* uses `H=b+r=417`, so both raw anchors are isolated. Each hypothetical swap leaves those same two raw anchors, because the new O-minus pair's predecessor anchor remains unchanged; no cross-cluster match appears. Therefore E* produces `{1,7,501,507}`.

The unchanged phase block has exclusion `2(b+3b+1)=298`, below the separation 500. Both phase pairs pass prospective stability. Hence

- `F26(X)={0,6,500,506}`
- `F*(X)={1,6,501,506}`

This finite local-word argument independently confirms a genuine malformed-input inequality, without running a CA update implementation. X has four particles and is outside the five-particle admissible set.

## 7. Separate radius-two appendix

The independent companion audit in `../fresh-audit-radius2/` derives conservation from a de Bruijn graph coboundary and exhausts a mixed-orientation spanning-tree parameterization of all Boolean local rules satisfying that condition. Its derivation is not the appendix author's leading-zero implementation or its reversed verifier. Exact details, checker, hashes, and receipt are in that companion audit.

The fresh enumeration checks 32,768 assignments and obtains exactly 428 distinct conservative binary five-input tables. It verifies the certificate's 423 distinct nonprojection tables, their distinct input-word pairs, and every local one-step collision equality. The claimed collision lengths have counts 164 at length 4, 179 at length 5, and 80 at length 6. Exactly five tables remain, each directly verified as one of the coordinate projections.

A periodic collision yields distinct bi-infinite full-shift inputs with equal images, so it is a proof of noninjectivity, not a heuristic trajectory test. The graph derivation also bridges conservation on finite supports to the complete local constraint set. The classification is independent of the large-radius construction. It supports the stated radius-at-least-three corollary under the standard binary, translation-invariant, time-independent, symmetric-neighborhood, full-shift-reversible, ordinary-number-conserving model; it supplies no external novelty conclusion or sharper large-radius bound.

## 8. Transport limits and final disposition

The following conditions are essential and correctly preserved by the packet:

1. The source is deterministic and partial-injective on **all** natural-counter IDs, not merely a promised orbit; exact image guards and natural pre-counters are required
2. Only strict intermediate states from enabled source-edge subdivisions are admissible
3. Clean-target normalization requires a control-wide no-incoming initial control, and enlarged-source constants must be recomputed
4. Periodicity/return equivalence to designated halting additionally requires no nonfinal blocking on the claimed universal input family
5. Universal-source universality and the pinned ledger are inherited, not independently re-established here
6. The new full-shift rule differs on malformed inputs, so old arbitrary-malformed evaluator traces, Diophantine/arithmetic verifiers, ordered-factor certificates, and circuit-cost claims do not transfer automatically
7. Admissible semantic computation claims do transfer through the proved step-for-step and inverse agreement
8. Two mathematical involutions do not imply two inexpensive arithmetic factors or template-independent running time

No required mathematical correction was identified. This is a proof/static-certificate audit and an authentication of fixed evidence; it is not a machine-checked proof, implementation certification, new source universality proof, or priority/minimality survey.
