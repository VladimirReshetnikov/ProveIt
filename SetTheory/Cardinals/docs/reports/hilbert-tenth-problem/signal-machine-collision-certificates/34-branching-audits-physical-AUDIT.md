# Independent audit of the frozen five signal branching construction

## Verdict

**Accepted within the stated scope. No mathematical defect was found in the frozen core.** The proof supplies a physical, nondestructive two-chamber test and a uniform simulation of each fixed finite deterministic two-counter program. The section, marker labels, scale and five live occurrences are restored as claimed. The 19-speed and 32-event upper bounds, the strict instruction-time bounds, and the designated-section halting semantics are supported.

This is an independent mathematical and exact static audit, not a proof-assistant formalization, physical simulation, novelty certification or exhaustive search. The separate arithmetic certificate under development is outside this audit. The retained predecessor is not being re-certified in its entirety: only its translation primitive is used here, and that primitive is re-proved in the frozen core and independently checked below.

## Source binding and execution boundary

Audit date: 4 October 2026, UTC.

Frozen packet: `five-signal-branching64-20261004`.

- `PROOF.md` SHA-256: `85f5de45c0a30f8bdf45b82a613ef9e5a8c766b5d8215d17a3ebbbd0f60b370f`
- `MANIFEST.json` SHA-256: `e5d9f9a399ab9515a13b66ea4160b063a585c801002105b62f4528da516c1589`

All six content files were read as inert data. Every manifest entry matches its content. The independent checker also pins the manifest itself, so its source claim cannot silently follow a changed manifest. No author scientific code, upstream code, physical simulator, stored execution, counter program or Lean process was executed. The author's `static_algebra.py` was inspected, but neither imported nor run. Its recorded evidence was read without treating the claimed pass as independent proof.

The new `audit_static.py` was inspected before execution. It uses Python's standard library and rational arithmetic, with no external package, shell subprocess, dynamic evaluation, event search or next-collision engine. It verifies manually transcribed equations, local rule incidence and finite rule-table syntax. Its output is `audit-results.json`. The frozen content files were opened with `O_NOATIME`; their modes, sizes, access times, modification times, change times and hashes were checked unchanged. No original was rewritten or chmodded. This is a content-file preservation claim; no unrecorded pre-audit directory access time is asserted.

The successful final run reports **4,424 checks**, **56 primitive local rules**, and a **118-rule, 142-label static example** containing both increments, both conditional instructions, looping control flow and halt. The example table was assembled and checked, never executed. These finite syntax checks supplement the arbitrary-program namespace proof; one example is not itself proof of the universal quantifier over programs.

## 1 Forward branch geometry and exact chambers

Source: `PROOF.md` sections 2 and 3, lines 33–161.

Starting from the outgoing section, the first three contacts occur at `(time, position)` equal to `(x,x)`, `(5x/3,0)` and `(19x/9,4x/9)`. The target positions at the middle and last contacts are respectively `2x/3` and `4x/9`. The messenger then travels at `-1/4`, the target at `2`.

The messenger's next anchor time is `B=35x/9`; the fast target is then at `4x`. Its potential spectator contact occurs at `A=17x/9+y/2`. Hence `A-B=(y-4x)/2`. Both selected words require `y>4x`, and this condition makes the anchor bounce the next relevant event. The outgoing speed-4 messenger would catch a still-fast target at time `53x/9`, position `8x`. The difference between that catch time and `A` is `(8x-y)/2`.

Therefore the strict alternatives are exactly:

- Z: `x>0`, `y-4x>0`, `8x-y>0`, `D-y>0`
- N: `x>0`, `y-8x>0`, `D-y>0`

The N inequalities imply `y>4x`. At `y=4x` the anchor contact and target/spectator contact tie at distinct places; at `y=8x` the speed-4 messenger, target and spectator meet together. Neither equality belongs to the selected interface. The lower chamber `x<y<4x` is not falsely included or needed.

For Z, direct line equations give target restoration at

`F=(10y-8x)/9`, time `11x/3+5y/18`,

followed by anchor return at `25(2x+y)/18`. The seven positive flight durations are

`x, 2x/3, 4x/9, 16x/9, (y-4x)/2, 2(8x-y)/9, F`.

For N, restoration is at position `8x`, time `53x/9`; anchor return is at `125x/9`. Its last two flight durations are `2x, 8x`, after the common first four. Thus the six- and seven-event tables are internally correct.

For sufficiency, every event endpoint has exactly the declared binary contact. All other strand separations are strict. In Z coordinates `a=y-4x`, `b=8x-y`, `c=D-y`, the inverse parameterization is `x=(a+b)/4`, `y=2a+b`, `D=2a+b+c`. In N coordinates it is `x=a`, `y=8a+b`, `D=8a+b+c`. The independent checker verifies the strict sign of every nonzero endpoint difference, not merely the adjacent pairs, in these positive cones. It checks the five velocity identities on each flight and fixed pair ordering through the open flight. Affineness then excludes every unlisted meeting, including simultaneous remote contacts.

For necessity, the two prospective comparisons are made only after the preceding valid prefix. This avoids continuing an invalid prospective trajectory through an earlier contact. The resulting chambers are exact for the selected complete words.

## 2 Physical reversal and full restoration

Source: section 4, lines 162–213.

The final forward `C_c/L` collision is a real interface: incoming messenger speed `-1`, outgoing reverse-entry speed `+1`. It occurs once. There is no extra zero-time phase-switch collision and no reversal of that same anchor collision at elapsed time zero.

After this interface the next reverse contact is the preceding non-anchor forward contact. The reverse messenger and moving-target labels have negated forward speeds. The Z-only target/spectator reverse event changes the target label locally and leaves the remote messenger unchanged. The two sets of reverse labels remain branch tagged through the common reverse geometry. The final reverse contact is a new physical anchor collision with incoming speed `-1` and outgoing speed `+1` carrying the selected control label.

If the forward event times are `t_0=0<...<t_m=T`, reverse events have elapsed times `T-t_(m-1),...,T-t_1,T`. These are event times relative to reverse entry, not the consecutive flight lengths. The consecutive lengths are the original positive flight lengths in reverse order. The manuscript's phrase “occur after durations” is consistent with this elapsed-time reading; no mathematical correction is required.

The checker verifies all inverse velocity equations, every pair separation and every local rule against the independently transcribed label columns. Uninvolved labels must agree across each event, which directly checks the absence of remote phase changes. It confirms literal restoration of `L,X,Y,R`, their positions and stationary speeds, with the messenger at L outgoing right. Only the branch-control messenger label differs.

The changing maps are invertible: `x -> (10y-8x)/9` has inverse `x -> (10y-9x)/8`, and `x -> 8x` has inverse `x -> x/8`. Their determinants are `-8/9` and `8`; the doubled test has identity positional map. The total counts are 14 and 12, and total times are `25(2x+y)/9` and `250x/9`.

This is a branch-tagged inverse gadget. No global reversibility is inferred for the identity-completed finite rule table.

## 3 Uniform encoded coverage

Source: section 5, lines 214–249.

Let `u=2^-a` and `v=2^-b`. Both are in `(0,1]`, and the prescribed encoding gives

`x/D=1/20+u/10`, `y/D=19/20-v/10`.

Thus `x/D` lies in `(1/20,3/20]` and `y/D` in `[17/20,19/20)`, preserving the same strict marker order for all counter values. This is a single encoding and fixed rule table, not a collection of local constructions indexed by the input counters.

For `a=0`, `x/D=3/20`; consequently `(y-4x)/D >= 1/4` and `(8x-y)/D > 1/4`. Every zero input is in Z. For `a>=1`, `x/D<=1/10`, giving `(y-8x)/D>=1/20`; every positive input is in N. The scale and endpoint gaps are also bounded away from zero. The intermediate Z target gap satisfies `(y-F)/D>1/36`; the N gap is at least `1/20`.

Reflection uses target distance `D-y` and spectator distance `D-x`, which obey the same bands with the counters interchanged. The reflection is an involution, negates physical velocities, preserves all event-time differences and contacts, and swaps marker roles. Explicit transfers cross both interior markers and bounce at the far anchor: three events and exactly D time each. They preserve the stationary marker labels.

The checker uses closed rational rectangles, including the unattained limit endpoints, to establish the strict inequalities. Since all relevant expressions are affine, vertex bounds are complete interval certificates, not numerical sampling over a few counters.

## 4 Direct increments and decrements

Source: section 6, lines 250–326.

For scaling, `h=(k-1)/(k+1)` satisfies `-1<h<1` for every `k>0`. The four-event table obeys `t+h(t+kt)=kt`. The target moves monotonically between t and kt; if both lie strictly between the anchor and spectator, all flights and separations are valid. Conversely a failed endpoint guard obstructs that selected word no later than its attempted restoration.

For translation, `e<1` gives `h=e/(2-e)` in `(-1,1)`. Put `u=t/(1-e)` and `t'=t+eD`. The first four-event scale reaches u. The next six contacts occur at messenger positions `u,s,D,s,t',0`. Its restoration equation is `u+h(2D-t'-u)=t'`. The identities `u-t=et/(1-e)` and `t'-u=e(D-t')/(1-e)` show that u lies between t and t'. Thus valid initial and final endpoint guards also protect the hidden scale endpoint. The target stays below s and never participates in an unlisted spectator contact. All intended messenger spectator crossings are accounted for.

The two updates are literal affine operations:

- Increment: `t -> t/2 -> t/2+D/40`
- Positive decrement: `t -> 2t -> 2t-D/20`

Substitution of `t=D/20+(D/10)2^-n` gives the next encoded distance for `n+1` or `n-1` exactly. The latter is used only when `n>=1`, after the positive branch. No zero-decrement behavior is assumed.

All intermediate and final target endpoints lie inside the spectator band uniformly. The checker independently expands all four scale rows and all ten translation rows, including target positions at outward and inward spectator crossings. It checks their local rules, unchanged remote labels, all strand separations, exact update identities and duration coefficients.

Each update has 14 events. The moving speeds needed in distance coordinates are `-1/3,1/3,1/79,-1/41`. Durations are `2D+(196/39)t` and `2D+(290/21)t`. On their respective admitted bands they lie strictly between `2D` and `4D`.

## 5 Finite control and resource bounds

Source: section 7, lines 327–355.

For any fixed finite program, each block has finitely many rules. Assigning distinct temporary messenger and moving-marker labels per instruction and branch separates every context-dependent input rule. Stationary labels can be shared because a context-sensitive rule always includes an instruction-specific moving label. Marker-only events also use fresh temporary moving-marker labels, so their input keys do not clash across instructions.

At an interface, only the outgoing label of an existing terminal anchor collision is identified with the next block's entry phase. The speed is the required `+1` at L, or `-1` at R in a reflected block. Distinct branches may emit the same next instruction label without violating forward determinism. Labels can be reused on later iterations because they are finite control types, not added live occurrences. Consequently one finite table works for every initial counter pair and every subsequent instruction of that fixed program.

Identity completion on the remaining distinct-speed input sets is finite and number preserving. It cannot introduce an extra event into a certified encoded execution: the geometry already excludes the extra contacts. It need not make the rule map injective.

Counts obtained from the independently checked blocks are:

| Instruction path | Events |
|---|---:|
| Increment A | 14 |
| Increment B | 20 |
| Conditional A, zero | 14 |
| Conditional A, positive decrement | 26 |
| Conditional B, zero | 20 |
| Conditional B, positive decrement | 32 |

The speed union is exactly a convenient 19-element upper bound: zero and both signs of `1,1/3,1/79,1/41,3/2,1/4,4,1/2,2`. All audited labels lie in it. Additional phase copies increase the alphabet, not the speed count or the five live occurrences.

The static example table in the JSON exercises left and right updates, both branch exits, self-looping control and halt. Its syntax check is extra corroboration. The disjoint-namespace argument above establishes the general construction and shows why no input-specific recompilation is needed.

## 6 Time and halting semantics

Source: section 8, lines 356–365.

An A test lies in `(D,4D)` and each update in `(2D,4D)`. Each transfer costs D. Combining the listed paths proves the claimed strict `D<T<10D` bound. The largest structural combination is the B-positive path: two transfers, one positive test and one decrement. The upper bound is deliberately loose.

D remains fixed and positive. After n completed nonhalting instructions, elapsed time exceeds nD. Each individual instruction contains finitely many events with positive separations. Together these facts exclude finite-time collision accumulation, including an alleged accumulation hidden in a single instruction. They do not require a uniform positive lower bound for every individual inter-event interval.

Halting means reaching the full outgoing section with `Q_H`. This does not mean all five signals become stationary. The optional finite-collision implementation keeps `Q_H` at speed `+1`, crosses X, Y and R by identity rules, then has no further contacts. These are exactly three additional events and no population change. A spatially confined bounce convention would have different collision-halting semantics, as the source explicitly acknowledges. Before halt, the verified tables and their reflections keep all positions in `[0,D]`.

## 7 Literature and scope of the result

The primary sources were checked directly on 4 October 2026.

1. Durand-Lose's MCU 2004/LNCS 3354 (2005) manuscript, section 3, PDF pages 6–8, explicitly uses two stationary scale signals, one signal for each counter and one instruction signal; the preceding section specializes to equal-cardinality rules. Its encoding is `alpha*2^-a`, `beta*2^-b` with `1<alpha<beta<2`. Counter order can change, and zero values lie beyond the unit-scale marker. These passages support the five-live-signal antecedent. The present core therefore cannot establish first five-signal universality. Its stated distinction, a fixed ordered section with explicit nondestructive branching and uniform guards, is appropriately narrower. [Primary manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2004_MCU.pdf)

2. Durand-Lose's CiE 2006 manuscript, section 2.2, PDF page 5, describes negated signal speeds and reversed collision rules for time reversal. It also distinguishes global reversibility. The packet correctly uses this established principle and separately handles its physical section interfaces. [Primary manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf)

3. Becker et al., section 2, Definition 1, PDF page 4, defines a finite meta-signal set, fixed speeds and deterministic distinct-speed collision inputs and outputs. The five count here is live signal occurrences, not alphabet size. [Primary manuscript](https://arxiv.org/pdf/1804.09018)

4. Dudenhefner, FSCD 2022, Definition 2 and Theorem 6, provides an undecidable two-counter instruction model with increments and successful conditional decrements, and warns that exact instruction semantics matter. The packet's instruction set directly includes that model by choosing the zero destination as fall-through. The core compiler needs no stronger claim about a particular optimized universal program. [Primary paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol228-fscd2022/LIPIcs.FSCD.2022.16/LIPIcs.FSCD.2022.16.pdf)

No novelty, minimum-population, noise-robustness, finite-precision implementation, globally reversible computation, optimized speed/event count, or new fixed-arity Diophantine-halting result is established by this audit. Choosing a separately justified fixed universal counter program yields the stated fixed-table corollary; no such universal program is constructed or optimized here.

## 8 Audit limits and disposition

No blocking or material nonblocking mathematical defect was found. The complete geometry and compilation argument are accepted for the explicitly stated encoded runs and selected chambers. Outside those chambers, or outside the discrete encoding, the theorem makes no simulation claim.

The checker is supporting evidence. It is not a parser that extracts and formally proves the Markdown theorem; its manually transcribed equations and rule templates were compared with the pinned proof. Its full finite static certificate does not execute an infinite computation. The all-counter and all-program conclusions rest on the displayed algebra, uniform guard argument and finite-control induction.

The source says an independent audit was pending when frozen. That is an accurate historical freeze status; no original should be modified merely to replace it. This separate dossier records the completed audit of exactly those frozen bytes.
