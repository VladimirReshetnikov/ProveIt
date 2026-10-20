# Machine and encoding search: K219 to K218

This directory contains exploratory searches against the pinned K219 packet. **No 218-state machine has been established by this work.** Negative bounded searches are not lower bounds. The tested classes leave many possible encodings, global invariants, and changes to the computation uncovered.

## Baseline and conventions

The baseline is `K219_Construction_2026-10-20/machine/k219.native.tm`, SHA-256 `b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`, extracted from the incoming archive in ProveIt commit `26d5de6d21fa354d50e0b84fe851c289925b8d72`. It has 219 working states, start 0, dispatch 84, and halt 254. Its source has 206 DAG nodes and 4,744 primitive occurrences. The protected native engine and its decoder aliases are significant: identical source subtrees do not automatically imply interchangeable physical decoder states, because the helpers exploit bits preceding the leaf.

All code in this directory is exploratory. Existing portable proof infrastructure is imported from the pinned K219 and K221 packets. A successful finite search would need a new unbounded runtime certificate and the appropriate source proof before being claimed as a construction.

## Completed local deletion searches

`search_folds.py` computes an inductive finite-window overapproximation from the blank initial state. Unknown bits entering the window are chosen nondeterministically. The stored radius-5 and radius-7 invariants therefore include every corresponding window of every reachable baseline configuration; they can include unreachable windows.

For pairs sharing one transition after state identification, the other transition was enumerated over both writes, both directions, and all retained targets including halt. Radius 5 and radius 7 each tested 228,636 actions. Each required a positive new computation of at most 30 steps to match the exact old one-step endpoint. Neither found a survivor.

`search_diamonds.py` allowed positive common endpoints of up to 40 old and 40 new steps, at radius 5. It tested 228,636 actions, with no survivor.

`search_double.py` allowed both branches of an engine-involved merged state to change. Branches were synthesized separately, requiring reunion before reentering the merged state, so the unknown opposite branch was not used. The radius-5, 40-step search tested 8,533,992 row actions and found no complete fold.

`search_bypass.py` tested a different deletion class: remove a state and independently synthesize each of its incoming transitions, rather than requiring a common target for every incoming row. The old/new paths had to rejoin within 40 steps and a radius-7 window, before encountering another rewritten entry. It tested 194,472 actions and found no survivor.

These searches rule out only their stated bounded local certificates. They do not rule out a valid merge justified by a stronger invariant, a longer/global computation, or more than the permitted row changes.

## Finite primitive-interface screens

The C++ screens use a finite tape window, at most 30,000 steps per primitive case, an initial header at displacement 64, two spare counters of value 1, and baseline logical counters all zero except the tested positive decrement operand, which is 1. They screen every source leaf and both decrement guards: 6,167 baseline cases. The baseline first passes the entire suite. A candidate must reach a fully formed dispatch frame, not merely visit state 84; some primitives pass through intermediate redispatch states.

Two candidate classes were tested:

* Pair identification, independently selecting each resulting branch from one of the two original rows: 94,750 baseline candidates, no survivor.
* Pairs with one common branch after identification, enumerating the other branch over every retained state, both writes and directions: 227,592 baseline candidates, no survivor. This C++ class excludes the halt target, unlike the local Python searches.

The second class also found no survivor on the row-157 rewrite seed (226,720 candidates), exploratory row-160 seed (224,976), both rewrites (224,104), and the independently certified six-leaf NOP + K219 seed (229,336). The row-160 seed is only exploratory and is not asserted to satisfy an unbounded runtime theorem.

### Source-admitted backgrounds

`admissible_source.py` computes a forward product invariant with each register in a subset of `{0,1,2,>=3}`. Increment and decrement are abstracted soundly; the fixed point is separately checked for seed inclusion and edge closure. Starting from `[3,0,0,0,3,0,0,0,0]`, it admits 4,741 source occurrences and 6,162 guards. There are 1,421 decrements with both guards and two forced-zero decrements. The finite general-fold screen on minimum admitted backgrounds tested 227,592 candidates and found no survivor.

The two forced-zero sites are ordinal 4606 (`11101001011001100`, CD6) and ordinal 4718 (`111111000`, CD1). Their unreachable continuations are ordinals 4607, 4719, and 4720. These are invariants of the source computation, not claims that all other abstract combinations are concretely reachable.

`joint_source.cpp` then retains disjunctions of complete nine-register patterns in the same four-category domain. Its fixed point contains 41,439,908 `(site,pattern)` pairs. It produces the same reachable sites and guard classification, but tightens 4,737 marginal site facts. For example, register 0 at root is at least 3. One joint-pattern witness per admitted guard provides a stricter finite screen without inventing a combination of independently possible register values. The admitted joint-background fold search completed 227,592 candidates with no survivor; its receipt is recorded in `joint219_general.log`.

## Equality synthesis and physical compilation

The baseline packet has sixteen finite clean-equality hits. `eq_variants.py` and `compile_eq.py` inspect those sixteen and their register-5/register-6 reflections. Compiling the original hit reproduces the baseline table byte for byte. Only the original and one alternative have a 206-node whole-source DAG; the latter requires a right-child increment of register 6 for which no existing single-row leaf implementation survived the finite interface tests. Other compiled variants have 220–224 physical states. These are exploratory tables, not newly certified constructions.

An expanded grammar adds the existing clear-5 subtree and CB2, CB3, CC4 atoms, and forbids primitive CD5, CD6, CI5, CI6 as right children. Its semantic signatures use counters 0–6; goals are checked at 0–4. This is a bounded heuristic grammar, not an all-natural specification or complete enumeration by program size. In particular, the cost-7 run intentionally skips the intermediate cost-6 layer, so it excludes root splits using that layer.

The cost-6 run tested 24,273,655 combinations and found no goal. The cost-7 run tested 119,152,764 combinations and found twenty finite goals, stored in `left_hits.json`. Their whole-source DAGs have at least 208 nodes. They were also physically compiled with state 302 removed and the predecessor's ordinary return protocol restored. Invalid suffix-dependent aliases at 108 and 122 were cloned. Seven roots compiled under the finite leaf-interface test: the smallest has 221 states, the others 222. The remaining roots require unsupported CB2/CB3 returns or longer zero-run handling. Thus the physical compilation, not merely DAG count, rejected this attempt to save state 302.

## Weaker, semantically motivated endpoints

The exact baseline frame contract also fixes auxiliary tape details that do not affect the nine logical counters. The weak endpoint accepts any well-formed finite spare list with at least one spare, an arbitrary head translation and header gap of at least 64, and exact logical register values and PC. `weak_choice.cpp` applies this relaxation to pair row-choice candidates on five seeds. Its individual receipts and logs are in `weak_choice_results/`; the parent investigation runs the complementary one-common-row class.

`cfg_bisimulation.py` contracts source CB/CC identity edges and minimizes the remaining labeled control-flow graph. Pure identity cycles receive a divergence class. The baseline has 3,321 active actions and 3,317 bisimulation classes after 109 refinement rounds. The returned relation is checked against action labels and successor classes. `bisim_general.cpp` and `bisim_choice.cpp` permit a returned PC whose zero-extended decoded leaf lies in the same class as the expected successor. All remaining bits after that leaf must be zero until the header. These finite screens run on baseline, NOP, rho6 permutation, and NOP+rho6 seeds, with receipts in `bisim_results/`.

`cfg_liveness.py` recognizes finite transfer loops: a CD r positive branch followed only by increments of other registers and identity instructions before returning to the same CD r. Such a loop clears r and adds fixed multiples of its old value to the other counters. Backward liveness can therefore ignore the old r only when all incremented targets are dead. In this program 1,057 such loops are recognized; only 21 nonhalting sites lose one live register. To prevent a stuttering-divergence loophole, every primitive edge internal to a recognized loop must still preserve its controlling register exactly, with the positive CD performing the original decrement. Entry from outside may alter a dead value, but the subsequent clear loop retains its natural-number descent. The finite screens additionally compare all logical registers live at either returned continuation. These are discovery screens, not unbounded proof certificates.

## Completed weak-endpoint counts

Every entry below completed with zero surviving finite candidates. The admitted endpoint is a discovery specification; these counts are not unbounded proofs of impossibility.

| Seed | Auxiliary-only row choice | CFG-class row choice | CFG-class one arbitrary row |
|---|---:|---:|---:|
| Baseline K219 | 94,750 | 94,750 | 227,592 |
| Six-leaf NOP + K219 | 94,746 | 94,746 | 229,336 |
| Certified row-157 rewrite | 94,752 | — | — |
| Exploratory row-160 rewrite | 94,756 | — | — |
| Both row rewrites | 94,758 | — | — |
| rho6 reparameterization | — | 94,748 | 228,464 |
| NOP + rho6 | — | 94,744 | 230,208 |

The baseline CFG+liveness screen completed 94,750 row-choice and 227,592 one-arbitrary-row candidates, again without survivors. A separate single-entry deletion screen removes a state having exactly one external incoming row and synthesizes that row over every write, direction, and remaining target including halt. With the CFG+liveness+auxiliary endpoint it tested 98,112 candidates, with no survivor (`finite_bypass.log`).

## Physical register assignment

`compile_permutation.py` is an exploratory compiler that preserves prefix-sensitive decoder groups, clones a group if it conflicts with protected engine rows, and splits incompatible logical or suffix-dependent aliases. It synthesizes leaf actions against their actual source prefixes rather than selecting an action by register number alone. Its identity run reproduces the literal baseline SHA-256 and 219 states.

The 22 nonidentity seed-preserving transpositions are the swap of registers 0 and 4, plus all pairs among the seven initially zero registers. Every attempted transposition encountered a primitive context for which this compiler could not synthesize a single-row entry using the existing helper states. These are **compiler-class failures**, not impossibility results for register permutations. New helper states, different opcode layouts, or a rebuilt interpreter were not included.

`permutation_matrix.py` screens up to five distinct seven-bit suffix contexts per old register, new register, and increment/decrement opcode. Every nonidentity reassignment fails at least one sampled fixed-helper context, leaving only the identity matrix. This necessary-condition screen has the same restricted scope. The recorded compilation and matrix summaries are included; partially built tables are not constructions.

## Constant-operand halt specialization and a rejected 219-state table

A fresh source invariant shows that the unique external entry to the halt test has register 6 equal to 0 just before CI6. Consequently the external entry to its equality macro has register 6 exactly 1. Internal revisits of the equality loop may instead have register 6 equal to 0, so treating every visit to its first leaf as an external entry would be unsound. The compact independent zero/positive verification is included in the sibling audit directory.

Write `D=CD5`, `Z=(D,CC1)`, `H=CH`, and let `E` be the existing clean equality macro. Two equivalent source transformations follow:

* `S=((D,((D,CB1),H)),Z)` halts exactly when register 5 is 1; on all other inputs it clears register 5 and returns normally. Removing the preceding CI6 leaves register 6 at 0. The whole source has 208 DAG nodes and 4,738 leaf occurrences.
* With register 6 initially 0, `(D,(E,H))` has the same behavior and reuses the existing equality subtree. Replacing `(CI6,((E,H),tail))` by `((D,(E,H)),tail)` keeps the whole source at 206 DAG nodes and 4,744 leaves.

A naive physical compilation of the second source still had 219 states and passed decoder-prefix binding, but it is **invalid**. It changed protected row 38/0 from `0 R 13` to `0 R 303`. The independent CI5 primitive at source PC `111010010010011110`, outside the replaced region, uses row 38/0 as an arithmetic helper. From an all-zero logical frame, the old primitive returns the correct result after 660 TM steps; the changed table returns an incorrect frame after 640. In particular, unchanged logical source subtrees and a successful decoder binding do not suffice to protect arithmetic aliases.

The protected helper path includes `47/0 -> 63 -> 123 -> 39 -> 11/0 -> 26/1 -> 38/0 -> 13`. Cloning only state 38 and redirecting 26/1 does not solve the issue because 26/1 is also protected. Exhaustive finite synthesis of the one row 38/0 in the raw 219-state table found no repair among 880 actions: both writes, both directions, and all 219 working targets plus halt. The best action passed only 98 of 6,168 finite source-interface cases. This failed table is not included among the candidate machines.

One can retain CI6 and then explicitly clear register 6 before the six-leaf test, or clear it only on failure. These forms preserve the problematic original instruction but introduce source nodes; no beneficial physical compilation has been established. The constant-operand lemma remains useful independently of this unsuccessful encoding.

## Potential dedicated-comparator route

Removing the source equality macro makes native decoder states 77, 87, 88, and 301 unnecessary; removing the specialized right-child decrement protocol can also remove 302. A direct equality primitive would therefore need at most four additional states to improve 219 to 218, subject to actual decoder reuse and engine restoration.

Registers 5 and 6 are physically adjacent. Alternating deletion from the right edge of one unary block and the left edge of the other can be driven by four short scan/check states. The unresolved costs are detecting equality versus either exhaustion, clearing the unequal remainder, and repacking the enlarged zero gap into the interpreter's canonical single-zero separators. A comparator that leaves arbitrary internal gaps is incompatible with the current register representation.

State 103 is also used arithmetically through transition 119/1. Its incoming local invariant forces it to scan 1 on that nondecoder use. Consequently removing its equality-decoder role frees **row 103/0**, not row 103/1. This is a potentially useful half-state resource for a future specialized comparator.

## Reproduction and scope

The packaged `replay.py` has a quick mode for source closure, abstract invariants, CFG/liveness construction, and byte-exact identity compilation. Optional modes rerun the expensive local, finite, equality, and permutation searches. Python needs only the standard library; C++ programs require a C++17 compiler. The executable search sources and the small baseline inputs are included. Large generated window invariants, the 41-million-pattern joint state set, and compiled binaries are regenerated rather than shipped.

Recorded receipts are distinguished from fresh output under `output/`. The package manifest records every included file hash. Empty hit files mean no finite survivor within that particular search, not a verified impossibility theorem. The separate main packet replay checks the two independently validated 219-state variants; this research directory does not establish a new <=218-state construction.
