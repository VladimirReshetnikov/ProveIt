Source-side research for a machine below 208 states (2026-10-29).
No accepted smaller machine was found in this research branch.

1. Repaired source reassociation attempt, REJECTED.
   build207.py uses the owned source-tree library. It rotates source nodes
   155/85 and 52/154, merges the newly identical states154 into85, and
   redirects118/read0 to186. The source has unchanged ordered primitives,
   startup address and maximum zero run6. candidate207.native.tm and
   candidate207.sites.json are expressly rejected exploratory artifacts.
   Full symbolic verification fails at the CD5 contract, and the independent
   audit supplies a concrete canonical-frame counterexample in ../audit/.
   The repair correctly follows lookahead00 but misroutes lookahead01.
   It is not a counterexample about eventual blank halting.
   repair_targets.py and repair_action.py found no exact replacement under
   their stated partial-tape and100-step bounds; this is not an impossibility
   theorem. A partial tape rejects unknown reads, so longer scans are excluded.

2. Broader source reassociation search.
   general_rotations.py permits a rotation when complete resolved source CFG
   is unchanged, even if the previous all-three-factors-closed sufficient
   condition fails. Of70 initial structurally admissible rotations,57 preserve
   CFG, compared with50 satisfying the closed-factor criterion. Seven newly
   allowed rotations are (84,189,0),(84,78,1),(189,145,0),(134,225,1),
   (225,210,1),(210,18,0),(38,53,1). Only the last two preserve the exact
   startup source address in this initial layout. search_open.py seeds these
   two then performs protected closed rotations, allowing temporary zero-run7
   but requiring a final zero-run<=6 and five contextual folds from212states.
   It performed6,640 random-walk iterations in302.38seconds, finding no
   candidate. Iterations are not distinct layouts or exhaustive coverage.
   Hidden runtime helper states155 and151 remain protected.

3. Other measured ideas, not machine constructions.
   equal_sequences.py finds no distinct closed source nodes with identical
   flattened primitive sequence in this baseline.
   operand_aliases.py finds only12 equivalent opcode/argument choices at
   ordinal3873, all root-overflow variants; no state saving established.
   increment_commute.py finds no distinct all-increment source nodes with
   the same multiset of registers.
   measure_adjoin.py expands the separate theory worker's proposed filtered
   adjunction postfix using the known closed K215 macros. It obtains723
   emitter primitives,3877 total primitives, but207 distinct source DAG nodes,
   compared with197 in the current program. This is not a207-state machine.
   The source-only metric does not establish its theory/calculus calibration,
   blank startup, literal runtime implementation, or any state reduction.
   adjoin_source.json is therefore only an exploratory source expression.

All code in this directory was newly authored or uses explicitly identified
previously owned source utilities. Supplied proposal scripts were read only.

4. Complete-DAG adjacent-increment search.
   increment_full.py examines all197source-DAGnodes (the physical pure-R
   traversal in increment_commute.py only reaches176labels). It finds214
   adjacent increments of distinct registers for which the second increment
   has no external predecessor in the complete resolved CFG. They collapse
   to3shared structural rewrite patterns. search_commute.py exhausts all8
   choices of applying each pattern globally. DAGcounts are197 once,
   198 three times, and199 four times. No smaller source results.
   This does not exhaust arbitrary subsets of214occurrences or combinations
   with other transformations. Pairwise correctness follows from addition
   commutativity and absence of control entries into the second instruction;
   the actual initial source ordinal136 is not such an interior entry.

5. Filtered-adjunction literal-label sensitivity.
   measure_constants.py measures fixed adjoined-variable labels2through16,
   using PUSH1 followed by balanced (k-1)-increment trees. The27-token word
   and interval DP are held fixed. DAGcounts are207,207,208,207,209,209,209,
   208,210,210,211,210,211,210,211, respectively; source occurrencecounts
   range3874through3888. These are syntactic cost measurements only. The
   labels were not all proved semantically safe for their small-code aliases.
   The interval DP objective is not claimed to be a global minimum over all
   source expressions. No candidate table or kernel certificate is produced.

6. Unchanged-theory quantifier factoring.
   measure_factored.py compares the original negated-cover expression with
   the classically equivalent expression factoring its two universal clauses
   under one quantifier, in both conjunct orders. Using the same retained
   closed-macro compiler and interval DP, the original yields28tokens,
   737emitter primitives,3891total primitives,204DAGnodes (matchingU222).
   Factored lower-first yields28tokens,782emitter primitives,3936total,
   205DAGnodes; upper-first yields206DAGnodes. This is a controlled comparison
   within this compiler, not a lower bound or a direct comparison of fully
   optimized native machines. Current197DAG source uses additional later
   optimizations. No improvement was found in the measured factoring family.
