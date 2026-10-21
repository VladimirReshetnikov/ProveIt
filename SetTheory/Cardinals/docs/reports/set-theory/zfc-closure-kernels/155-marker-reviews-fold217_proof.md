# Independent proof review: the 400-to-69 state fold

## Result and exact inputs

The literal 217-state machine is halting-equivalent, on every binary initial tape from state 0 and every integer head position, to the submitted prefold 218-state machine. This is an ordinary mathematical theorem about the two exact tables. It does not by itself verify the prefold source reallocation or the inherited consistency calibration.

- Prefold native table SHA-256: `34617022def75d88a4f357589d7a48f468d17b58c910947ed0738aa3c6a5760a`.
- Final native table SHA-256: `c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099`.
- Both start in native state 0. Native halt label 254 has no outgoing rows.
- The old table has 218 working states and 436 rows. The new table has 217 working states and 434 rows.

The final table deletes state 400, redirects its incoming target to 69, and replaces `69/0` by `0 L 188`. Every other row is exactly the old row with target 400 renamed to 69. In particular, the helper rows 188, 92 and 90 are unchanged between these two inputs. Their earlier reallocation belongs to the separate source/runtime proof.

## The inductive entry fact

In the old table, the complete incoming-edge census is:

| Destination | All incoming rows |
| --- | --- |
| 69 | `53/1 = 1 R 69` |
| 400 | `224/0 = 0 R 400` |

Neither state is the initial state. Consequently, at every old computation step that starts in state 69, the cell immediately left of the head contains 1. At every old step that starts in state 400, that cell contains 0. The assertion follows directly from the preceding transition: it moves right and writes the stated bit into precisely that cell. It is valid independently of the rest of the tape, all register values, source addresses, or the duration of the computation.

Equivalently, the configuration predicate

- state 69 implies left neighbor 1;
- state 400 implies left neighbor 0;
- every other state has no additional condition

holds initially and is preserved by every old transition.

## The four local diagrams

Let the old head position be h, its scanned bit be b, and the forced left neighbor be m. Represent either old state by new state 69, with identical head and complete tape.

The old rows are

| Old state | Read 0 | Read 1 |
| --- | --- | --- |
| 69 | `0 R 105` | `1 R 31` |
| 400 | `0 R 104` | `1 R 31` |

If b=1, the new table has the same `1 R 31` transition. Thus both old roles are simulated in one step, without changing any bit.

If b=0, the new machine uses `69/0 = 0 L 188`. It moves to h-1 and reads the predecessor marker. Its next two transitions are:

| Forced marker | Second transition | Third transition | Endpoint |
| --- | --- | --- | --- |
| m=0, old role 400 | `188/0 = 0 R 92` | `92/0 = 0 R 104` | state 104, head h+1 |
| m=1, old role 69 | `188/1 = 1 R 90` | `90/0 = 0 R 105` | state 105, head h+1 |

Every transition preserves the bit it reads. Only cells h-1 and h are read before the endpoint; neither changes. No outside cell is visited, and no intermediate state is halting. The endpoint is therefore identical, in state, head and entire tape, to the corresponding old one-step endpoint.

The proof covers all four combinations of old role and scanned bit. No finite-register approximation or blank-start sample is used.

## Whole-run equivalence

Define the state map phi by phi(400)=69 and phi(q)=q for every other working or halting label. At an old configuration satisfying the entry fact, represent it by the new configuration with state phi(q), the same head and the same complete tape.

Every old transition outside the two folded states has an identical mapped one-step transition. The four diagrams above handle the two folded states, using either one or three positive new steps. The endpoint again represents the old successor and satisfies the old invariant. Induction on the old run length constructs matching new prefixes. There are no interior halts.

If an old run halts, the constructed finite new run halts. If the old run is infinite, the matching positive blocks construct an infinite new run. Determinism rules out a separate earlier new halt. Hence the two machines halt under exactly the same initial tapes and head positions from state 0.

More precisely, after n old transitions, the corresponding new prefix has length n+2c_n, where c_n counts old read-zero transitions in states 69 or 400 among those n transitions. Its length lies between n and 3n. This explicit positive bound also excludes hidden infinite stuttering.

This elementary finite-state argument and its induction can be formalized in ZFC. No new proof-assistant theorem was compiled in this review.

## Independent executable checks

`check_fold217_four_cases.py` is independently written and imports neither the construction script nor its source/compiler/runtime helpers. It parses and pins both tables, verifies the exact incoming census, checks all 432 ordinary mapped rows, and checks the four two-cell diagrams. Each diagram aborts if it would read outside its two specified cells. Its result is `INDEPENDENT_LITERAL_FOUR_CASE_FOLD_PASS`. A corrupted initial halting transition is rejected.

A second, preexisting independently authored checker, `check_joint_fold.py`, was run on these same literal inputs at radius 1 and fuel 7. It freshly computed and checked an inductive all-initial-tape window domain:

- 1,104 invariant contexts in total;
- 4 nontrivial contexts;
- 1,100 diagrams with old/new durations 1/1;
- 4 diagrams with old/new durations 1/3;
- maximum old/new block lengths 1 and 3;
- corrupted-initial-halt negative control rejected.

Its result is `INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS`, preserved in `fold217_independent_window.json`. The two code paths are corroborating executable mathematical checks, not a proof-assistant kernel certificate.

## Review conclusion

No issue was found in the relative all-tape fold. In particular, the helper has no additional mutation at this stage, and predecessor markers hold for every old run independently of the source interpreter. The remaining whole-construction obligations are the exact source reassociation, complete primitive runtime, complete blank initialization, and consistency calibration of the dominated-rho8 source. These are separate from this proved fold and must be reported with their own evidence.
