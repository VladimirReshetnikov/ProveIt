# Decoder and runtime reduction experiments

## Result and scope

These experiments did **not** produce a verified machine with fewer than 252
working states. They did produce a useful new 252-state runtime: successful
modus ponens places its consequent in the existing formula cache. The exact
old-label binary change is `(204,1): (1,R,113) -> (1,R,151)`. A separate
bootstrap audit found a physical register permutation under which this
runtime starts correctly on a blank tape. Its full 8,361 conditional affine
instruction cases pass here, without restricting register values by a source
phase invariant.

The high-level cache-interface argument and blank-tape certificate belong to
the accompanying theory and bootstrap artifacts. This directory supplies the
decoder mapping, independent conditional runtime checks, and bounded search
experiments. No new Lean or Coq theorem was checked in this directory. No
failure of these searches is a lower bound on all possible machines or
compilers.

All repository inputs were pinned to ProveIt commit
`43026ff42f0939f09b9e95495248cfadcad38e38`. The original program, public253
runtime, and permutation252 construction remain attributed to their original
authors, including Mira-Cult, Jeff, Wade, the mira-emmy work, and ProveIt.

## Exact positive artifact

`rotation-candidates/mp-cache-permuted252.tm` is the old-label table with the
cache continuation and the successful physical permutation. Its SHA-256 is
`9ba862d15e0f689525281e1c96083acf7f389157bd56d6a2676f223106dc07a9`.

Logical registers are ordered `(N,T,W,A,D,H,X,Y,L)`. Their physical indices are
`[4,5,0,8,6,2,1,7,3]`. The companion source file is
`rotation-candidates/mp-cache-permuted252.json`; it includes this permutation.
The maximum unfolded source-leaf depth is 34. There are 6,437 source leaves
and 8,361 guarded instruction cases.

The source edit replaces the entire successful-MP subtree at binary prefix
`111111` by the already-existing transfer loop `while D>0: D--; H++`.
In the original 219-node source this redirects node130's right edge from
node166 to node197. The loop uses the same binary entry151 already present in
the optimized runtime; the final incoming bit supplies its required context.
No state or transition row is added by this edit.

For successful MP, its comparison has already established `T=H=X=Y=0`.
Consequently this transfer changes the relevant registers to
`(T,W,D,H)=(0,S,0,b)`, where `b` is the proved consequent and `S` is the saved
stack. This is a deliberate change to the source interface, not equivalence
to the original program on every trace. The accompanying proof compiler must
load the cached result when needed. The exact source-interface proof is
provided in the theory agent's files.

The separate bootstrap certificate reports blank old state0 reaching
dispatcher96 after 707,393 steps at head -13 with gap40 and logical registers
`[6,0,0,0,2,0,0,0,0]`. Every spare register at this boundary is zero. This is a
safe source root, not the all-zero source root. The source phase experiments
below therefore use precisely this initial vector.

### Conditional runtime proof boundary

`mp-cache-permuted252-check.json` records all 8,361 strict affine cases with
zero failures. The executor is the unchanged attributed
`27-variant-experiments-machine_search-grammar_search-strict_affine.py`.
`check_rotation252.py` enumerates the modified decoder's cases and uses this
executor with 1,000 symbolic-rule fuel per case.

For each source instruction, the initial tape relation quantifies over every
free gap parameter `n>=0`, every nine-register file, and every valid finite
spare-register suffix. A decrement case assumes only the named register's
zero or positive guard. The proof retains the full explicit program-counter,
head, left delimiter, gap, and file-boundary frame. Halting cases require an
actual halt and do not require a final tape shape. Every accepted case has at
least one literal machine step.

The only opaque machine excursions are the four existing register-box
contracts: physical-register marking, increment, zero decrement, and positive
decrement. All 55 rows supporting those contracts remain unchanged. A positive
decrement appends a zero spare register; it does not erase or forget the
existing spare suffix. Passing the finite symbolic cases denotes unbounded
register values by these contracts and affine-run rules; it is not a finite
simulation of selected numerical inputs. The Python implementation of the
checker is not newly kernel-verified.

## Source-phase and vector-effect strengthening

`cache_phase_analysis.py` computes a finite inductive source-control invariant.
Each logical register has an abstract mask over the three classes
`{0}`, `{1}`, and `{2,3,...}`. Increment, positive decrement, and zero tests
overapproximate all natural values. The worklist closes the exact finite
source control-flow graph under those transfers. The final checker verifies
initial inclusion and closure of every permitted edge, which supports the
usual induction on execution length.

From the certified safe root, this reaches a fixed point after 35,206 worklist
pops. Exactly three of the 8,361 guard cases are excluded: case numbers8202,
8203, and8204. They are the impossible positive/body cases of one transfer
loop whose source path begins `11101001011000110`. The corresponding CD6 leaf
is `111010010110001100`. The stored invariant is
`mp-cache-safe-phase.json`. The original unmodified program's known six
exclusions are separately reproduced as a control check.

Two stronger register-box executors were then used for new searches:

* `phase_zero_fold252.py` permits a zero decrement of a register other than the
  named source guard when its value is independently zero in the phase
  invariant. Such an excursion has the identity effect on the entire file.
* `vector_effect_fold252.py` records every primary register as an exact
  constant or an initial physical-register variable plus an integer offset.
  It permits repeated marking and repeated register operations. A decrement
  is executed only when the refined phase/guard bounds prove zero or prove
  positivity. An unknown guard is rejected. The number of appended zero
  spare registers is tracked explicitly after every positive decrement.

For the vector checker, the initial spare suffix is an arbitrary finite list
`beta`; after `k` positive decrements it is exactly `beta ++ [0]*k`.
The default dispatcher relation compares the exact primary vector and the
entire explicit left/frame tape while allowing any valid finite spare suffix.
It therefore identifies two different appended counts only through an
explicit invariant relation, not by claiming the tapes are equal. An optional
`--exact-spares` mode also compares the appended counts. Only the default
relation was used for the recorded complete fold sweep. The construction
composes the four unchanged box contracts; its Python implementation is not
a kernel certificate.

The stronger vector sweep executed 12,124 candidate checks containing multiple
justified marking excursions. Most subsequently failed their complete frame
checks. One additionally accepted complete guard, case8360 for deletion151
redirected to144, performs two independently justified zero decrements. That
whole fold still fails other guards. These figures must not be reported as
12,124 newly verified full cases or as a 251-state machine.

## Complete and partial search results

All searches below are bounded diagnostics. A rejected candidate may have
exceeded fuel, used an unsupported symbolic operation, or failed the chosen
interface relation. Counts identify the particular search family, not a
universal impossibility theorem.

| Experiment | Candidates or proposals | Conditional checks | Result |
|---|---:|---:|---|
| Original closed rotations, randomized | 12,000 proposals | Graph cost only | Best252 |
| Original closed-rotation beam | 74,872 proposals; 54,527 distinct tables costed | Graph cost only | Best252; 480-second bound |
| Cache-MP closed-rotation beam | 72,482 proposals; 52,786 distinct tables costed | Graph cost only | Best252; 480-second bound |
| Cache-MP old physical map, uniform folds | 55,471 recipes | 127,562 | Complete; no survivor |
| Cache-MP safe physical map, uniform folds | 55,471 recipes | 127,000 | Complete; no survivor |
| Safe map, phase-known-zero oracle | 55,471 recipes | 126,976 | Complete; no survivor |
| Safe map, exact vectors and valid spare suffixes | 55,471 recipes | 126,976 | Complete; no survivor |
| Safe map, vector oracle, one-incoming-edge full actions | 132,048 recipes | 203,347 | Complete; no survivor |
| MP/DROP-exchanged runtime, uniform folds | 55,471 recipes | 127,059 | Complete; no survivor |
| Coordinated two-incoming-edge deletion of252 on old physical map | 1,008,016 full assignments planned | 89,225 | Partial; 424,182 assignments pruned, 583,834 remain |
| Return-counter-aware zero-run search | 24,000 proposals | Graph and code-shape cost only | No six-zero-run candidate |
| Hoisted equality-success gate, synthesis of lifted B2 action | 1,012 full actions | 1,012 | Every action rejected first B2 guard |

A uniform fold deletes one eligible working state and redirects all incoming
transitions to one other surviving working state while retaining their writes
and moves. There are 221 eligible deletions and 251 targets per deletion.
All 55 Box rows, their immediate targets, and dispatcher96 are protected.

The full-action degree-one sweep considers the 131 eligible states with one
incoming edge from another state. For each, the replacement incoming action
may write either bit, move left or right, and target any of the remaining251
working states or halt: `131 * 2 * 2 * 252 = 132048`. Every survivor would have
received all 8,358 phase-feasible guard cases. There were none.

The two beam searches each retained candidates with at most257 graph states,
bounded maximum zero run by7 and source depth by39, and stopped at their time
bound with substantial remaining frontiers. They are not exhaustive across
all coordinated decoder transformations.

The return-counter metric counts unfolded leaf paths containing seven or more
consecutive zero edges. The baseline has18 such paths and maximum run7.
Reducing the maximum to6 might permit a shorter return counter, but this
would itself require a complete changed-table proof. Across four search
weights the best observed count was10, at269 graph states; no candidate
actually attained maximum run6. The recorded metric is a search objective,
not a proved compiler formula guaranteeing a state reduction.

## Other semantic and compiler experiments

The alternative successful-MP continuation consisting of Dag198 followed by
Dag207 puts the consequent in both top and cache with clean scratch registers.
It compiles by adding a state255 with rows `(0,R,151)` and `(1,R,37)` and
redirecting old204/read1 to255. All 8,366 strict affine guards pass, but it has
253 working states. `mp-double253-check.json` records this positive runtime
check. No blank startup was certified for that table.

Sharing a clear-top-then-transfer continuation between MP and the AX gates
looked source-efficient but collided with a contextual selector optimization:
entry143 clears H when reached in one bit context and clears T in another.
The six failing cases of the proposed shared-gate tables are retained as
negative diagnostics. These tables must not be presented as verified
252-state alternatives.

A source specialization of NIP tests `H=1` directly, avoiding its general
comparison with an incremented scratch register. Directly reusing decoder
states46 and62 breaks their other runtime uses. A role-aware compilation
preserving observed non-decoder uses reaches254 graph states; it passes
8,351 of8,352 strict guards and fails the relocated B1 continuation. This is
also an unverified candidate, not a new machine result.

`opcode_permutation252.py` compiles all six placements of MP, DROP, and NIP
within their existing non-AX opcode positions. With ordinary cache-MP NIP,
all six tables pass all8,361 affine guards. Identity and MP/DROP exchange
cost252 graph states; the remaining four cost253. With the specialized NIP,
all six cost254 and each has one B1 failure. These twelve constructions use
one compiler heuristic per placement and do not prove optimality for those
source programs.

The valid MP/DROP exchange is saved as
`rotation-candidates/mp-drop-swap252.tm` (SHA-256
`3f20c2fb02e9642259f5c3b2dad930bb1d7d68fa2b50fcdfb956c6cfd8a3e504`).
Its source commands0 and1 are exchanged, so its proof compiler must recode
them. All55,471 eligible uniform folds were checked in43.1 seconds with no
survivor. A blank startup is not certified here. The role-aware compiler keeps
unchanged source subtrees and freezes rows observed in non-decoder roles;
this is a cost heuristic. Its outputs receive the independent complete
affine checks, which determine their runtime status.

## Reproduction

Use ordinary Python3 with assertions enabled. Do not use `python -O`.
All paths below are relative to this directory, whose input subdirectories
must be kept intact. No network access or proof-assistant installation is
required for these Python replays.

```sh
python -B check_rotation252.py rotation-candidates/mp-cache-permuted252.json --table rotation-candidates/mp-cache-permuted252.tm --output mp-cache-permuted252-check.json
python -B cache_phase_analysis.py --dag rotation-candidates/mp-cache-permuted252.json --initial-registers 6,0,0,0,2,0,0,0,0 --output mp-cache-safe-phase.json
python -B fold_changed252.py --name mp-cache-permuted252 --physical 4,5,0,8,6,2,1,7,3 --start 0
python -B phase_zero_fold252.py
python -B vector_effect_fold252.py
python -B vector_degree1_fullaction252.py
python -B opcode_permutation252.py
```

The timing-limited searches intentionally have variable stopping points
across machines; their recorded counts are the counts actually reached in
this run. Exact transition, source, driver, and result-file hashes are in
`ARTIFACT_HASHES.json`. The main report should distinguish the full verified
cache-MP runtime and its separate safe bootstrap from all graph-only or
failed tables in `rotation-candidates/`.
