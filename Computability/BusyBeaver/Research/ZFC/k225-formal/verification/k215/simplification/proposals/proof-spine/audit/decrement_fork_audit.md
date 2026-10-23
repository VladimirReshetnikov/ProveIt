# Independent audit: share the decrement prefix, then fork

Revision: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6` of VladimirReshetnikov/ProveIt.

## Verdict

The factoring is mathematically sound when expressed as composition of the existing executor soundness theorem. A separately written, fail-closed finite replay reproduces all reported symbolic-call totals. It binds all 4,751 source leaves, including all 1,425 decrement sites and both 2,850 decrement outcomes, to the pinned source and machine rather than accepting the supplied site list alone.

This is a mathematical/source audit and finite replay, not Lean or Rocq compilation, kernel certification of the proposed change, or a performance benchmark. No received repository program was executed and no toolchain was installed.

## Main results: use the maintained full-dispatch start

| Executor/start | Baseline symbolic calls | Factored calls | Saved calls | Saved fraction | Shared prefix range | Maximum complete run |
|---|---:|---:|---:|---:|---:|---:|
| Lean, `KHomeReady`, `start Q` | 514,073 | 312,947 | 201,126 | 39.1240% | 39–222 | 262 |
| Rocq, raw executor, `start Q` | 1,337,729 | 852,647 | 485,082 | 36.2616% | 123–454 | 601 |
| Optional diagnostic: Lean + Home from `leafPort` | 415,205 | 263,513 | 151,692 | 36.5342% | 36–161 | 207 |

Each row covers the same 1,425 sites and 2,850 outcomes. These are separate modes, not interchangeable measurements. The first two make the fork useful on its own without adopting a separate decoder-prefix integration. The third starts after the decoder and is only a residual diagnostic.

The minimum remaining fuel at a successful full run is respectively 3,738, 3,399, and 3,793 out of 4,000. Every shared prefix establishes positive progress. Both Home-enabled modes use exactly two Home shortcuts per shared prefix, 2,850 total; the Rocq raw mode uses none.

For site i, let p_i be the shared prefix length and a_i, b_i the two suffix lengths. The counted baseline is sum(2 p_i + a_i + b_i), while the factored algorithm is sum(p_i + a_i + b_i). Thus the saved call count is exactly sum(p_i). These are successful symbolic-stepper calls, including representational steps and shortcuts, not concrete Turing-machine steps. The audit's own work includes extra checks and replays and is not itself the claimed factored implementation.

## Exact interface and branch meaning

A symbolic configuration is `(q, onLeft, L, R)`. The cut predicate for physical register r is exactly:

- q = 0;
- onLeft = false;
- R is the singleton `[box (mark r)]`;
- L is retained in full, unchanged by the act of splitting the proof.

The register equality and singleton right-list shape are essential. Neither a control state alone, nor a short path suffix, nor normalized tape equivalence is an adequate classifier. The replay keeps the complete source word at both the dispatch start and the optional leaf port.

The prefix runs with branch `none`, initial `moved = false`, and the cut as the explicit target. The executor tests `moved && target` before invoking the stepper. It must return the cut, not attempt a neutral step at it. The two suffixes start at that returned exact configuration with `moved = true`.

For r < 9, their first symbolic steps are:

- zero: `(0,false,L,[mark r])` to `(97,true,L,[plain none])`, step progress flag false;
- nonzero: `(0,false,L,[mark r])` to `(40,true,bit true :: L,[plain (dec r)])`, step progress flag false.

The flags on these oracle transitions are conservative. They do not certify positive machine progress by themselves. Positivity for the composed result comes from the prefix's successful execution from `moved = false`.

The branch validity hypotheses remain unchanged:

- `Valid none vs`: at least 10 registers;
- `Valid (some (r,true)) vs`: at least 10 registers and register r is zero;
- `Valid (some (r,false)) vs`: at least 10 registers and register r is nonzero.

For a logical source register a, the checker retains the existing a < 9 and path length ≤ 48 guards and uses r = `physOf a`, with permutation `[6,2,0,4,3,7,8,5,1]`. The audit verifies the same permutation in the pinned Rocq checker.

The final targets are the original full `tgtConf`/`tgt_conf` values, not new approximate goals. The zero branch uses `breakPath 1 Q`, overflow on `stripPath false 1 Q`, and the plain file. The nonzero branch uses `incPath Q`, overflow on Q, and the decrement file with growth one. All terminal checks preserve `sMatches`/`matches` semantics, including normalized right segments and exterior blank trimming on the left. Empty-prefix overflow is true, as in the existing `allOnes`/`allones` definitions.

## Why the generic proof is enough

Fix the existing machine M, register-file lemmas B, natural gap parameter n, and register list vs. Suppose:

1. `exec M none cut f s false = some c`;
2. `exec M br target g c true = some t`;
3. `Valid br vs`.

The length component of (3) gives `Valid none vs`. Applying the existing `exec_sound` to (1) yields positive reachability from `conc n vs s` to `conc n vs c`. Applying it to (2) yields `target t = true` and ordinary, possibly reflexive reachability from `conc n vs c` to `conc n vs t`. Existing positive/ordinary transitivity gives positive reachability from the start to t. When the suffix target is `sMatches t e`, existing `sMatches_conc` identifies its concrete endpoint with e.

This argument works with an arbitrary cut predicate. The decrement predicate is needed to identify a useful split and validate the finite optimization, not to introduce a new tape rule. No new tape representation, box semantics, simulation induction, or generic branch-noninterference theorem is needed. The finite audit additionally verifies that all actual guarded prefixes coincide exactly with the neutral prefix and first diverge at the cut, but the generic soundness argument does not depend on that computational coincidence.

Successful execution from initial `moved = false` already proves the prefix positive. The tail starts true because the composed path has already moved; its `exec_sound` conclusion used here is ordinary reachability, not the conditional positive conclusion for a false initial flag. Resetting the tail flag to false also succeeds in every audited instance, but is not needed by the design.

## Do not use oracle failure as the stopping rule

The formal stepper does not stop merely because `oracle q none x = none`. For a singleton box it next consults the raw row `M q false`; a row `(false, left, q2)` produces a valid literal transition. At the actual K215 cut the neutral step happens to fail because `M 0 false = (true,right,94)`. That accidental property must not enter a generic theorem or classifier.

The independent audit includes a regression witness: changing only the row at `(0,false)` to `(false,left,94)` makes neutral stepping at the marked box succeed via the fallback. The classifier remains the explicit pre-step cut, independent of that row.

## Independent binding and replay checks

The new audit:

1. Verifies Git blob hashes of every source file it uses against fixed expected blobs for the pinned revision. It also records SHA-256 hashes and local source paths in its result. Source provenance is the cached pinned source metadata; no fresh remote fetch was performed by this audit.
2. Parses the maintained Lean 179-node `p215` program, checks its root and decreasing node references, enumerates all 4,751 ordered leaves, and compares the result exactly with `sites.json`.
3. Independently parses Rocq's 179-node `Prog215.v` and checks every node and the root against the Lean program.
4. Parses current decoder nodes, roles, and blocks; replays all 281 finite restoring blocks; checks structural edge bindings; and derives every entry port from the complete source word. No received port map is required.
5. Checks equality of all 430 defined transitions among Lean's table, the native table after the fixed 301→102, 302→120, 254→230 relabeling, and Rocq's table after its explicit disabled-state filter.
6. Verifies the actual Home readiness guard before using a Home shortcut: the 15 scan rows and the 18-step restoring boundary window.
7. Runs each neutral prefix to the exact cut, both baseline outcomes to their exact old targets, and both suffixes from the cut. It compares entire symbolic traces, including progress flags, and checks the branch oracle effects.
8. Requires successful target recognition with positive remaining fuel. A stuck symbolic step or budget exhaustion raises an error; neither is counted as a successful run.

Physical-register site counts are: 0:175, 1:5, 2:270, 3:28, 4:32, 5:347, 6:1, 7:34, 8:533.

## Final proposed-source review and integration gates

The reviewed final Lean adapter is `rocq/proposed/KOracleCut.lean`. It imports only `KHomeReady` and takes fuel explicitly, so it can sit below `KSim`; the initial draft's `KSim` import cycle has been removed. Its `execCut_sound` and `forkTo_sound` use exactly the two existing soundness instances and endpoint rewriting described above. The integration fragment `KSim.decnz.fragment.lean` retains both original guards, uses `physOf r` throughout, and preserves both complete targets and existing register-validity proofs. The Rocq `OracleCut.v` fragment now specifies inserting checker definitions before `check_site` and the composition lemmas inside its existing `Sound` section.

The final source hashes are recorded in `decrement_fork_reviewed_hashes.json`. Static inspection finds the intended semantic composition and dependency layering coherent. This does not assert that elaboration succeeds: neither proof assistant was available or run. The next gates are compiling the adapters, regenerating all finite leaf certificates, synchronizing generated producers/manifests, and rebuilding the sparse/dense endpoint and dependency reports.

The changed checker also is not claimed extensionally equal to the old checker at a fixed fuel for every arbitrary input. The prefix and suffix each receive their own budget, which changes the accepted search space. The generic semantic conclusion remains sound; every old and new phase in the pinned finite workload succeeds independently far below its budget.

## What the percentages do not establish

The measurements establish an algorithmic decrease in symbolic-stepper calls on the complete pinned decrement workload. They do not count target-predicate comparisons, normalization costs, allocations, proof terms, kernel reductions, memory, or compilation time. Other operation sites are not part of these denominators. The 4,751 source leaves and 2,850 decrement outcomes are not being claimed as reduced obligation counts.

In particular, a source-level `let` or `match` binding does not ensure that Lean's kernel reducer or Rocq's evaluator shares every occurrence of the computed cut. Rechecking two tails can re-normalize an expression denoting the cut. A separately stored cut configuration with an independently checked prefix equation can make the intended sharing explicit, but that is an engineering option requiring its own integration and benchmark, not an audited speedup claim. The report should say “symbolic calls saved,” not “proof compilation sped up by 39%/36%.”

## Reproduce

From the deliverable root:

`python3 audit/decrement_fork_replay.py`

Expected terminal status: `INDEPENDENT_FINITE_REPLAY_PASS`.

The script writes `audit/decrement_fork_result.json`; it prints the summary without the 4,275 per-mode site records. A saved printout is `audit/decrement_fork_stdout.json`. Preserve `rocq/inputs/` and the small pinned support-source folder `audit/decrement_fork_inputs/` when packaging. Only Python's standard library is required.

The code in this audit is new-owned code; it treats the Lean/Rocq/native inputs as inert text. It does not import or execute the author's checker. The results are computational evidence for a proposal whose final compiled obligations remain to be discharged in the repository's real toolchains.
