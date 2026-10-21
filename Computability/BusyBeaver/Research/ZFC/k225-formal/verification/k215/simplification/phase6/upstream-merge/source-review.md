# Read-only merge boundary for origin/main bec5e93775

The upstream production delta is exactly20 paths: two Lean modules, their one DomRho8 producer, and17 Rocq source/input/generator/manifest paths. No other production Lean root, maintained formalism producer or canonical file outside those groups changes. The much larger remainder consists of incoming arrivals and proposal placement; it was not reviewed as new canonical proof code.

Retain the current working bytes for the12 existing paths in `keep-current-paths.txt`, including the three files upstream deletes. Retain the absence of the eight new canonical Rocq paths in `keep-current-absences.txt`. `review.json` pins all20 decisions. These lists are recommendations only: no checkout, merge, index or canonical mutation occurred. Root should first commit the completed phase6 checkpoint, then use that concrete commit as the retained-byte source. Upstream proposals and commits remain available unchanged in Git; no archive or proposal payload should be removed by this resolution.

## Lean

Upstream `KSeedModel222.lean` is byte-identical to the first isolated semantic-cleanup attempt already recorded locally (SHA603e7457…). Current phase6 SHA516f8751… additionally preserves attribution, removes the unused `hirr` helper parameter with five adjusted calls, removes eight unused simp arguments, and has the recorded zero-warning successor. Taking upstream would regress that cleanup; retain current.

Upstream `DomRho8.lean` and `generate_domrho8_lean.py` are byte-identical to the aggressive files in the b070 delivery reviewed under `/tmp/k215-b070-domrho8-review/delivery/`. The pointwise lifting argument is coherent: cd99 and cd88 lift a proved implication beneath an arbitrary antecedent; J+K gives q→(b→c); composition plus two lifts yields the unrestricted rho8 row. It eliminates the private deduction machinery, but also deletes public `distribution` and cd100–106. The upstream producer normalizes CRLF before checking a single LF hash, accepting mixed endings as well.

The held compatibility candidate at `/tmp/k215-b070-domrho8-review/candidate/` restores the exact old public distribution theorem and its seven supporting schemas. It retains all previous public signatures and adds lift_right; it pins exactly the two known LF/CRLF template byte strings instead of normalizing arbitrary mixtures. That is the preferred future proposal under the existing API-preservation policy, but it remains uncompiled. Neither upstream's claimed enumerator rebuild nor the earlier delivery's component receipt is a check of this compatibility successor or the currently frozen phase6 full endpoint. Retain current DomRho8 and its producer for this merge, then evaluate the held successor separately.

## Rocq

Commit5a09be9b09 replaces the215 offset relation with normalized one-sided checking, adds PathCodec/BisimMirror/NormalizedBisim and a1,426-entry certificate, updates Source215, and changes both the compile plan and regeneration/manifest inputs. Three existing offset files are deleted. Source215.p215_dagPerm retains its statement, but the proof closure changes. The commit message reports a44-module closed compile under Rocq9.1/stdlib9.0 and explicitly says recursive coqchk was not rerun. This read-only review did not verify those claimed executions.

Keep the entire current17-path Rocq delta as a unit: retaining only Source215 while accepting the new manifest/generator would make future regeneration inconsistent; keeping the new source theorem while restoring the old compile plan would omit its imports. The existing verified Rocq checkpoint and its recursive kernel evidence remain the current boundary. No new Rocq implementation is requested in the active Lean simplification work, so preserve these changes only as deferred upstream history/proposals for now.

## Scope

Read complete diffs of both Lean sources and the Dom producer; compared exact upstream bytes with the held b070 delivery and first seed attempt; read the held API-preserving candidate review and exact file pins. Read the Rocq source/registration/build/regeneration deltas and commit scope. No full new archive intake, generation, compiler invocation or execution of upstream code occurred. No result about phase6 completion is inferred here.
