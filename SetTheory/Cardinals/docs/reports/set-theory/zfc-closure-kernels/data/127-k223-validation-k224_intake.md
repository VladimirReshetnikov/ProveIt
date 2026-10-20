# K224 intake and independent replay

## Result established independently

`independent_intake.py` imports no code from either incoming archive. It passes and writes `independent_intake.json`.

- The exact K224 ZIP at ProveIt commit `49ee7cfdc8e0364c6db3614675d141d66f9350ed` has 4,404,250 bytes, Git blob `a4b02ffe27ef9f08a26d8ac722a061d2480abcb6`, and SHA-256 `cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887`.
- All 124 archive members and all 123 distributed manifest entries were checked. The safe extraction is `../intake/extracted/K224_Construction_2026-10-20`.
- All 275 files overlapping the previous local K225 proof packet are unchanged in the nested predecessor ZIP. The previous canonical table is still `f5d69a16a0324c69c8c6c407dbf18abcccf0e2d2a2283d5101ebc4591964140c`.
- The final canonical table is exactly 224 working states (0–223), 448 complete binary rows, start 0 and separate halt 224. Every working state is graph reachable.
- All448 printed transitions in the report’s TeX table independently match the literal canonical table; see `printed_table.json`.
- Canonical table SHA-256: `6361b0b29c2e0485bf8cf025dcf2606c2fac071f3f6e24fbde04016466d92168`.
- The source has 4,799 primitive occurrences, 210 distinct subtrees including leaves, depth 38, maximum zero run 6 and 6,238 guarded cases. An independently written structural-interval CFG reproduces graph SHA-256 `6c4e8fe51c856768a685b3ce53c2291015a7dbfbe3c4d8e2a89d1aa47f5e10e0`.
- The exact all-zero run after 409,835 transitions has dispatcher canonical22 = K84 = legacy96, head −5 and precisely 351 one-cells. Its logical registers are `(3,0,0,0,3,0,0,0,0)`, extra gap117 and 167 spare registers of value1; all other tape cells are zero.

## How 225 became 224

This is a changed source followed by a contextual decoder fold, not just a fold of the old fixed K225 table.

1. Cancel four double-negation pairs in the K bundle (eight negation constructors).
2. Reassociate the closed existential constructor while retaining its arithmetic result.
3. Replace the equality-vacuity binder by the canonical relation code `4P(a,b)+1`, retaining all eight logical rows, full relational vacuity, the original whole-bundle gate, proof enumeration, and the nine-register encoding.
4. Three closed source rotations expose a 225-state parent named Rel225.
5. In that parent, every incoming transition to K157 writes0 then moves right, while every incoming transition to K191 writes1 then moves right. Retain157, remove191, redirect its incoming edges, and replace retained rows by `157 0 0 L 67` and `157 1 1 L 148`.

The four exceptional parent rows have exact positive whole-tape simulation blocks of lengths3,3,5,3. Each uses only the head cell and the left neighbor and restores them to the parent endpoint; the exterior tape is arbitrary and untouched. The other446 parent rows commute with the state map in one step. The tags follow from all incoming rows and common start0, so this local fold theorem covers every binary initial tape and every initial head position. The independent script checks all these conditions and the canonical/K/legacy label bijections.

## Proof and runtime boundaries

The source construction supplies eleven finite all-register local bisimulations (263 branch/return cutpoints), exact emitter reconstruction and complete guarded-source graphs. The main helper theorem requires the actual-code K coupling: choose the private code after translating the arbitrary matrix's equality, rather than reusing its old code. The new logical certificates check 68 finite helper roots/59,947 proof nodes and 1,563 fusion nodes; they do not alone constitute the uniform arbitrary-matrix theorem. Both new checkers have also passed a fresh run with Python optimization enabled (`-O`), rejecting all four helper and three fusion tamper controls; receipts are `rel_helper_optimized.json` and `fusion_optimized.json`. The mathematical interpretation and proof-enumerator adaptation are in the archive's theory notes.

The generic runtime proof quantifies over all nine independent natural registers, arbitrary natural extra gap and first spare value, and arbitrary finite remaining spare list. A 4,000-step symbolic derivation limit is a proof-search bound, not a bound on these values or concrete execution. The expected final proof has 6,238 cases, 1,503,342 symbolic rule steps, all448 literal rows, maximum403 symbolic steps/case, and minimum13 concrete steps/case.

The archive explicitly does **not** claim a freshly compiled end-to-end Rocq/Lean theorem for this exact224-state table. Its new equality interpretation, source adapter and machine endpoint remain ordinary mathematical/executable-certificate work; pinned K230 formal evidence is inherited. Nothing here is a minimality claim.

## Fresh aggregate replay

The original inspected driver was launched as:

```
python -B research_sub224/intake/extracted/K224_Construction_2026-10-20/portable/reproduce.py --full --full-baseline --output-dir research_sub224/replay
```

An executor interruption occurred after full K226 replay, K225 construction and K225 independent checking passed, immediately after K225 runtime induction schemas started. The original interrupted receipts/logs are preserved in `interrupted_replay/`. `resume_replay.py` validates completed outputs and reuses only these stages, runs the unchanged original drivers, rederives K225 runtime, then attempted K224 phases in `../replay_resumed/`. That attempt stopped at the input manifest because other active workers had generated Python bytecode in the shared intake. No certificate failed. `finish_replay.py` now reads a freshly authenticated audit-only extraction, reuses the completed fresh K225/K226 proofs and runs the unchanged K224 driver into `../replay_completed/`. The final result is **FULL_REPLAY_PASS** in `../replay_completed/replay.json`, with all17 phases passed. Recovery provenance is `resumption.json`. The final224 runtime freshly proves all6,238 cases,1,503,342 symbolic steps and all448 literal rows in415.8 seconds, reproducing the archived case-array hash exactly. Fresh225 and226 runtime proofs also pass all6,656 cases each. No executable source/runtime/startup gate is missing; the explicit no-new-proof-assistant boundary still applies. This requests fresh K226 and K225 runtimes in addition to the final K224 runtime. K228 and K227 runtime evidence is only integrity-audited by the inherited driver, not freshly rederived. The unpacked input remains unchanged and all outputs use separate directories.

## Additional report found during intake

A later public commit `490a3c3bcd0f5ebedc5bcd9188b36e7bac8a3246` adds `ZFC_Compact_Search_2026-10-20.zip`. Its 4,009,460 bytes have Git blob `e8fb9a7981d282507b1059044dd052d08b3264a6` and SHA-256 `c120908aada195b9ee3c235c240407fcaa36b8fa4acb1b551247cb70eea5f201`. It was safely extracted separately under intake; its code has not been executed by this audit.

That report explicitly attains no machine below225 and does not supersede K224. It does contain useful search tools: seed-relative finite register invariants, precise symbolic runtime tape-window projection including list/run interiors, offset/tag/helper fold screens, open rotations, continuation-depth retuning, and measured alternative logical/source families. Its no-hit counts concern the separate DN4 225-state machine, not the current K224 candidate. Discovery workers have the exact paths and scope warnings.
