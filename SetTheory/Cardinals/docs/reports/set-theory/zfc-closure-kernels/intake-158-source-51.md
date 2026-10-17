# Source 51: geometric enumeration counters

Review completed 17 October 2026 by `/root/drop_contract`. Delivered extraction: `/tmp/zfc-intake-158/zfc_geometric_counter_research_2026-10-17/zfc_gap_clock`. All execution was on the separate copy `/tmp/zfc-intake-158/run51`. No maintained file, git state, delivered file, proof compiler, version query or dependency build was modified or invoked. Checksum manifests were ignored. The six finite Python checks below were inspected before execution; their complete drivers and executed helper closure were read. No network or third-party Python dependency is needed. The paper and all five section files were read; the four new Lean modules were reviewed at source level, with the 711-line no-filler adaptation reviewed by its full diff against bundled Enum254. Delivered formal logs are historical evidence, not a fresh kernel check by this review.

## Provenance and disposition

- Archive: `docs/incoming/zfc_geometric_counter_research_2026-10-17.zip`.
- Manuscript pin: ProveIt `85633fd2f57b5dca16f87667699134d1b500ebc0`, explicitly at `README.md:144` and `report.tex:123–125`.
- Upstream attribution: Mira-Cult, Jeff, Wade and mira-emmy; exact imported/public-reduction pins at `README.md:146–150` and `report.tex:145–151`.
- Continue `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels` as a new numbered source. Its content concerns the existing C254/252-machine spine, not a separate theory family.
- No new state record. The strongest assembled artifact has 253 working states and 506 rows, works on its prepared-frame domain, and its inherited blank start has an elementary infinite escape. Preserve all those distinctions.

## Mathematical review

1. **Two scheduler refinements are different and both correctly stated.** `report.tex:204–275` and `formal/GapClock.lean:30–177` distinguish increment at the end (observation `N=g+1[tail≠0]`) from increment at the start (observation `N=g`). The first proof checks all four input/output-tail cases; the eager variant is essentially a renaming of the logical counter at command boundaries. Each extends by finite iteration to halting, with an arbitrary total Option-valued command body. These abstract source theorems do not establish actual binary body termination or the physical loader.

2. **Parity completeness is sound and useful.** `sections/parity.tex:23–52`, `formal/ParityCandidates254.lean:21–48,87–97,135–145`: prefix an arbitrary universally halting word with MP/DROP/NIP, using the three opcode values 0,1,2. The adjacent Cantor-code differences are `q+1` and `q+2`, so at least one is odd and the three prefixes hit both parities. Argument `g+B` forces the code above both the progression start and bound. The suffix's uniform halting makes an arbitrary prefix safe for completeness even if that prefix halts itself. Soundness still needs the ordinary formula/stack invariant. The existing uniform-reset/refutation block is reused; it is not a new consistency calibration. Mere cofinality of a subset of codes would not suffice; `report.tex:465–472` explicitly retains that limitation.

3. **The stride-two scheduler closes the abstract reachability argument.** `formal/EnumParity254.lean:135–239` proves strict descent of a nonzero list pointer, drains arbitrary initial lists, reaches each later parity member unless halted, then applies the uniformly halting candidate. `complete_from` has no soundness assumption; `safe_start_iff` does. This is a source theorem over Lean Nat, not the arbitrary-internal-model PA representation currently being constructed in the maintained tree.

4. **Removing MP's truth filler preserves the full source enumerator, with a necessary compensating change in proof blocks.** `sections/no_filler.tex:19–103`; `formal/EnumNoFiller254.lean:62–71,603–650,705–709`. Successful MP changes `(B,P(0,S),B,0)` to `(B,S,B,0)`. Soundness retains the already-good stack. Completeness removes the final NIP from the MP derivation block; retaining it would pop a genuine entry of S. The full diff against bundled Enum254 changes these effects and their proofs, namespaces/imports/attribution, and adds the final equivalence. All original axiom rows, equality, GEN and CP/GIC remain. The intended one-row binary change is `(204,1)` target `113→132`; its conditional audit is separate from the source equivalence and leaves blank initialization open.

5. **The geometric transducer's ordinary all-gap invariant is coherent.** `sections/loader.tex:3–91`: first register must be zero, `g≥1`, with a valid unary suffix. At Test after k positive cycles the moving cut `j=h+g−1−k` splits the shrinking source run from the growing output run; the left block has k+1 ones. The two overwritten old rows are entered only on the opposite symbols to their ordinary-runtime uses. At k=g, the terminal zero branch restores the header and inherited cleanup leaves `(g+1,L=g+1,h−g−2)` while fixing the suffix in absolute coordinates. The three durations sum to `2g²+15g+40`, including dispatch. The finite whole-tape tests support this argument; they are not themselves a proof for all gaps. No Lean serialization of this binary transducer is supplied.

6. **The runtime cost and startup obstruction are correctly separated.** Source sharing reduces 203 decision pairs to 197, but the seven new loader states and two shell states yield `244+7+2=253` charged working states. The source shell has 8,382 guarded leaves including custom LOAD; the ordinary affine checker has 8,381 because LOAD is separately handled. Maximum depth 36 fits the required gap at least 40. At least nine physical blocks are retained even though only eight logical registers are active. The inherited start reaches `(state42,head12,ones={4,6,10})` at 102 steps; `(42,0)→(1,R,42)` then proves an infinite rightward escape. This is stronger than a fuel cutoff and positively rules out that particular bootstrap as the desired consistency-calibrated construction.

No mathematical blocker was found in those scoped arguments. The source-level Lean proofs were not freshly elaborated here, and none of the finite runtime checks proves the full new binary consistency endpoint.

## Corrections required in the synthesis

1. **Wrong characterization of the user's requested base theory.** `README.md:164–168` and `report.tex:56–58,108–119` say the user requested provability in ZFC and that PA is stronger than requested. This thread explicitly requests the nonhalting/Con(ZFC) equivalence *provable in PA*. Preserve the source statement as delivered but correct it explicitly in the integration: ordinary ZFC arguments are relevant intermediate mathematics; they do not change the target.

2. **Stale Choice-calibration status.** `report.tex:392–400` describes serialized Choice removal as still open. The current maintained `Computability/BusyBeaver/Research/ZFC/binary_perm252.md:47–56` records the complete external Lean equivalences from ChoiceCalibration254 and BinaryZFC252, with no added premise. Lines 58–60 explicitly keep PA formalization open. The paper's snapshot pin explains its old status; do not perpetuate it as current status.

3. **Stale records remain historical.** The bundled `experiments/no_filler_frozen/inputs/candidate252_independent_audit.py:235` lists the old binary bootstrap/simulation as remaining obligations. Its helper is inherited provenance; those are now completed for the original maintained permutation252 table. They remain genuinely open for the newly changed runtime and cannot be transferred silently.

4. **Historical formal timing is not the final bundled timing.** `sections/no_filler.tex:143–146` says 5.247 seconds. The bundled final `formal/verification/verification.json` records EnumNoFiller254 at 4.805771182 seconds in a 15-module build. Treat the prose as an earlier recorded run; avoid presenting one as the other's exact timing. This does not affect the mathematics.

5. **Do not replace the just-checked original MP endpoint with the alternate semantics.** The maintained complete actual MP proof preserves the original success filler `cantor(0, old WS)`. The new no-filler result proposes a distinct source/machine variant and would require its own changed actual-control contract, calibration and bootstrap.

## Fresh bounded verification

The command prefix below is `timeout 120s uv run --no-project --offline python -B`, executed with cwd `/tmp/zfc-intake-158/run51`. All six processes returned code 0. Logs are under `review-logs/`.

| Command after prefix | Result |
| --- | --- |
| `clock_schedule.py --candidates 100000 --output data/clock_schedule_results.json` | 576 local cases; 300,000 candidates and 374,146 commands over starts 0,40,137. Mutation rejected. Regenerated JSON exactly matches delivered JSON. |
| `gap_dag_audit.py --source machine/inputs/Prog254.v --output gap-dag-audit.json` | Original/body/shell pairs 203/194/197; leaves 6460/6450/6453; guards 8391/8378/8382; depths 34/33/36. New shell has zero ordinary root overflows. JSON exactly matches delivery. |
| `machine/code/assemble_gap_runtime.py` | 8,381 affine cases, minimum 15 literal transitions, 288 loader cases; pruned runtime rechecked; 253 states/506 rows. Exact old-label and canonical runtime tables regenerated. Full 102-step escape reproduced; one-million-step continuation reaches state42/head999910. JSON exactly matches delivery. |
| `experiments/no_filler_unit/check_no_filler_unit253.py --runtime-root machine --output experiments/no_filler_unit/replay` | 8,356 conditional affine cases plus 288 loader cases. 53 protected rows; all 506 rows required, no freed row, 253 states. JSON exactly matches delivered results. |
| `machine/code/gap_loader.py --fold-past` | Earlier nine-state/stride-two loader: 288 whole-tape cases; exact time `2*g*g+19*g+54` plus dispatch. JSON exactly matches delivery. |
| `experiments/no_filler_frozen/nofiller_frozen_search.py --input-dir experiments/no_filler_frozen/inputs --output experiments/no_filler_frozen/replay --seconds 100` | All 8,366 base guards pass. Complete 55,471-fold census, 127,407 affine checks, zero survivors in 43.723 seconds. All 55,471 journal rows are byte-identical to the delivered journal. Only `elapsed_seconds` differs in results JSON. One-million-step bootstrap remains an uncertified fuel result (state85/head686). |

The comparison summary is `/tmp/zfc-intake-158/run51/review-logs/result-comparisons.json`. No result is inferred from a filename or manifest alone. Existing source identity assertions inside the functional scripts were preserved; no separate checksum-manifest audit was performed.

Not rerun by this review: the 15-module Lean build; generic Wade compilation; supplementary mixed-box, disjoint-swap, root-entry and full start-label searches; LaTeX/PDF build. Their delivered evidence remains attributed historical evidence. The principal finite suites and complete advertised frozen no-filler fold census above are independently reproduced. The generic compiler and other supplementary numerical claims must retain their recorded, unreplayed scope unless another intake reviewer runs them.

## Recommended next work

- Retain parity completeness and the uniform-reset padding method as a reusable completeness interface for alternative physical counters. General modulus m needs a residue theorem; cofinality alone is insufficient.
- Treat no-filler MP as a justified new input to whole-program optimization. It saves proof-block instructions and changes possible contexts even though the direct measured table still costs 252 and the geometric combination still costs 253. It may be combined with future source changes without weakening C254, provided the new operational and bootstrap obligations are proved.
- Any geometric-counter search should optimize the charged runtime and initializer jointly. The exact failed initializer is evidence against simply grafting the seven-state loader onto the inherited start. A smaller loader alone would not close the target.
- Adapt the current actual MP comparison/parameter-copy contracts to a *separate* no-filler branch if a concrete smaller artifact warrants it. Do not divert or weaken the maintained PA-equivalence proof of the existing 252-state table merely to adopt an uncalibrated runtime.
