# Batch 165: source blocks and workspace after the 245-state endpoint

Source 69 adds *Toward fewer than 246 states: Certified source blocks, unused workspace, and concrete obstructions*, delivered in `36633bfe16c90d9db1a8ab4b5cb35241da4b31ca`. It gives a more flexible simulation method, numerical invariants and exact rejected-candidate witnesses. It establishes no new smaller consistency machine. Its reference is the older 246-state construction; the maintained baseline is now the [closed external 245-state Lean endpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/routing245_binary.md). The internal PA proof remains open.

The report is an addition to this host, with 454 ancillary files preserved unchanged and 12 manuscript/PDF/TeX/delivery files recoverable from the committed archive: 466 files total. Placement `500381f8f1b4f450870895a642a2845a15a008ea` precedes this reconciliation. The existing base article remains unchanged. The exact [placement map](data/intake-165-placement.json) and [reproduction instructions](intake-165-reproduction.md) restore the original directory names before any replay.

This placement also retires a reintroduced copy of `zfc245-proof-20261018.zip`. Its Git blob is exactly the original source 68 archive, `4f5f4bf61ab41a68221c50fef160ddc0cd27e0c1`, from `8286787dd0468d848db345debe304b002d7064a4`. All 273 ancillary blobs were confirmed in their original placement tree `46e8518e0eddc4bc16a7a1b38cd21bd58abf9226`. It receives no new source number. [History evidence](data/intake-165-history-matches.json) distinguishes this exact repeat from the still queued reports.

## What changes in the simulation method

The report's positive finite-block simulation theorem permits one binary execution block to implement several source instructions. Both source and binary progress must be positive, the source block must avoid executing halt, and every accepted binary endpoint must recover a related source frame. Source halt has its own finite binary-halting obligation. These hypotheses support both directions of halting equivalence by finite induction; merely revisiting a dispatcher or observing a long active run is insufficient.

The workspace relation forgets absolute head location, extra zero-gap space and a finite nonempty spare suffix. It retains all nine primary register values and the entire clean tape shape. The delivered engine checks a pointer together with its full register-offset vector; matching the pointer alone is unsound. A changed table must preserve or reprove the register macros, check all required guarded blocks and establish its own blank initialization. The original 246 source uses gap at least 40; that bound is not automatically a contract for the different routed 245 source.

| Certificate or experiment | Delivered result and limit |
|---|---|
| Broad-root numerical invariant | 6,456 admitted leaves, 8,384 nonhalt transfers and 5,518 exact-zero facts. |
| Restricted-root invariants | 5,551 zeros at cutoffs 2, 4, 8 and 16. The extra 33 come from restricting the initial state, not from the larger cutoff. |
| Existing source exclusions | Four absent leaves and two impossible positive branches, credited to earlier research. They do not themselves remove a binary state. |
| Quiet blocks | 10,563 endpoints; 2,050 of 8,385 admitted guards have extra endpoints; maximum five source instructions. |
| Arithmetic blocks | 17,643 endpoints; 4,856 cases have extra endpoints; maximum 13 instructions. All 8,384 nonhalt closures stop before an undecidable decrement or halt; none stops at cap 32. |
| Six local action-domain records | Each records 254,856 trials and the same local domains. Intake compares the records; it does not rerun these searches. |
| Eight joint rerouting obstructions | Exact finite graphs with 19 nodes and 128 edges, using unbounded sparse tapes. They refute the stated joint choices at displayed frames, not every smaller machine. |
| Constant-transfer rewriting | Eighty placements; smallest retained initialized runtime is 252 states. No changed blank initializer. |
| Cooperative decoder pivot | Three representatives preserve all transported macro rows; 8,820 full symbolic repair trials have no survivor. Fifteen other representatives have exploratory results because they change a macro row. |
| Two source-loop deletions | Shared decoder sizes 206, 204 and 207, with emitted runtimes 252, 247 and 253. No improved blank-start result. |
| 238 closed source variants | 59 finite-filter rejections, 153 full guarded passes, 26 guarded failures. Five smallest initialized runtimes remain 246; 271,950 fold and 651,700 sole-entry trials find no survivor. |
| Origin-preserving emission | 260 rotation/control choices; 198 guarded passes and 40 distinct 246-state ties. No new blank initialization. |
| Detector pair families | Nominal 1,759,392 and 855,938,304 assignments lead to 895,440 and 15,635,760 concrete completions, with no accepted result under the stated finite screen. Nominal counts are not all executed machines. |
| Existing-label blank starts | Only old 95 reaches the required root within ten million transitions and the stated head window. This does not establish unbounded uniqueness. |

The finite invariant starts with all nine root fields arbitrary in its broad form. The narrower cutoff-4 root masks also admit any positive N with A = X = Y = 0 and the other fields arbitrary; this is an execution invariant, not a replacement for the safe formula/cache/stack premises of logical calibration. All 472 rows directly inspected by the original symbolic instruction traces still occur after the six exclusions. The separate register-box contracts remain necessary.

Two origin-prioritized greedy congruence orders additionally reduce rotation 42 from 254 to 249 initialized runtime states, preserving all 42 macro-used rows and passing the delivered guarded replay. These results have no verified blank initialization. The shortened-detector screens require 25,173 finite frames, at most 2,500 transitions and 16 dispatcher visits, within a 512-cell tape window; their completed finite rejection is not unrestricted semantic impossibility.

The new ordinary proofs and their assumptions are detailed in the preserved [source audit](69-blocks-reviews-source-block-workspace-audit.md). Numerical mask closure is the universal invariant argument; the finite sampled arithmetic traces are additional implementation checks. The state-4 nondeterministic exploration and hybrid-macro follow-up were incomplete and remain labelled as such.

## Why the two retained 245-state tables are rejected

`tail_trap245.tm` enters the closed state set `{48, 63, 112, 131}` after three transitions of its own blank run. Every row there moves left within that set. Thus elementary induction proves unconditional nonhalting. Assuming Con(ZFC), ZFC cannot also prove that nonhalting equivalent to its own consistency. Its survival of 21 finite two-row macro screens, totalling 20,168,400 recipe occurrences, does not rescue it. A further 6,860-recipe repair screen also fails.

`short_detector245.tm` fails 36 original guarded cases. An exact failing frame appears after 1,700 source instructions and 6,012,481 binary steps of the **reference 246** blank computation. The mutant is tested from that reference frame; this is not a claim that its own blank run shares the prefix. The two next pointers differ. When the original source first reaches the mutant pointer 146 source steps later, its theorem-stack register is 10 rather than 0. The difference survives the workspace abstraction. It rejects this intended simulation, not every conceivable alternate calibration of the table.

Neither rejected table is the subsequently verified routed 245 machine. Their exact bytes and explanations remain in the [rejected-table note](69-blocks-rejected-README.md).

## Fresh checks and formal scope

The unmodified main driver passed all 14 named jobs on a complete disposable copy in 36.176 seconds. Eight supplemental checks also passed: the remaining reference-suite checks, independent reconstruction/audit and contextual-emitter baseline. The independently rebuilt tables match the delivered reference bytes. The emitter's JSON explicitly reports 203 decoder nodes, 246 initialized runtime states, 8,391 guarded cases and no failures; exit status alone was not used as that conclusion.

The [main execution record](data/intake-165-source69-main-execution.json), [supplemental execution record](data/intake-165-source69-supplemental-execution.json) and separate [main](data/intake-165-source69-main-review.json) and [supplemental](data/intake-165-source69-supplemental-review.json) reviews retain their scopes. The main driver includes one comparison of recorded search domains. No large discovery search, delivery-checksum audit, Lean/Rocq compilation or TeX build was performed in these replays. Python checks do not create a new kernel theorem.

The delivery was written against ProveIt `8cdc55ff9281b0aaba49bf74b0b225d57f12b893` and busy-beaver `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. Its ordinary target is a **ZFC-provable** consistency equivalence; no serialized PA proof is claimed. Its model-construction discussion does not discharge the current arithmetic interpretation obligations. The [current project criteria](../../../../../../Computability/BusyBeaver/Research/ZFC/README.md) also permit stronger theories under accepted consistency benchmarks with proved upper and lower calibration bounds. This source proposes no stronger theory.

The report also retains its incompleteness caveat: for a correctly calibrated machine, Con(ZFC) gives nonhalting and ZFC-unprovability of that nonhalting statement. Bare consistency alone does not exclude a ZFC proof of the false existential halting statement; a suitable Σ₁-soundness assumption gives the stronger two-sided conclusion. No two-sided independence claim from consistency alone is added here.

Attribution follows the unchanged [notice](69-blocks-NOTICE.md): Mira-Cult's original program and calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework, mira-emmy's public 253-state step, and the subsequent ProveIt and incoming-contributor reductions and logical calibration. Imported material keeps its original notices and licensing boundaries.

The existing `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RuntimePerm252.lean` already proves positive-segment halting equivalence through `PositiveSimulation.step` and `halts_iff`, with exactly one source instruction per segment; `RuntimeInstanceRouting245` reuses that contract. A useful next formalization is the report's positive **multi-instruction** source-block extension with a whole-frame workspace relation. It could justify a future reduction that reaches a later source state. Raising the delivered closure cap alone has no demonstrated benefit: these closures stop at uncertain arithmetic branches rather than at the cap.
