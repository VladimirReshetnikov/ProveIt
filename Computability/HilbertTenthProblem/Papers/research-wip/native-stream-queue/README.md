# WIP: native queue streams and research continuation

This directory is an explicitly scoped research handoff on
`codex/diophantine-native-stream-wip`. Start with
[CONTINUATION_PROMPT.md](CONTINUATION_PROMPT.md). No local-machine files are
needed to continue in an independent clone.

**The established complete universal bound remains 76.** The native-stream
component costs six operations with external bounds, or eight with a paid
joint bound; finite-controller arithmetic and power geometry remain unpaid.
The proposed five-operation loader has no completed proof or implementation.

## Linux research continuation, 2026-09-29

The handoff was fetched and checked at `3c6494aaaca68927cce4e8cc65bfde5a45e656c3`
in a clean ProveIt worktree. The complete76 checker, native-stream checker,
four independent queue audits and bridge-rewrite checker all pass with the
pinned dependency on Linux. [LINUX_VALIDATION.json](LINUX_VALIDATION.json)
records the focused commands, results and evidence boundaries. The original
Windows receipt below remains a historical handoff record.

New research, without a change to the complete universal bound:

| Artifact | Established result | Remaining boundary |
|---|---|---|
| [One-field half mask](one_field_half_mask.md) | Exact bounded mask predicate in **51=30M+21A**, including power recovery and a positive-witness converse. The proof excludes its `F=q` boundary after the kernel. | A universal single-field compiler, input and acceptance are absent; 51 is a module count. |
| [Base-four half mask](pell_kernel_base_four_half_mask.md) | The same **51=30M+21A** predicate with retained power `X=4^(2r+1)`; even masks work with the exact origin-parity condition. | Even exponent removes one stride obstruction but does not prove compiler alignment. |
| [Native ternary selectors](native_controller_three_selector_53.md) | Exact three-label selector relation in **53=29M+24A**, with power geometry, typing, bounds and one-hot synchronization; 54 also exposes the repunit. | Controller, ordinary input, transport and acceptance remain unpaid. The first label is fixed to zero. |
| [Native gate routing](native_controller_nand_composition.md) | Complete **66** cyclic NAND relation and **67** finite three-state variants; paid routing also proves Boolean input typing. | Commuting NAND wiring collapses. The richer rule family has no universality, raw-input or acceptance proof; the Rule110 search is explicitly bounded. |
| [Noncommuting native routing](native_controller_noncommuting73.md) | Exact **73=37M+36A** NAND relation with a paid tail route, positive converse and an admitted noncommuting example. A finite-defect lemma bounds deviation from an ordinary rotation. | Universal wiring, input and acceptance remain absent. Removing the tail bound gives a refuted72 source. |
| [Restricted tail routing](native_controller_noncommuting72.md) | Exact **72** and **71** NAND restrictions, including positive noncommuting examples. The71 relation has distance at most four from one rotation, sharply, and admits a family with independent block choices. | The structural bound does not classify all solutions or establish universality. |
| [Single native word](native_single_word46.md) | Exact native typing in **45=25M+20A** using necessary signed parity; the explicit-parity46 reference is retained. | Repunit, Boolean projection, program mask, input and controller are additional obligations. |
| [Two native fields](native_controller_two_fields48.md) | Exact **48=27M+21A** two-field relation;50 exposes the repunit. The proof covers the smallest admitted index8 and both parity directions. | Two Boolean planes have a combined parity restriction and fixed initial bit; no computation is supplied. |
| [Paired Boolean fields](native_controller_boolean_pairs56.md) | Exact **56=30M+26A** relation for two independent Boolean streams and their complements, with repunit supplied. | Joint selectors and arbitrary Boolean functions are not free. |
| [Four independent fields](native_controller_four_fields55.md) | Exact **55=30M+25A** four-field relation;57 exposes the repunit. The [56/58 reference](native_controller_four_fields56.md) pays parity explicitly. | Four Boolean planes have a combined parity restriction; routing, control and ordinary input remain unpaid. |
| [Cyclic NAE/majority](native_controller_nae_majority60.md) | Exact **60=33M+27A** relation for two rotations and a not-all-equal gate with majority output, at even length. The [61 reference](native_controller_nae_majority61.md) also proves a conditional spectral restriction; the [67 source](native_controller_nae_majority67.md) permits either length parity. | This finite gate relation has no universal simulation or ordinary-input/acceptance compiler. |
| [Dual-rail ordinary-input FIFO](native_dualrail_fifo64.md) | Exact **64=33M+31A** typed FIFO initialized by ordinary `6x`, deriving field bounds from three aggregate bounds. General carry control costs nine more operations, giving73. The [65 reference](native_dualrail_fifo67.md) is retained. | The FIFO alone admits all inputs; no universal controller or accepting compiler is supplied. |
| [Joint-bounded FIFO](native_dualrail_fifo63.md) | Exact **63=33M+30A** FIFO with ordinary `6x` and `A+D<q`; the proof excludes packed overflow as well as field carries. General and equal-endpoint carry architectures cost **72** and **71**. | Controller padding must respect the joint bound. Neither architecture has a universal compiler; the complete bound remains76. |
| [Filtered carry structure](pell_kernel_dualrail_carry_structure.md) | Necessary coefficient conditions, effective width bounds outside the read-only endpoint interval, endpoint rigidity and same-sign read obstructions. | These retain the Boolean filters and do not classify the remaining coefficient family. |
| [Exact carry memory](input_bridge_carry_memory.md) | An explicit finite-window characterization of the entire labelled carry language, including boundaries, and necessary synthesis criteria. | It does not remove the FIFO or imply decidability or universality of the coupled system. |
| [Direct Rule110 synthesis](native_controller_rule110_affine_synthesis.md) | Exact linear certificates exclude all322 direct one-symbol/three-state rail assignments, with arbitrary integer coefficients. | Eight assignments have only an uncoded-output obstruction; serialization and accepted-language implementations remain open. |
| [Serialized Rule110 controllers](native_controller_rule110_serialization.md) | Exact full carry-graph audits distinguish a conditional typed transducer from a larger false accepted transduction. A [zero-code variant](native_controller_rule110_zero_code.md) has exactly the six desired coded edges and permits zero padding. | Block code typing, ordinary-input normalization, row geometry and a universal accepting simulation remain unpaid. Both unfiltered controllers have explicit escapes. |
| [Full FIFO code-typing counterexample](input_bridge_rule110_code_typing.md) | A complete positive arithmetic witness emits and later consumes uncoded blocks, yet empties the FIFO and returns its carry to zero. The six desired paths also rule out free affine rail identities for that fixed compiler. | Refutes automatic code typing for the specified01/10 controller only; no general filter lower bound is asserted. |
| [Selector/FIFO composition](input_bridge_selector_queue.md) | At most **69** operations for the complete finite three-row FIFO relation, with paid power geometry and bounds. A shared **63** specialization accepts exactly positive ternary repunits. | The established loader requires more read rows and a different origin treatment; the finite controller remains unpaid. |
| [Stateless FIFO regularity](native_stateless_fifo_regular.md) | Every fixed finite stateless table with this equal-length transport accepts a regular language of ordinary inputs, even with padding, a fixed first row and positivity flags. | This excludes a universal stateless replacement, not the existing synchronized controller or a redesigned transport. |
| [Interleaving refutation](interleaved_compiler_collapse_refutation.md) | New positive separated-field **74** and collapsed **75** sources admit every positive input for every admitted fixed compiler, including an empty-set compiler. | This rejects those specified sources, not either previously open75 candidate. The proof here uses an independent whole-cell stride. |
| [Main-power interleaving refutation](interleaved_compiler_main_power_refutation.md) | A new **74=41M+33A** source remains false when the stride is twice the actual main Pell power. All inputs still have positive witnesses. | Reusing the packed index does not repair this specified interleaving source; the two older75 candidates remain open. |
| [Elementary prime padding](pell_kernel_prime_padding.md) | Boolean unit-cell subsets attain every residue modulo an arbitrary fixed odd factor times a growing padding length, while preserving reserved endpoint bits. | A mathematical witness-selection lemma; no extra arithmetic operation or universal compiler is supplied for free. |
| [Discriminant input-gap projection](input_bridge_discriminant_gap_projection.md) | Exact two-coset projection of a distinct **75=41M+34A** gap-deletion candidate, its fibers over genuine76 witnesses, and a certified bridge-only alias. | No full false input or soundness proof for that candidate. |
| [Unscaled input bridge](input_bridge_unscaled13.md) | Exact conditional **13=6M+7A** bridge for `W=2^x` and `x>=2`, with explicit positive witnesses. | Input 1 forces zero quotients. Fixed disjoint End variants covering every input phase exhaust the data mask; this is not a complete75 compiler. |
| [Squared-congruence kernel repair](pell_kernel_squared_congruence.md) | The same-cost change `jc` to `jc^2` preserves completeness but still permits the wrong-index kernel family; a numerical input bridge also attaches. | The actual compiler/transport is not attached, so this does not refute full75. |
| [Arithmetic-carry controller analysis](native_controller_carry_obstruction.md) | Exact carry compiler criterion and scoped affine/polynomial controller obstructions. | Powers/bounds remain external to the conditional13 controller schedule. |
| [Effective affine-carry width decision](input_bridge_presburger_effectivity.md) | Constructive audit closes the multi-coordinate effectivity gap: the scoped unfiltered affine/absorbing-zero model has a decidable ordinary-input language. | Extra edge filters, nonlinear witnesses or a different endpoint are outside the theorem. The checker implements the terminal procedure, not full quantifier elimination. |

The mask, selector, interleaving, input-gap and squared-congruence packages
have independent scoped proof/source/receipt review passes.
The controller's carry, scalar-queue and polynomial arguments also
have independent review. The later parametric-Presburger effectivity audit
checks the constructive primary proofs and closes the previously recorded gap.
These are mathematical proofs with symbolic and finite checks, not Lean
formalizations or new publication bounds.

Fresh default checks for the new artifacts:

```sh
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_one_field_half_mask.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_base_four_half_mask.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_three_selector_53.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nand_composition.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_noncommuting73.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_selector_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_stateless_fifo_regular.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interleaved_compiler_collapse_refutation.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interleaved_compiler_main_power_refutation.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_prime_padding.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_discriminant_gap_projection.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_unscaled13.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_squared_congruence.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_native_controller_carry.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_noncommuting72.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_presburger_effectivity.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_single_word46.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_two_fields48.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_boolean_pairs56.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_four_fields56.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_four_fields55.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nae_majority67.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nae_majority61.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nae_majority60.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_dualrail_fifo67.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_dualrail_carry_structure.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_carry_memory.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_rule110_affine_synthesis.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_rule110_serialization.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_rule110_zero_code.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_rule110_code_typing.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_dualrail_fifo64.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_dualrail_fifo63.py
```

The immediate constructive targets are a compiler using the single masked
field and a native controller using the typed Boolean streams or selectors.
The direct interleaving shortcut is now refuted, including strictly positive
separate data and verification fields and reuse of twice the actual main
Pell power. The native alternative has paid typing for three choices and
two Boolean routing ports, including a paid noncommuting tail route.
Its uniform NAND form has a proved structural collapse; its three-state
form has no universal computation compiler. The native FIFO now composes
with the selectors with paid powers and bounds, but any fixed stateless
table accepts only a regular input language. Larger affine state codes
alone cannot encode the current erase/copy language. The full unfiltered
affine-carry model with an absorbing zero endpoint is also decidable, even
with finitely many carry coordinates. The dual-rail FIFO now types the Boolean labels and includes ordinary
input within64, or63 with a joint stream bound. Free equality comparisons
reduce general control to nine extra operations, giving a concrete72
architecture in the latter case. Its filtered-controller universality
question remains outside the full-trit decidability theorem. The exact
finite-memory criterion and serialized Rule110 experiments make explicit
why a desired transition subgraph and unpaid code typing do not suffice. A useful next
construction must supply a synchronized controller, a proved universal
local relation with routing, or a different computation model, with
ordinary input and acceptance included in its full ledger.

## Preserved and runnable work

The component proof and source live in their normal project locations:
- [Native-stream proof](../../1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md).
- [Native-stream checker](../../verification/explore_native_stream_raw_queue.py)
  and [receipt](../../verification/explore_native_stream_raw_queue.json).

The author gates passed. An independent final proof/source/receipt review
completed during this handoff with no findings, including the signed-code
capacity argument. Fresh exact receipt replay passed: 31,980 arbitrary scalar
tuples, 131,160 forward FIFO runs, and 463 paired-controller histories covering
43,665 transitions. This is a full review of the **conditional component**,
not a proof of an arithmetic controller or of a smaller universal bound.

This directory's four independent audit scripts preserve earlier machine and
stream evidence. Their import paths have been adapted to the migrated layout.
The bridge-rewrite proof/checker/receipt records no saving: schedules76,76,77,77.
The checker now compares its saved receipt by default; `--write` regenerates it.
[native_ternary_controller_encoding.md](native_ternary_controller_encoding.md)
preserves the unfinished controller analysis.

Run from the repository root with Python3.10 or later. The handoff dependency
is pinned in `requirements.txt`:

```sh
python3 -m pip install -r Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/requirements.txt
python3 Computability/HilbertTenthProblem/Papers/verification/explore_native_stream_raw_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_queue_base_three_streams.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_delayed_blank_loader.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_constant_length_one_blank.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_finite_state_raw_queue.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_complete76_bridge_rewrites.py
```

These commands use repository-relative paths; they do not require Windows,
Lean, TeX, an old checkout or credentials for the retired repository. A Windows
handoff replay is recorded in `VALIDATION.json`; no Linux execution is claimed.
The full historical checker environment may require additional dependencies.

## Archived earlier untracked research

`legacy-untracked/current/` preserves the remaining formerly untracked
research notes, scripts and receipts without promoting their conclusions.
`legacy-untracked/MANIFEST.json` lists original relative paths, archive paths,
sizes and canonical-LF SHA256 hashes. This archive excludes the three native
stream files installed above and includes the other untracked files beneath
the old research `current/` directory. It is a selective research preservation,
not a backup of build products or the entire old `tmp/` directory.

These are historical WIP artifacts with different scopes, abandoned candidates
and negative results. Counts in them are not current complete bounds. Their
old relative links or source-loading assumptions may need adaptation before
execution; the archive has not been run as a suite. Use maintained project
sources for dependencies and do not regenerate a receipt merely to conceal a
mismatch. No newly discovered complete bound below76 was found in the handoff
inventory.

The original files remain intact in the originating checkout. The remote
continuation depends only on this branch and the migrated tracked dependencies.
