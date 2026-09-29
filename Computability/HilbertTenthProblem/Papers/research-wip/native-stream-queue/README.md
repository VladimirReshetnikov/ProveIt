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
| [Interleaving refutation](interleaved_compiler_collapse_refutation.md) | New positive separated-field **74** and collapsed **75** sources admit every positive input for every admitted fixed compiler, including an empty-set compiler. | This rejects those specified sources, not either previously open75 candidate. The proof here uses an independent whole-cell stride. |
| [Main-power interleaving refutation](interleaved_compiler_main_power_refutation.md) | A new **74=41M+33A** source remains false when the stride is twice the actual main Pell power. All inputs still have positive witnesses. | Reusing the packed index does not repair this specified interleaving source; the two older75 candidates remain open. |
| [Elementary prime padding](pell_kernel_prime_padding.md) | Boolean unit-cell subsets attain every residue modulo an arbitrary fixed odd factor times a growing padding length, while preserving reserved endpoint bits. | A mathematical witness-selection lemma; no extra arithmetic operation or universal compiler is supplied for free. |
| [Discriminant input-gap projection](input_bridge_discriminant_gap_projection.md) | Exact two-coset projection of a distinct **75=41M+34A** gap-deletion candidate, its fibers over genuine76 witnesses, and a certified bridge-only alias. | No full false input or soundness proof for that candidate. |
| [Unscaled input bridge](input_bridge_unscaled13.md) | Exact conditional **13=6M+7A** bridge for `W=2^x` and `x>=2`, with explicit positive witnesses. | Input 1 forces zero quotients. Fixed disjoint End variants covering every input phase exhaust the data mask; this is not a complete75 compiler. |
| [Squared-congruence kernel repair](pell_kernel_squared_congruence.md) | The same-cost change `jc` to `jc^2` preserves completeness but still permits the wrong-index kernel family; a numerical input bridge also attaches. | The actual compiler/transport is not attached, so this does not refute full75. |
| [Arithmetic-carry controller analysis](native_controller_carry_obstruction.md) | Exact carry compiler criterion, scoped affine/polynomial controller obstructions, and a nonuniversality theorem for a single-coordinate zero-absorbing affine-carry queue. | Powers/bounds remain external to the conditional 13-operation controller schedule; the multi-coordinate effectivity question is expressly unaudited. |

The mask, selector, interleaving, input-gap and squared-congruence packages
have independent scoped proof/source/receipt review passes.
The controller's carry, scalar-queue and polynomial arguments also
have independent review; the separate parametric-Presburger application was
checked against its primary theorem, without promoting algorithmic effectivity.
These are mathematical proofs with symbolic and finite checks, not Lean
formalizations or new publication bounds.

Fresh default checks for the new artifacts:

```sh
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_one_field_half_mask.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_base_four_half_mask.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_three_selector_53.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_nand_composition.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interleaved_compiler_collapse_refutation.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interleaved_compiler_main_power_refutation.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_prime_padding.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_discriminant_gap_projection.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/input_bridge_unscaled13.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/explore_pell_kernel_squared_congruence.py
python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/audit_native_controller_carry.py
```

The immediate constructive targets are a compiler using the single masked
field and a native controller composed with the three typed selectors.
The direct interleaving shortcut is now refuted, including strictly positive
separate data and verification fields and reuse of twice the actual main
Pell power. The native alternative has paid typing for three choices and
two cyclic Boolean routing ports. Its uniform NAND form has a proved
structural collapse; its three-state form has no universal computation
compiler. Larger affine state codes alone cannot encode the current
erase/copy language. A useful next construction must supply richer routing,
a proved universal local relation, or a different computation model, with
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
