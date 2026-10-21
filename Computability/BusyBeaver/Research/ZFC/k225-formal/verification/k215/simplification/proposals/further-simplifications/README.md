# K215: further proof simplifications

21 October 2026. This is a separate follow-up research packet. It does not replace or modify the earlier delivered packet. It is **not a newly kernel-verified endpoint**, and it establishes **no 214-state construction**.

Start with `report/report.pdf`, then `review/REVIEW.md`. The editable report is `report/report.tex`; `report/qa/QA.json` records its visual/build checks. Topic reports and pinned source inputs are self-contained under the following directories:

- `recent_commits/`: historical source/receipt audit plus the separate `phase5_refresh/` production-adoption update. The earlier placement-only addendum at `62f0f95e2b2df5b380ae502eb65bd64f1ee90209` is retained as history, not the current production status.
- `runtime_contexts/`: a reusable, table-specific return-to-dispatch contract, full symbolic endpoint replay, independent full-tape checks, and context-preserving decoder factoring.
- `runtime_boundary_optional/`: a separately reviewed boundary-only extension, preserving the primary runtime results.
- `calibration/`: fresh-variable padding and a named-syntax semantic kernel specification, avoiding unnecessary decoder round trips without assuming an injective codec.
- `wellformedness/`: derive break/continue summaries and topological rank instead of supplying three witness arrays. All 487 bounded nodes, including unreachable nodes, remain checked.
- `terminal_contract/`: weaken immediate terminal agreement to terminal drain under deterministic partial-step semantics and positive progress.
- `review/`: independent mathematical review and separate finite corroboration.

## Evidence boundaries

The latest production refresh is pinned at `0359ebda60aaf52758358e1450a04988136db67e`, following phase-5 adoption at `de9fdb0873b36d049d075a5c0568f2dfcff28e7a`. That adoption is distinct from the earlier proposal placement. Its saved 184-module result is recorded upstream evidence, not a fresh build here; the outer-session exit 143 and accepted saved/live evidence are kept separately. This packet checks source/hash consistency and **does not rerun the upstream compilers**. The finite experiments retain their original `beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc` input pins rather than silently rebinding historical results to the new head.

The newly authored Python programs supply finite, independently replayable evidence. Ordinary mathematical arguments give the proposed unbounded specifications. Neither a Python PASS nor a source hash is a Lean/Rocq proof. All new formal drafts and derivative patches are explicitly **uncompiled**. Upstream Lean/Rocq/Python files under `sources/` or `inputs/` are reference data, not executed code.

The home shortcut preserves all 6,176 original branch endpoints while reducing abstract symbolic dispatches from 2,442,801 to 926,351. The separate optional boundary experiment reaches 926,299 dispatches, saving 52 more, without changing the primary 926,351 scope. These are operation counts, not runtime, kernel reduction, proof-size or compilation-speed measurements. The named-kernel, shortcut soundness, generic WF checker and endpoint integration gates remain open. The normalized source lane already consolidates WF into one module; deriving its summaries does not eliminate sixteen current WF modules.

## Portable replay

Requires Python 3.10 or later, with its standard library only. No network, Git checkout, package installation, Lean, Rocq, TeX or historical research workspace is required.

From any directory:

    python3 -I -B /path/to/research_proof_simplification_next_release/verify_release.py --negative-controls

For package-byte integrity only:

    python3 -I -B /path/to/research_proof_simplification_next_release/verify_release.py --hash-only

Without `--negative-controls`, the verifier runs twelve positive/data-consistency checks. The optional flag adds the runtime rejection suite and outer package-isolation controls. The source-pin check verifies 242 bundled source occurrences plus the reviewed-artifact hashes. Check counts and timings are recorded in `REPLAY_RECEIPT.json`.

The outer verifier refuses `-O`, `-OO`, and any `PYTHONOPTIMIZE` setting, verifies the pinned manifest and every payload byte, and copies the complete packet to a temporary directory. Only its explicit allowlist of owned programs runs, under isolated Python. Regenerated principal files must be byte-identical to their archived outputs; the terminal result must equal its archived JSON. The original release is checked unchanged afterward. Do not redirect output into the release: an extra file fails integrity validation. Direct checker invocation may write adjacent outputs, so prefer the outer verifier.

## Hash and receipt binding

`MANIFEST.json` lists every payload file except itself and the outer verifier. `verify_release.py` embeds the manifest's exact SHA-256. Authenticate the delivered ZIP using the separately supplied digest before relying on this chain. Internal hashes are not signatures or external proof of provenance.

To avoid a circular receipt hash, `REPLAY_RECEIPT.json` describes the successful staging replay against the exact preserved `REPLAY_INPUT_MANIFEST.json`, before replay receipts and final release bookkeeping were added. The final manifest pins both that input manifest and its receipt, as well as the final documents. `REPLAY_BINDING.json` confirms that the staged replay payload remains unchanged. A separate `FINAL_REPLAY_RECEIPT.json` beside the delivery ZIP records a second, complete replay of the exact sealed final release; it is deliberately outside the ZIP. The ZIP digest and final-manifest digest are recorded beside that final receipt, not embedded circularly in the ZIP.

## Contents and exclusions

`SOURCE_PIN_CHECKS.json` records reproduced Git-blob/SHA-256 checks; `STAGING_SELECTION.json` identifies copied and omitted files. Python caches, compiled binaries, TeX auxiliary files, PNG-render bulk and transient local logs are excluded. The stale nested terminal manifest is omitted in favor of the outer manifest. Selected upstream receipt/log excerpts remain as historical evidence.

`PORTABILITY.md` documents the execution boundary. `PROVENANCE.md` and `licenses/` preserve attribution and prior notices. Those notices are not a blanket license grant for custom files with unresolved license scope. The optional `report/build.sh` rebuilds only the report with an installed TeX Live environment and is not run by finite replay.
