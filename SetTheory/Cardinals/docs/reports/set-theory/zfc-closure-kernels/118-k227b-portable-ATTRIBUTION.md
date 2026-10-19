# Attribution, runtime provenance, and license scope

## Inherited foundations

The original compact proof-search calculus, formula encoding, source program, single-marker interpreter, and 254-state construction are credited to **Mira-Cult**. **Jeff Ketchersid** supplied the upstream end-to-end verification, and **Andrew James Wade** supplied the compiler framework. The successive source, routing, startup, and state-sharing reductions retain their original attribution. This packet does not claim those inherited contributions as new.

The supplied K230 development and its theory-specific changes are preserved under `upstream/K230/`. Its exact provenance and the scope of the retained licenses are described in:

- `upstream/K230/provenance.json`
- `upstream/K230/manifest.json`
- `upstream/K230/THIRD_PARTY.md`
- `upstream/K230/LICENSES/`

In particular, the K230 source records that some custom upstream proof sources have no identified root or explicit license notice. The MIT-family and MPL notices retained for other components must not be extended to those files by implication. This packet asserts no new blanket license for the combined material.

## Byte-identical symbolic runtime dependency

The two files in `runtime/` are copied **without modification** from the supplied `zfc237-research-20261019/verification/` directory:

- `symbolic_runtime.py`: SHA-256 `c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145`
- `independent_runtime.py`: SHA-256 `0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346`

These are inherited mathematical checking programs. Their historical header wording, including "Self-authored," is preserved as part of the byte-identical source and is **not** a claim that this packet newly authored them. The preserved historical attribution traces the affine/unary/list checker through the earlier 239-state research packet and 241 companion. The helper remained unchanged; the engine's historical adaptation concerned source-list validation metadata rather than its transition or induction rules.

The preserved attribution and archive provenance can be inspected in:

- `licenses/ATTRIBUTION-historical237.md`
- `licenses/ATTRIBUTION-source80.md`
- `licenses/PROVENANCE-historical237.json`
- `licenses/SOURCE_PINS.json`

The cited historical ProveIt checkout is commit `ce192939372ac7944fe2a0208c68a96d49fb5e3b`; its inherited source/calibration pin is `13ec39ed43148b1807f51ed6e6528e1c84659562`. These identify historical provenance; replay of this packet does not need to fetch those repositories.

## Portable wrapper

`replay_runtime.py` is portable orchestration adapted from the existing composition driver `research_sub235/compositions/prove_runtime.py`, whose exact digest is recorded as `original_driver_sha256` in `RUNTIME_DEPENDENCIES.json`. The wrapper checks its own and both engine file hashes, validates the exact bundled table/source/configuration, and calls only the generic `table`, `prove_blocks`, and `case` APIs. It does not execute either historical engine's standalone `main`, old source loader, or source-specific `validate_inputs` entrypoint.

The wrapper does not introduce new symbolic inference rules. It freshly rederives every exact-table one-block schema and every guarded source case, then compares the full case and block certificates and every nonexecution result field against the sealed receipts. The elapsed time and wrapper hash are explicitly excluded from result equality because they necessarily change on replay. The sealed wrapper hash is separately pinned.

Only Python 3.10 or later and its standard library are required. Assertions must be enabled; optimized Python is rejected. No imports from another research tree, package installation, network access, or external proof-engine checkout are needed. Historical unused entrypoints remain in the unchanged source files solely to preserve their exact bytes.

## What the runtime evidence means

The replay uses literal transition rules plus unary induction and finite-list structural induction. It covers independent natural primary registers, both decrement guards, arbitrary natural extra gaps, an arbitrary first spare value, and an arbitrary finite spare tail. It checks the exact whole-tape, head, source-successor, and positive-duration contract.

This is executable ordinary mathematical evidence. It is not a new proof-assistant kernel theorem, not a serialized PA/ZFC derivation, and not a finite numerical simulation offered as a universal proof. The source/theory calibration and its stated proof status remain separately attributed to the supplied K230 development and the other packet certificates.

## Retained notices

`licenses/` preserves the original ProveIt and Wade license texts, original-source notices, historical attribution, and the K230-supplied BusyCoq MIT, LibTactics MIT-X11, Undecidability MPL-2.0, and Wade MIT-0 notices. Duplicate K230 notices are provided for convenience; their authoritative source context remains under `upstream/K230/`. Retaining a notice does not enlarge its original scope or assign a license to otherwise unlicensed custom material.

## Separate 227-state extension

This directory is a separate extension of the sealed 228/229 packet; the original packet was not modified. The additional `source_fold227_zerofix` candidate uses the repaired source reassociations, role reallocation, and contextual fold recorded in its construction and source certificates. Independent full literal and jump-resolved source CFG comparison binds its exact ordered primitive occurrences to the proved 228-state source. No historical receipt is relabeled as a fresh run.

The same byte-identical inherited runtime engine is used for the 227-state candidate. Its separate portable replay rederives every block and guarded case from the exact new table, then compares against that candidate's own sealed receipts. The new runtime wrapper differs only in admitting the additional candidate name and extending the pinned input manifest; it introduces no new mathematical proof rules.
