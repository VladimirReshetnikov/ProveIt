# Conditional-K223: reproducible construction and verification

This standard-library Python3 packet builds a 223-working-state, two-symbol, one-tape deterministic Turing machine. Its canonical table has 446 rows, start 0, source dispatcher 22 and halt 223. The claimed set-theoretic calibration retains the inherited metatheoretic assumptions; it is not a new proof-assistant kernel verification.

The canonical table SHA256 is `7edafbb2395d39e3b0895a5e0f4da61e12a371b0af71ef4cfb1a43c06e7b917f`.

Run from any directory, with an output directory outside this packet:

```
python -B reproduce.py --output-dir /path/to/new-quick-output
python -B reproduce.py --output-dir /path/to/new-full-output --full
```

Both commands verify the packet inventory and hashes first. Inputs are immutable; outputs, snapshots, logs and newly generated receipts go only to the named new/empty directory. The full command freshly derives all 6,238 guarded instruction cases over nine independent natural registers, arbitrary natural extra gap, and every nonempty finite spare list. The quick command checks the stored case hashes, complete case coverage, positive-duration forms, and exact blank startup; it does not rerun that induction.

Both modes reconstruct the exact source from its compact block-DAG recipe, reconstruct the native/canonical/legacy tables, check the final fold on open whole tapes, check the exact literal emitter and both closed Hilbert endpoints, run an independently authored source audit, replay exact startup and the source bucket induction, audit every decoder occurrence and the canonical isomorphism, and reject seven deliberate certificate corruptions. The mathematical conditional-K/equality/enumerator calibration is documented in `theory/` and the independent review in `audit/conditional223_theory_enumerator_review.md`.

## Construction

`build.py` applies 37 pinned allocation-row edits to the authenticated K224 table, obtains a 224-state conditional-K implementation, and merges native 18 into 180 by a positive-block all-tape simulation. `reconstruct_source.py` applies a 160-node structural block descriptor to the pinned baseline source. Its 4,799 instruction occurrences and every guarded control-flow edge are independently checked against the explicit conditional emitter; a hash of an opaque source file is not used as a substitute for that check.

`helper_allocation.md` explains the decisive constraint: assign the new `(CD3,A)` chunk to 37 before 11, which enables the fixed-child decoder 26. The helper states retain their existing engine transitions and were never globally unreachable. The complete 24-order census is in `helper_order_census.json`.

## Evidence and trust boundary

- `results/` preserves the deterministic construction outputs; `reproduce.py` always rebuilds them externally.
- `runtime/reference/portable/` contains a completed replay under the exact bundled portable driver; the quick mode audits this evidence. Historical engine receipts are separate provenance.
- The source-invariant and stored-runtime auditors use explicit checks and are run under Python optimization; the symbolic induction engine must have assertions enabled.
- Four finite-list block schemas are rederived from the literal table. Bounds in symbolic proof search bound certificate construction, not concrete registers or simulated execution.
- The separate theory certificates establish exact source/emitter and Hilbert bindings. Mathematical equiconsistency additionally uses the stated inherited ordinary-calculus, set-theory, macro, pairing, and enumeration contracts. No finite simulation is substituted for these universal obligations.
- `runtime/reference/helper_trimming.json` documents the only helper-library edit: deletion of an unused historical main function containing a nonportable old test path. All imported runtime functions are unchanged, and the portable replay binds their new file hash.

The unchanged 4.3 MB upstream K224 ZIP, including its full predecessor and licenses, is retained in `upstream/`; baseline input bytes are checked against its manifested members. The new replay does not rerun every inherited upstream proof.

Every file is pinned by `MANIFEST.json`; replays require a new or empty external output directory. No network, package installation or surrounding research workspace is needed.
