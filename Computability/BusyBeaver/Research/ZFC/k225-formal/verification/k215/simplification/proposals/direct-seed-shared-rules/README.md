# K215: direct seed models and shared propositional proofs

**Two checked proof-simplification components, with a 14-page research report.**

Reviewed ProveIt revision:
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

Date: 2026-10-21, America/Los_Angeles. The commit timestamp is 2026-10-22 UTC.

The principal recommendation is to use the original completeness model directly
in Lean's lower bridge, and to share the remaining duplicated propositional
derivations between the two Rocq named calculi. No machine transition changes.
This packet does not modify the public repository.

## Read first

- `report/main.pdf`: complete report, mathematical proofs, exact measurements,
  verification limits, integration sequence, prior-work attribution, and further
  research questions.
- `report/main.tex` and its four `.tex` inputs: editable article sources.
- `lean/README.md`: direct-seed patch and clean replay.
- `rocq/README.md`: shared propositional core and concrete adapters.
- `evidence/final-audit.md`: independent mathematical/source/evidence review.

## Results and exact scope

| Component | Result | Verification performed |
| --- | --- | --- |
| Lean direct full seed | `FullSeed mem` on the original domain; preliminary indiscernibility quotient removed from active lower bridge | Lean 4.32.0, 112 fresh project compilations, no project cache reuse; generic endpoint plus direct and legacy API clients; all eleven expected assumption profiles |
| Lean K215 source closure | 178 -> 177 modules; 40,517 -> 40,387 physical lines; 2,093,112 -> 2,086,255 bytes | Independent read-only source/import census, including new proof and interface costs |
| Rocq shared propositional core | 71 derivations shared by two real instances; all old names retained | Coq 8.18.0, ten compiled modules, 142 exact signature checks, 26 closed reports, recursive `coqchk` |
| Rocq paired source reduction | 297 -> 261 lines; 23,160 -> 16,001 bytes | Includes the common core and both facades; 7,159 bytes / 30.9% reduction in this selected scope |

**Limits:** the physical K215 certificate closure and final `KEndpoint215` were
not rebuilt. The full production Rocq 9.1.0 / stdlib 9.0.0 endpoint was not
rebuilt. Those remain integration gates. Existing full-endpoint receipts
certify the repository's old exact sources, not the new overlays.

The Lean reduction concerns the active endpoint closure. Retaining the optional
old quotient/equality-free APIs adds 184 lines and 7,472 bytes across the six
production files overall. It is not a repository-wide source deletion. The
Rocq reduction requires adopting both facades: keeping the standard duplicate
and replacing only the restricted file would grow the selected source by
97 lines and 3,653 bytes. No build-speedup or proof-object-size claim is made.

## The mathematical change in Lean

`KEind222.c222_complete` takes derivability of `enc (th f)` on its syntactic
side, but its model hypothesis supplies satisfaction of the original formula
`f`, including literal equality. For every formula `psi`, choose

    m = not (not psi)
    k = enc (th m).

The checked lemmas `Free i f -> i < enc f` and
`Free i f -> Free i (th f)` imply that `k` is not free in `m`.
Double negation ensures `k > 1`. The named bundle at role names `0, 1, k` is
derivable and its direct semantics gives the seed property for `m`; pointwise
double-negation elimination gives it for `psi`. The later tagged-domain and
bisimulation-quotient ZF construction remains unchanged.

This is a checked implementation of the earlier uncompiled
`sharing-interfaces/calculus/DIRECT_FULL_SEED.md` proposal, following the
existing Rocq `Complete222.v` fresh-code construction. Those origins are
acknowledged rather than claimed as new.

## Reproduction

Use an unmodified checkout at the pinned ProveIt revision. The Lean replay
validates exact source/import identities and runs in a new output directory:

```sh
python3 lean/replay_direct_seed.py \
  --repo /absolute/path/to/ProveIt \
  --lean /absolute/path/to/lean-4.32.0/bin/lean \
  --output /absolute/path/to/new-empty-lean-replay
```

For a source census (this does not compile proofs):

```sh
python3 tools/closure_census.py /absolute/path/to/ProveIt \
  --module-overlay lean/overlay \
  --output /absolute/path/to/proposed-closure.json
```

The Rocq component's pinned source inputs are bundled. With Coq 8.18.0 on
`PATH`, run from `rocq/`:

```sh
python3 generate.py
python3 check.py
```

The `rocq/README.md` explains the single standard-library import spelling
adjustment and the distinct production namespace, manifest, generator,
external-provider-overlay, and Rocq 9.1 integration requirements.

To rebuild the article, run from `report/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The six-file Lean production patch is `lean/direct-seed.patch`. The two audit
clients are in its overlay but are not production patch hunks. Reviewable Rocq
source patches are under `rocq/patches/`; they are component patches, not a
claim that the frozen production driver already accepts a new logical root.

## Evidence and preservation

`evidence/source-pin.json` records the reviewed commit and recent changes.
The baseline/proposed closure JSON files include every project module's hash,
imports, byte count, and physical line count. Both proof packets preserve their
raw successful logs and exact source bindings. `evidence/manifest.json` hashes
all delivered files except itself. Compiled proof objects and toolchain
installations are omitted.

The original ProveIt license is retained as `LICENSE.ProveIt`. Inherited
Rocq inputs retain their separate notices under `rocq/licenses/`. No blanket
relicensing of inherited material is asserted. The original logical
derivations and seed principle are attributed to their repository and upstream
authors; this packet contributes their checked reorganization and integration.
