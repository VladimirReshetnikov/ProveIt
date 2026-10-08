# Integration into ProveIt

The change set targets exactly:

```text
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit:     2b93767bd3cf7ea7c1995acd66f50c72858a30c5
Subtree:    Topology/UnknotRecognition
```

The archive contains a source snapshot for independent review and execution.
The patch records changes at their real repository-relative paths. It adds the
research article, data and proofs as well as implementation files. Existing
unmodified source and historical oracle dependencies are included in the
snapshot but are not redundantly added by the patch.

## Apply the complete change set

In a clean review checkout of the pinned revision, with the archive extracted
elsewhere, use its absolute patch path:

```sh
git switch -c research/native-orbits-20261008 2b93767bd3cf7ea7c1995acd66f50c72858a30c5
git apply --check /path/to/extracted/unknot_native_orbits_20261008/integration.patch
git apply /path/to/extracted/unknot_native_orbits_20261008/integration.patch
git diff --stat
```

`git apply` leaves new files untracked and edits unstaged for review. The patch
does not commit or publish anything. `CHANGES.json` lists the original and final
hash of every affected path, including new files. On a later branch revision,
review intervening changes and adapt the patch as needed; the experiment
baseline is the pinned revision above.

The smaller `implementation.patch` contains code, tests, the frozen corpus and
relevant module documentation. It is a review subset of the complete patch,
not a second sequential integration step. Raw result JSON and article assets
remain in the complete patch and snapshot.

## Validate after integration

```sh
cd Topology/UnknotRecognition/fast
python3 -B -m unittest discover -s tests -v
python3 -B normal_orbit_research/replay_saved_examples.py
```

The same commands were run on the isolated delivered snapshot. For the full
native audit and three benchmark commands, use the research README. Build the
PDF with `make` in `research/20261008_native_orbits/article/`; prebuilt figures
and tables are included.

## Suggested review order

1. `interval_orbit_verify.py` and the six local proof rules in the article.
2. `interval_orbits.py`, its scheduler and finite-oracle tests.
3. The unchanged normal extractor, then `normal_components.py`, ambient-input
   assumptions, boundary parity certificate and independent native audit.
4. `interval_incidence.py`, the coning identity and exact output contract.
5. The seed-search diff, first-firing hypothesis, unary fallback, deterministic
   derivation order and proper-closure pruning.
6. The independent worker repair and its pre-existing failing test.
7. Raw data, source hashes, controls, censored results and article claim ledger.

The native topology API takes a supplied vector and triangulation. Its positive
disk certificate does not replace the missing knot-exterior provenance step,
surface search or attachment-aware cutting. It is deliberately not wired into
PD-level recognition as an unconditional verdict. The existing opt-in
two-meridian stage retains its default dispatch and positive certificate schema.

Keep the standalone article under `research/20261008_native_orbits/` during
review. Its accepted results can subsequently be integrated into the maintained
synthesis without replacing or losing that manuscript's earlier material.
