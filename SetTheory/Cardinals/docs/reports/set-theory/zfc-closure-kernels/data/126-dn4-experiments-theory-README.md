# Native ZFC source experiments

This directory is a portable companion to the construction report. It supplies the ordinary double-negation calibration, exact source reconstruction, selected alternative source programs, literal compiler-cost probes, and pinned prior art. **This theory branch does not claim a machine with fewer than 225 working states.** The DN4 binary-runtime and blank-startup proofs belong to the parent construction packet.

The files under `ksp/`, `ks_dne/`, `ks_clavius/`, and `canonical_ve/` are larger experimental tables. Their internal decoder contracts and working-state counts were checked, but their full runtime and startup were not promoted. The selector probe covers 32 representative primitive cases. `selected_results_manifest.json` records these limits separately from every reported metric.

## Verify the archived selection

Python 3.10 or later and its standard library suffice. Run with assertions enabled. From this directory:

```sh
python scripts/verify_selected_results.py
python scripts/reconstruct_full_dn.py --baseline inputs/sites225.json --recipe dn4/recipe4.json --builder vendor/build_zfc235.py --output rebuilt_dn4.json
python scripts/verify_full_dn_semantics.py --baseline inputs/sites225.json --source rebuilt_dn4.json --recipe dn4/recipe4.json --builder vendor/build_zfc235.py --dag vendor/Dag230.v
```

The first command checks file hashes, all selected source metrics, complete two-symbol table shape and literal state counts for the K/S/Peirce probes, and exact DN4 reconstruction. It does not replace an unbounded binary-runtime proof. The last command checks the source and symbolic-formula obligations explained in `tex/full_dn_proof.tex`.

## Rerun source discovery

All input and output paths are supplied explicitly. The supported experiment names are `full-dn`, `selectors`, `logical-rows`, `swap-ab`, `ksp`, `ksp-parameters`, `ks-dne`, `ks-dne-parameters`, `ks-clavius`, `ks-clavius-parameters`, and `canonical-ve`.

```sh
python scripts/run_source_experiments.py logical-rows --baseline inputs/sites225.json --builder vendor/build_zfc235.py --dag vendor/Dag230.v --dn4 dn4/sites_full_dn4.json --output regenerated
```

Replace `logical-rows` by another experiment name as needed. The `full-dn` search does not require `--dn4`. The K/S/Peirce parser minimizes new compound occurrences followed by depth; it is a discovery heuristic for a shared source DAG, not a globally optimal compiler. The launcher fixes Python's hash seed for new runs. The archived selected trees record the exact choices used in the literal compiler probes, including equal-cost parsing choices.

The earlier scratch-only decoder compiler is not required to inspect or verify these archived counts. Reconstructing its full search procedure requires the decoder-search tools retained in the parent packet; no isolated source-count script supplies a binary runtime certificate.

## Provenance and proof status

`vendor/build_zfc235.py`, `vendor/Dag230.v`, and `inputs/sites225.json` are pinned by SHA-256 in the checker and manifest. Source 116's repository files are retained under `prior_art/`, with exact repository commit and original paths recorded in the manifest. Membership-defined equality is prior work. The larger equality-reduction and NBG alternatives are discussed as theory routes, with no speculative state count.
