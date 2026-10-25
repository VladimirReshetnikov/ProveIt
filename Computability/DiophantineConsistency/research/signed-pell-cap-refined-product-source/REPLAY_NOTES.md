# Source-only release and retained results

The README records the historical static checkpoint. After both complete
static reviews passed, root explicitly authorized exactly its five commands,
sequentially. All five completed with exit status 0 on 2026-10-24. No algorithm,
core proof, boundary or pin changed between review and execution.

The independent static review is
`reviews/signed-pell-cap-refined-product-source-static-peer.md`, SHA256
`a988f129c46e1b68fabc5c54549c8db969936474778566e1b8048883b8cbf5b5`.
Root independently read the complete code/proof closure and authenticated
the 138 external files, five core files and nine closed dependencies before
release. The executing SOURCE_PINS SHA256 remained
`6071ae1afb38ee0ce6bbb644f647655409b470af1c76c4617b0a2adc98e85147`.

The commands below ran from `/home/codex/.codex/worktrees/62ff/Proofs`, in the
displayed order. Each stdout was retained whole in the corresponding
`verification/*.txt`; each output JSON was copied byte for byte into the
packet, then compared against that stdout with `cmp`.

```sh
python -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-source/build.py --output /tmp/refined-product-build.json
python -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-source/check.py --output /tmp/refined-product-check.json
python -O -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-source/check.py --output /tmp/refined-product-check-optimized.json
python -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-source/build.py --check --output /tmp/refined-product-rebuild.json
python -O -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-source/build.py --check --output /tmp/refined-product-rebuild-optimized.json
```

| Command | JSON record | Full stdout |
| --- | --- | --- |
| Materialize | `BUILD.json` | `verification/materialize.txt` |
| Normal checker | `VERIFY.json` | `verification/check-normal.txt` |
| Optimized checker | `VERIFY_OPTIMIZED.json` | `verification/check-optimized.txt` |
| Normal pure rebuild | `BUILD_VERIFY.json` | `verification/rebuild-normal.txt` |
| Optimized pure rebuild | `BUILD_VERIFY_OPTIMIZED.json` | `verification/rebuild-optimized.txt` |

The source has 406 coordinates and 341 rows. Its guarded integer tuple has
478 coordinates, 365 rows and 25 whole Legendre graphs. These are literal
source namespace sizes. All 399 original body coordinates and 334 original
body rows remain fixed. The maps preserve 468 old coordinates and 357 old
rows, remove exactly ten scalar graphs and their 30 private auxiliaries, and
adjoin exactly seven product definitions and one strict-product graph.

Both checker modes passed the complete row/coordinate/guard/privacy maps,
all 18 actual request memberships and unsquared lowerings, all 15 primary
norms, all five shared moduli, all 54 bounded ports, eleven source ideal
identities, the full helper involution and universal signed identities.
Each rejected all 35 actual artifact corruptions. The two deterministic
rebuilds reproduced every byte of all five generated artifacts. The complete
receipts retain the individual controls and bindings.

The five generated JSON artifacts were fixed immediately after materialization.
The extra release/results files do not alter them. `RESULTS.json` records
their hashes, maps, source sizes and all five receipt hashes.

This release ran no optimizer, factorizer, projection, centering or quartic
collection. It makes no projected frontier claim. The ordinary calibration is
the complete sealed refined-product theorem followed by the complete sealed
refined-source calibration, with reconstruction on the original unnormalized
body as specified in the immutable generated `CALIBRATION_BINDING.json`.

Root received the immutable artifacts and author receipts before sealing and
is performing four fresh independent checker/rebuild replays. Final closure
will record that independent result separately without changing core or data.

Final root result: all four fresh independent source-only checker/rebuild
commands completed with exit status 0. Each complete JSON receipt and full
stdout matched the corresponding retained author record byte for byte, in
both Python modes. Both independent checker runs rejected all 35 controls.
`ROOT_REPLAY.json` records the exact four matched hashes; root retains its
eight replay records separately. Root authorized final author inventory
closure without further execution. Core and all five generated artifacts
remain unchanged.
