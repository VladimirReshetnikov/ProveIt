# Historical checkpoint, release and complete replay closure

The immutable core README/PROOF/BOUNDARY describe the historical CODE ONLY/HOLD
checkpoint. Both complete static reviews subsequently approved the final
builder `32d8298fac4c5fd5f8b152c242dcc5f06b7dd0d9502feebf5b3a98e78c48886c`
and checker `6c7f09ba6b3c94907b22e617a9d7a81f8f2e9b08db4716a79cccabf13f4ac881`.
All seven vendor files are byte-identical to their accepted parent. The final
pin SHA256 throughout execution was
`2cd12f3f97a56c51e2c946cd601e8345a2ea2ed3a6e0da9f639aac5c4b976959`.
All 458 external, seven vendor and five core pins and all 18 complete closed
inventories (including the grouping packet's typed hash/byte records) were
authenticated before root released any execution.

The outside independent static record is
`reviews/signed-pell-cap-refined-product-projections-static-peer.md`, SHA256
`1abef8edc28982bcf96c61cad30e8dbbc88de5dcc63b6bdcb8d31842710fa6a9`.
The full root preparation record is
`reviews/signed-pell-cap-refined-product-projections-preparation-root.md`, SHA256
`fff4cb0eb4e17840d882125dbf63ecb2664c71831239e2698cc02b5add233ba4`.

Root explicitly released exactly the following five commands on 2026-10-24,
in this order, from `/home/codex/.codex/worktrees/62ff/Proofs`. Every command
completed with exit status 0. No core, source, proof, vendor or generated
artifact changed after its materialization. The original cosmetic checker
EOF spacing was preserved to retain its reviewed byte identity.

```sh
python -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-projections/build.py --output /tmp/refined-product-projection-build.json
python -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-projections/check.py --output /tmp/refined-product-projection-check.json
python -O -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-projections/check.py --output /tmp/refined-product-projection-check-optimized.json
python -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-projections/build.py --check --output /tmp/refined-product-projection-rebuild.json
python -O -B Computability/DiophantineConsistency/research/signed-pell-cap-refined-product-projections/build.py --check --output /tmp/refined-product-projection-rebuild-optimized.json
```

| Command | Complete JSON | Complete stdout |
| --- | --- | --- |
| Materialize | `BUILD.json` | `verification/materialize.txt` |
| Normal checker | `VERIFY.json` | `verification/check-normal.txt` |
| Optimized checker | `VERIFY_OPTIMIZED.json` | `verification/check-optimized.txt` |
| Normal pure rebuild | `BUILD_VERIFY.json` | `verification/rebuild-normal.txt` |
| Optimized pure rebuild | `BUILD_VERIFY_OPTIMIZED.json` | `verification/rebuild-optimized.txt` |

Every retained stdout is byte-identical to its corresponding retained JSON.
Both checker modes passed all 46 actual corruption controls, full source and
guard/product/frame/call bindings, the complete Horn/private and monic/free
maps, both whole quartics, centering history, all five complete alternatives
and endpoint calibration. Both pure rebuilds compared every generated file
and the entire generated inventory byte for byte. `RESULTS.md` reports the
actual measurements; `RESULTS.json` retains the exact receipt hashes and maps.

Root authorized four fresh independent read-only replays against the immutable
data while the remaining sequential author commands finished. They were the
normal/optimized checker and normal/optimized pure rebuild, with unique
`/tmp/root-refined-product-projection-{check,build}-{normal,optimized}.{json,txt}`
paths. All four exited 0. All four complete JSON records and all four complete
stdout records were compared byte for byte against the matching author files,
with no difference. Root retains these records outside the author packet and
authorized final closed author inventory without further unchanged execution.

The release contains no alternate optimizer policy, source mutation, new
ordinary semantic claim, Lean run or canonical-page modification. All core,
generated data and frozen parents remain immutable. Final metadata and the
closed author manifest are separate from the core and emitted artifacts.
