# Authorized source-only release

The README and SOURCE_PINS retain the historical CODE ONLY/HOLD checkpoint.
Both complete static reviews passed, and root explicitly released the exact
five README commands on 2026-10-24. The reviewed executable/proof/core bytes
and pins remained unchanged throughout this release.

The outside independent review is
`reviews/signed-pell-cap-nine-factor-source-static-peer.md`, SHA256
`7326e1b0b257e0d21af9f37b4f009ff50a0df433f59dca187eb85d47dd65e159`.
Root's complete preparation review is
`reviews/signed-pell-cap-nine-factor-source-preparation-root.md`, SHA256
`afa0b1a608c9d19d2a435a3ca08d922f9f7c75bf3e023764596ad224206bd8cc`.
SOURCE_PINS remains
`9c51aa8cd2f9a3ed3cb1e633a4098416aa09fdae9778fac80a040e5199fc7fc2`.

The following commands ran sequentially from the repository root; each exited
zero. Each full stdout file under verification/ is byte-identical to its
retained JSON receipt.

```sh
python -B Computability/DiophantineConsistency/research/signed-pell-cap-nine-factor-source/build.py --output /tmp/nine-factor-source-build.json
python -B Computability/DiophantineConsistency/research/signed-pell-cap-nine-factor-source/check.py --output /tmp/nine-factor-source-check.json
python -O -B Computability/DiophantineConsistency/research/signed-pell-cap-nine-factor-source/check.py --output /tmp/nine-factor-source-check-optimized.json
python -B Computability/DiophantineConsistency/research/signed-pell-cap-nine-factor-source/build.py --check --output /tmp/nine-factor-source-rebuild.json
python -O -B Computability/DiophantineConsistency/research/signed-pell-cap-nine-factor-source/build.py --check --output /tmp/nine-factor-source-rebuild-optimized.json
```

BUILD.json records materialization. VERIFY.json and VERIFY_OPTIMIZED.json
record the independent normal/optimized checks, including all46 actual
corruptions rejected in each mode. BUILD_VERIFY.json and
BUILD_VERIFY_OPTIMIZED.json record pure deterministic rebuilds; their five
generated hashes exactly match materialization. The five generated artifacts
have not changed after materialization.

The actual source retains all406 body coordinates/all341 body residuals and
has475 guarded coordinates/364 residuals/24 whole graphs. The complete
ordinary/native calibration, original-body witness maps and both fresh old
triples are authenticated. These dimensions describe the source input.
No optimizer, factorizer, projection, centering, quartic collection or Lean
command ran. No projected frontier is claimed. Root's independent replays and
integration records belong outside this author packet.
