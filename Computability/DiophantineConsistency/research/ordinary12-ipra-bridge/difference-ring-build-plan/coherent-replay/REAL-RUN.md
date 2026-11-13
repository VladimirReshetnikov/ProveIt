# Proposed 70-source coexistence pair (not launched)

This concrete command is prepared for review. Do not run it until the exact
freezer, wrapper/coordinator and source/provider evidence receive separate
independent review, a fresh tracked-source audit passes, current free space is
checked, and the coordinating agent explicitly starts the run. The endpoint
checks provider/ordinary-source coexistence and three axiom reports; it does
not prove the desired graph transport, integrality, or an iPRA theorem.

Pins at preparation:

- Snapshot `/tmp/ipra-ordinary12-coexistence-source-03/manifest.json`:
  `9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded`.
  Its point-in-time audit SHA is
  `62fe3d1f2fee807ba3a81a32b8f8b4c6e918635e2a64fbd028596533dbcd9631`.
- Foundation receipt: `7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6`;
  its input manifest: `491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d`.
  The independent provider verifier exited 0, receipt SHA
  `60b8bcf556c275a33cbd133f1729fef439a2eaf4c3377d53e4ddbcafb9632a9e`.
  The original Foundation wrapper's outer exit was not captured; its receipt
  records inner Lake exit 0. Do not claim an observed outer exit.
- `paired.py`: `ab9a2787e4fb99f9c201280e1219e48a2bf6f7c8a2e8f78049743b3dce282ebb`;
  `monitor.py`: `bcb54868a78911f470e1ab833255b67e8f26d82fc7133eb0ddc5e663ef4770f8`;
  `path_guard.py`: `9af0852abe419dee3fa83a57aa8fbdb3584285c8c40a229c9ef041f610375173`.
- Guarded builder `rebuild.py`:
  `8170bd401b1821666fffc2a55f8dd908e473d32c71797661a5acd85a32d0dc56`;
  comparator `compare.py`:
  `530def48c58dc38ce8a293a5c9912762b2ad101e63faf7cb0763f71a7ac9a3a5`.

Immediately before any launch, verify all pins, independently audited review
receipts and actual verifier exits; re-audit all tracked sources using a new
output path and require exit 0, no drift, and a currently valid provider. The
proposed pair output path must not exist. Ensure Python optimization is off;
the wrappers reject a nonempty `PYTHONOPTIMIZE`, and the monitor removes it
from the builder environment. Direct optimized invocation of the unchanged
historical builder is unsafe.

```sh
python3 Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/monitor/paired.py \
  --output /tmp/ipra-ordinary12-coexistence-pair-01 \
  --snapshot /tmp/ipra-ordinary12-coexistence-source-03 \
  --snapshot-sha256 9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded \
  --provider-receipt /tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json \
  --provider-sha256 7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6 \
  --foundation-input Computability/DiophantineConsistency/reviews/foundation-provider-recovery/input-manifest.json \
  --expected-axiom-reports 3 \
  --reserve-bytes 4294967296 --budget-bytes 536870912 --interval 1 --grace 2
```

The reserve and per-sibling logical-output budget are **sampled thresholds**,
not enforced quotas or guarantees of continuous host free space. Monitor the
actual process and preserve complete outer stdout/exit, sibling states,
compiler logs, comparison and any interruption. Check live descendants before
any retry and never reuse partial sibling outputs. The builder's stated
package-transitive and dynamic dependency limits remain in force. Any result
must receive an independent artifact audit and cannot be broadened beyond the
exact snapshot and endpoint.
