# Integration into ProveIt

## Baseline and file layout

The reviewed baseline is `3a90fb34146c915328ab8eac6250cc2514f74ed0` in `VladimirReshetnikov/ProveIt`.

`integration.patch` adds the contents of `repo_overlay/` at repository-relative paths. It contains:

- Nine Python modules under `Topology/UnknotRecognition/fast/fastunknot/`.
- Five new test files under the corresponding `tests/` directory.
- `support_research/` scripts, source corpus, exact evidence, and retained measurements.

It changes no existing production file. The independently authored article is outside the code overlay. Keep its complete directory together when choosing a report destination: it uses companion TeX files and the generated figure PDFs. An eventual synthesis-section integration should preserve the theorem hypotheses, attribution, and negative benchmark findings.

## Review and apply

Use Python 3.10 or newer. From a clean ProveIt checkout at the pinned revision, with `PACKAGE` set to the unpacked package directory:

```bash
git apply --check "$PACKAGE/integration.patch"
git apply "$PACKAGE/integration.patch"
cd Topology/UnknotRecognition/fast
python3 support_research/run_tests.py --output support_research/results/local_regression.json
python3 support_research/audit_extra.py
python3 support_research/audit_focus.py
python3 support_research/example.py
python3 support_research/replay_evidence.py --output support_research/results/local_evidence_replay.json
```

Do not also copy the overlay after applying the patch; they are alternative ways to install the same additions. If integrating at a later revision, review any filename conflicts and rerun the focused validation. The attached reference snapshot is for reproduction, not for overwriting a newer checkout.

## Public interfaces

```python
from fastunknot.normal_support import compile_normal_support
from fastunknot.normal_support_verify import verify_normal_support
from fastunknot.normal_support_peeling import peel_normal_support_ray
from fastunknot.normal_support_peeling_verify import verify_normal_support_ray
from fastunknot.normal_packed_components import normal_packed_component_census
from fastunknot.normal_packed_verify import verify_normal_packed_certificate
from fastunknot.normal_ray_blocks import normal_ray_block_disk_count
from fastunknot.normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate
from fastunknot.normal_support_diagram import (
    certify_diagram_ray_disks, verify_diagram_ray_disk_certificate,
)
```

The prepared-input forms `compile_support`, `verify_support`, `peel_support_ray`, and `verify_support_ray` allow callers that already own validated geometry to avoid duplicate public-wrapper setup. The packed census accepts `encoding='packed'` or `encoding='vector'`, a reusable `support_certificate`, and an existing independently checked orbit trace through `orbit_certificate`.

The ray count first tries a unit transcript on each conservative raw-incidence block. If it fails, the certified general rank compiler decides whether the block is a ray. Higher-dimensional blocks use the maintained complete disc-count kernel under a shared orbit-cycle allowance. Exhaustion is inconclusive.

## Integration policy supported by current evidence

Keep the general observer and ray dispatcher explicit until an adaptive preflight policy is designed and measured. The large Fibonacci ray improvement is real for this stage, but the old maintained decoder and primitive-core shortcuts remain cheaper on several controls. No default-recognizer change is part of this patch.

The immediate development targets are partial unit elimination with a certified residual kernel, one shared geometry pass across blocks, a bounded-overhead observer dispatcher, and executable source-bound compressed cuts. The long-term theorem must additionally control candidate coverage, all failed branches and resets, marked-state size, transition cost, and complete negative verdicts.

## Optional oracle and timing commands

```bash
python3 support_research/audit.py --regina --output support_research/results/local_audit.json
python3 support_research/benchmark.py --diagrams 1,4,8,16,32 --output support_research/results/local_benchmark.json
```

The benchmark creates fresh local query state and includes one external replay in every public-query timer. New ray generation includes its internal replay; source-bound wrapper generation includes two. Run it serially on an otherwise quiet process. Raw times, A/A controls, paired ratios, explicit exclusions, and before/after source hashes are retained. The results should be compared as a complete protocol, not as isolated best timings.
