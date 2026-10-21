# Retained legacy interfaces after phase five

The completed check passes: 15 extra modules were freshly compiled against 184 hash-bound primary providers, and all five typed clients pass with standard axioms only and zero audit warnings. The two project linter warnings in `L2Control219` are identical to phase four. The [live review](live-review.json) rehashed the complete 199-module union after the audit; the [result](result.json) retains the actual compiler records.

The [pre-execution source peer](controls/peer-v2.json) and metadata controls retain the earlier binding defects and their corrected successor. After compilation, 14 byte-identical terminal legacy objects shared storage with their phase-four copies; [storage receipt](storage-deduplication.json) verifies every path, regular-file type and hash was preserved. This does not change their fresh compilation provenance.

The retained runner refreshes fifteen legacy modules against the completed 184-module phase-five primary basis. Its private 199-module union uses read-only symlinks for all primary providers and fresh regular outputs for the fifteen extras; it never overwrites a basis object. No completed legacy result is claimed until the run, typed audit and live reviewer pass.

The extras are the previous fourteen legacy modules plus `RMOffsetBisim`, which phase five removes from the primary import closure while retaining its public API. `LegacyAudit.lean` has five typed clients: four arbitrary-state root `iter_iff` interfaces and the arbitrary-program/register-file offset checker theorem. One audit module compiles these five clients and prints five standard-axiom reports.

Execution requires the exact primary PASS result and matching independent live review:

```sh
python3 -B build.py --basis /tmp/k215-proof-phase5/lean-run1 \
  --basis-review /path/to/phase5/live-review.json --out /tmp/k215-phase5-legacy/run1
python3 -B review.py --run /tmp/k215-phase5-legacy/run1 \
  --basis /tmp/k215-proof-phase5/lean-run1 --output /tmp/k215-phase5-legacy/live-review.json
python3 -B publish.py --run /tmp/k215-phase5-legacy/run1 \
  --basis /tmp/k215-proof-phase5/lean-run1 --primary-packet /path/to/phase5/lean \
  --out /tmp/k215-phase5-legacy/packet
```

The compiler uses the existing shared process-group supervisor and lock, one worker, 12GiB and 120seconds per invocation. Every source/import/provider/object/log/toolchain is bound and rechecked after the audit. Only the 15 extras are freshly compiled; this is not a fresh compilation of all 199 modules and adds no internal-PA result.

The compact packet stores fresh source snapshots/raw logs, the five-client source/report, complete union/basis ledgers, toolchain identities, before map, preparation and live-review evidence. It excludes compiled objects and does not duplicate the primary archive. `primary-reference.json` hashes the exact separate primary archive/index/summary/live-review. `review_saved.py --output /new/receipt.json` checks archived consistency only; optional `--primary-packet /path/to/phase5/lean` additionally checks those external file hashes and receipt continuity. It does not re-run the primary archive's own validator or claim to inspect live objects.
