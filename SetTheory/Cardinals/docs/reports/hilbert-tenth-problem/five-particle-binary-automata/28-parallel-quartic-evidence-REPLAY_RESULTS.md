# External replay results

Status: PASS. All 14 commands succeeded from the external working directory.
All 75 source file/directory entries retained identical bytes, modes, and nanosecond mtimes after each command and at completion.
Normal and optimized results agree. The polynomial and SOS files are byte-identical to the source artifacts. Prior mathematical counts are unchanged.

Source manifest SHA-256: 9f369b0a250b773c33f73213ec2e77e7c047118e9538e16c33cd84dfc625a31b
Overall wall time: 440.675102744 seconds

The frozen source is parallel-diophantine-certificate-research-20261003; the immutable backup is parallel-diophantine-certificate-research-20261003-v1. Source lineage is recorded in its PROVENANCE.json and lineage/v1-MANIFEST.json.

## Exact measured command wall times

| Script | Mode | Wall seconds |
|---|---|---:|
| test_certificate.py | normal | 108.052259970 |
| test_certificate.py | optimized | 110.385276993 |
| test_supplement.py | normal | 83.917122879 |
| test_supplement.py | optimized | 85.874118841 |
| test_multisource.py | normal | 8.386107973 |
| test_multisource.py | optimized | 8.607330571 |
| audit_emitter.py | normal | 12.056539629 |
| audit_emitter.py | optimized | 13.333078243 |
| test_example_validation.py | normal | 3.137724626 |
| test_example_validation.py | optimized | 2.608527186 |
| verify_example.py | normal | 1.927107751 |
| verify_example.py | optimized | 2.063021626 |
| verify_bundle.py | normal | 0.055303618 |
| verify_bundle.py | optimized | 0.134038691 |

Times are measured with time.perf_counter around the subprocess; they are observed replay durations, not performance guarantees.

## Replay commands

From the sibling replay directory:

    python -B replay.py --source-dir ../parallel-diophantine-certificate-research-20261003 --output-dir .

The exact individual commands (with directory placeholders) were:

    python -B <source>/test_certificate.py --output-dir <replay>/normal
    python -B -O <source>/test_certificate.py --output-dir <replay>/optimized
    python -B <source>/test_supplement.py --output-dir <replay>/normal
    python -B -O <source>/test_supplement.py --output-dir <replay>/optimized
    python -B <source>/test_multisource.py --output-dir <replay>/normal
    python -B -O <source>/test_multisource.py --output-dir <replay>/optimized
    python -B <source>/audit_emitter.py --output-dir <replay>/normal
    python -B -O <source>/audit_emitter.py --output-dir <replay>/optimized
    python -B <source>/test_example_validation.py --output-dir <replay>/normal
    python -B -O <source>/test_example_validation.py --output-dir <replay>/optimized
    python -B <source>/verify_example.py
    python -B -O <source>/verify_example.py
    python -B <source>/verify_bundle.py
    python -B -O <source>/verify_bundle.py

## Evidence

- replay-receipt.json: complete outcomes, exact unrounded wall durations, command strings and source snapshot digest
- source-before.json and source-after.json: full relative-path byte/mode/mtime snapshots
- normal/ and optimized/: fresh receipts and logs; each mode has independent artifact outputs
- output-routing-audit.md: four-runner edits reproduce originals when plumbing changes are reversed
- verifier-binding-audit.md and verifier-audit/: 37 bundled and 31 independent malformed-input rejections

Standalone verifier limitation: this is algebraic/metadata validation of the supplied artifacts; source/CA semantics depend on the audited compiler and manifest pins. Ledger contents and variable-name semantics are not independently reconstructed.

No source writes occurred during replay. The source manifest remains sealed; this external results file does not alter it.
