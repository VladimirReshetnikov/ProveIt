# Reproduce batch 160

The [placement map](data/intake-160-placement.json) covers all 655 delivered
files. Run the portable helper from the repository root, with a new output
directory outside the checkout:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_160.py \
  --repo "$PWD" --output /tmp/zfc-batch160-recovered
```

It reads the three committed arrival ZIPs, checks safe regular member paths
and the full inventories, compares all 633 placed ancillary files directly
with their original payloads, then restores all original paths. It performs
no network access, proof build or verification-suite execution. The fresh
[recovery record](data/intake-160-recovery.json) reports all comparisons passing.
The 22 archive-only files include every delivered main/section/PDF/root README;
they are recovered too. Checksum manifests are preserved without interpretation.

Verification must use a separate copy of the recovered package, since these
scripts overwrite evidence. Use Python 3 with assertions enabled. The scripts
use the standard library; no dependency download or proof compiler is needed.

| Source | Recovered package | Command inside a separate copy | Fresh result |
| --- | --- | --- | --- |
| 57 | `57-prefix/prefix-shift-research` | `python3 -B verify_research.py --extended --output /tmp/zfc-prefix-replay-new` | All 12 jobs, 26.786 seconds |
| 58 | `58-carry/zfc-prefix250` | `python3 -B code/verify_all.py` | All requested stages, 12.137 seconds |
| 59 | `59-audit/zfc-prefix250-report` | `python3 -B code/verify.py` | All 9 jobs, 27.302 seconds |

These are observed outer runtimes, not performance guarantees. The root used
180 seconds for source57 and 120 seconds for each later package. Each run
completed with exit0. Source57 remains a252-state construction; source58/59
are the same250-state machine. No full checksum-manifest suite was run.

Source57's [record](data/intake-160-source57-replay-record.json) and
[summary](data/intake-160-source57-replay-summary.json) bind the commands.
Fresh phase, source rewrite, NIP, projected-GEN, baseline and regenerated MP0
certificate results and all twelve job logs have `data/intake-160-source57-`
prefixes. The supplied source57 search journals retain their completed/partial
status; the extended run does not rerun every research search.
The positive-transfer driver does not fail its process on a reported semantic
failure, so its [actual result](data/intake-160-source57-positive-transfer.json)
was inspected separately: `passed=true`, all17325 cases passed, no failures.
The regenerated MP0 rows and segment relation are also preserved under the
`data/intake-160-source57-mp-source-mapping-` prefix.

Source58's [record](data/intake-160-source58-replay.json),
[summary](data/intake-160-source58-fresh-reproduction.json),
[regeneration](data/intake-160-source58-fresh-regeneration-and-canonical-audit.json)
and [comparison](data/intake-160-source58-replay-comparison.json) distinguish
fresh checks from the delivered evidence. The fresh affine JSONL is preserved.
Differences from delivery are runtime fields and relocated source/table paths;
all substantive results agree.

Source59's [record](data/intake-160-source59-replay.json),
[nine-check summary](data/intake-160-source59-fresh-verification-summary.json)
and [comparison](data/intake-160-source59-replay-comparison.json) record:

- Exact reconstruction:250 working states,500 rows,6459 source nodes,6460 leaves.
- Four block, three macro and nine marking induction templates.
- All8391 guarded instructions; at least13 literal steps per case.
- All24 unchanged marking rows and all9 selectors.
- Full source-token consumption,342 oracle controls and full-width PC agreement.
- Dual sparse/dense585431-step blank startup,438 one-cells and210 spares.
- Four local retiming cases and584942 equal complete-tape cutpoints.
- 33564 literal instructions,14197744 transitions.
- 16200 literal macros,8359100 transitions.

The nine substantive JSONs agree byte-for-byte with delivery except three
timing values: `elapsed_seconds` in instructions, and `seconds` in the two
literal regressions. The summary itself additionally records fresh timestamps,
runtime and per-result identities. These checks support the ordinary proofs;
they are not Lean kernel checks or a finite experiment establishing nonhalting.

Frozen mathematical and symbolic reviewer records retain their original
absolute scratch paths and their then-source-only status. Their publication
copies are unchanged; root's subsequent successful runs are the evidence above.
Scratch numbers161/162 refer to sources58/59 of this single batch160.
