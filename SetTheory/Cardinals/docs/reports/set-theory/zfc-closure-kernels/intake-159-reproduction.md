# Batch 159 / source 56: recover and replay the available salvage

The original incomplete ZIP remains recoverable from arrival commit `80e26b89e905bf3e5dfc322befdc1c6eaf25a109`, at `docs/incoming/zfc-state-reduction-research.zip`. Placement commit `901dd50056` preserves 321 available ancillary files and retires the ZIP from the incoming queue. Six main/build artifacts remain archive-only. All 327 delivered local payloads are complete; the intended package is incomplete because essential later members are absent.

The commands below require Python 3.10+ and Git. Keep assertions enabled: do not use `-O`. They run no proof compiler, dependency build or network job. Use a new scratch output outside the checkout; optional replays write results only in that recovered package. No checksum manifest is interpreted and no line endings are changed.

## Recovery only

Set the checkout path, then invoke the maintained helper. Its default map is `data/intake-159-placement.json` within the same report host.

```sh
zfc_repo=/path/to/ProveIt
zfc_host="$zfc_repo/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels"
python3 -B "$zfc_host/code/recover_159.py" \
  --repo "$zfc_repo" \
  --output /tmp/zfc-batch159-new
```

The helper reads the committed ZIP with `git show`, parses its complete local entries without relying on an absent central directory, compares all 321 placed ancillary files directly against their original payload bytes, and restores all 327 available members. Its `recovery.json` records `PARTIAL_DELIVERY_SALVAGED` and prints the exact package root:

```text
/tmp/zfc-batch159-new/zfc-state-reduction-research
```

This is recovery only: it executes no delivered verification code and does not recreate missing files. An alternative map may be selected explicitly with `--map /path/to/intake-159-placement.json`; the published default is sufficient for the maintained checkout.

## Prepare the optional review replays

The two maintained review wrappers determine the package root from their own location. Copy them into `review-logs/` under the recovered package using their original names:

```sh
zfc_package=/tmp/zfc-batch159-new/zfc-state-reduction-research
mkdir "$zfc_package/review-logs"
cp "$zfc_host/code/replay_159_partitions.py" "$zfc_package/review-logs/partial-journals.py"
cp "$zfc_host/code/replay_159_controls.py" "$zfc_package/review-logs/recovered-checks.py"
cd "$zfc_package"
```

The maintained helper names are publication names; the copies above preserve the scripts' tested location convention. These wrappers are review additions, not recovered manuscript files.

## Available finite controls and machine audit

```sh
python3 -B review-logs/recovered-checks.py
python3 -B work/state_reduction/audit_modified_source.py \
  --repo source/ProveIt \
  --source experiments/direct-negation255/source.json \
  --table experiments/direct-negation255/machine_255_oldlabels.tm \
  --output review-logs/machine255.json
```

The first wrapper checks the original 6,460 literal leaves against the supplied 203-node decoder, reconstructs the six recorded fold edits from 261 to 255 states, verifies exact renumbering of all 510 rows with start 0/halt 255, and samples the negation identity at 10,001 inputs. Its output is `review-logs/recovered-checks.json`. The identity has a separate ordinary algebraic proof; the sample is only a regression check.

The machine audit passed at intake: all 7,311 conditional affine cases; all 55 protected box rows; the exact 82,552-step whole-tape blank bootstrap; and 21,933 complete-frame literal trials over 11,257,202 binary steps, with all 510 rows covered including bootstrap. These are finite source/table/frame checks under the inherited box contracts. They do not prove every optimized source occurrence equivalent, provide the missing affine invariant checker, or establish a new kernel theorem. This 255-state artifact does not improve the maintained 252-state bound.

## Available partition journals only

```sh
python3 -B review-logs/partial-journals.py
```

The wrapper requires exactly 32 available result/journal pairs and writes `review-logs/partial-journals.json`. Intake replay checked 1,534,208 journal nodes and exactly **32,514,048 assignments** (32 × 1,008²), with zero remaining frontier and zero recorded survivors, in 44.844 seconds. Each domain assigns two incoming actions from the delivered 1,008-action grammar.

The covered deleted-state domains are exactly:

```text
68 72 78 79 81 122 125 127 143 149 151 152 153 154 161 166
167 176 177 179 180 188 192 193 212 215 235 240 243 245 250 252
```

The auditor independently checks assignment order, branch/prune partition weights, recorded counts and final frontier. It does **not** rerun each symbolic rejection outcome. The journal for state **82** is missing; states **89, 92 and 98** lack both result summaries and journals. Success on the available 32 does not verify the advertised complete 36-domain census or combined 46-domain family. The wrapper does not silently omit any additional recovered complete pair.

## Preserved full-verifier failure and other limits

The advertised entry point was attempted with its checksum-manifest step deliberately bypassed:

```sh
python3 -B verify.py --skip-manifest
```

It returned **exit 1** at `verify.py:59`, importing the missing `work/theory_audit/check_affine_certificate.py`. This command is an optional reproduction of that known failure, not a required successful stage. The entire `work/theory_audit/` directory is absent, including the advertised invariant checker, mutation controls and direct/shifted-negation generators. No wrapper substitutes implementations for those missing files. The supplied 8,384 invariant obligations, 1,433 enriched sites and 27 additional equation rows remain unreplayed claims.

The intake logs retain that failure alongside the separately passing checks. No complete intended-package recovery, full-suite PASS, new sub-252 machine, or PA consistency-equivalence completion follows from this salvage. The original user target remains equivalence provable in PA; weaker ZFC-formalizability commentary in the manuscript does not change that target.
