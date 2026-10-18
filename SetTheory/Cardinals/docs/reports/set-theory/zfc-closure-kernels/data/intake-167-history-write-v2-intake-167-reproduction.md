# Reproducing source 71 and batch 167

The original archive remains recoverable from arrival `d91a27b462cbf7fdc6537739775fd192b06fb769` at `docs/incoming/zfc244-loop-rotation-20261018.zip`, Git blob `663925a900262cb01eaf112b824dd957b4d497ba`, SHA256 `2609ff9ff0c6c0a2ba7619bcfad7e7480f3d9052dd32c161149e6a721c25a54a`. Placement `5513e77ff1` preserves 1,007 files unchanged; 37 manuscript/delivery files remain archive-only. The mapping restores all 1,044 original nested names, including files placed under flattened names and `.log.txt` extensions.

From a checkout containing the arrival and placement commits, choose a new external output directory:

```bash
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_167.py \
  --repo "$PWD" \
  --output /tmp/intake167-recovered
```

The helper refuses an existing output directory, retrieves the committed ZIP, validates safe member names, extracts the original payload and compares every placed ancillary file against the corresponding archive bytes. It prints the package root `/tmp/intake167-recovered/zfc244-loop-rotation-20261018`. It performs no delivery checksum-manifest verification or proof execution. Root's recorded recovery passed 1,044 recovered files and 1,007 placed pairs; see [recovery evidence](data/intake-167-recovery.json).

## Primary substantive replay

Use Python 3.12 with assertions enabled (`-B`, never `-O`). The included algorithms use the standard library. No network, package install, C++ compiler, Lean, Rocq or TeX is required. Run only on the recovered disposable copy or another complete new copy. Supplied routines write their output artifacts; retain the original placed source files unchanged.

The top-level `code/verify_all.py` also invokes delivery checksum manifests. The actual root replay bypassed that wrapper and called the seven substantive jobs directly. Preserve the semantic table/source identity assertions inside those programs. The following commands reproduce the same seven jobs with portable paths:

```bash
QT_PACKAGE=/tmp/intake167-recovered/zfc244-loop-rotation-20261018
QT_OUTPUT=/tmp/intake167-primary-replay
mkdir "$QT_OUTPUT"
python3 -B "$QT_PACKAGE/code/make_qt244.py" \
  --reference "$QT_PACKAGE/reference/baseline245" --output "$QT_OUTPUT/built"
python3 -B "$QT_PACKAGE/code/check_qt_rotation.py" \
  --reference "$QT_PACKAGE/reference/baseline245" --output "$QT_OUTPUT/source"
python3 -B "$QT_PACKAGE/code/check_table_boot.py" \
  --table "$QT_OUTPUT/built/machine_old.tm" \
  --baseline "$QT_PACKAGE/reference/baseline245/certificate/machine_old.tm" \
  --output "$QT_OUTPUT/blank"
python3 -B "$QT_PACKAGE/code/check_frames.py" \
  --machine "$QT_OUTPUT/built" --output "$QT_OUTPUT/frames.json"
python3 -B "$QT_PACKAGE/code/check_runtime.py" \
  --reference "$QT_PACKAGE/reference/baseline245" --candidate "$QT_OUTPUT/built"
python3 -B "$QT_PACKAGE/code/check_qt244_literal.py" --candidate "$QT_OUTPUT/built"
python3 -B "$QT_PACKAGE/code/check_runtime.py" \
  --reference "$QT_PACKAGE/reference/baseline245" --candidate "$QT_OUTPUT/built" --expanded
```

The recorded root runner applies a 600-second timeout to each child process group and retains stdout/stderr. It checks exact reconstruction of `machine.tm`, `machine_old.tm`, both site lists, `renumbering.json` and `boot.json`; the right-associated generated source lists must equal the actual candidate. All seven jobs pass. Expanded replay took 518.026 seconds in that environment; runtime is not guaranteed on other systems. A timeout is an unfinished check, not a failed mathematical theorem.

Expected expanded fields are `complete=true`, `counts.cases=8390`, `counts.symbolic_rules=2312438`, `positive_progress_checked=true`, `literal_rows_covered=487` and `unused_rows=[[27,1]]`. The all-primary-registers and arbitrary-nonempty-finite-spare flags must be true. Canonical SHA256 is `91ff0ff2dfe9155548d21405615934b46784c5e3cb850bbf056682d02b203790`; inherited table SHA256 is `0160caaf5d6db52eb7eb97a76cb04db4b424eb2bc0d58617818a6c7c6a1fe776`. The unused row is intentionally retained in the total table. A blanket all-rows-used assertion would reject the correct delivered scope.

The frame result checks 6,459 source leaves, 8,390 guarded cases and 8,389 nonhalting successor normalizations. The sparse/dense blank result is 407,931 transitions to the complete common root frame. Literal regression checks 8,390 finite fixtures and 6,470,964 transitions. These finite fixtures do not replace expanded induction. The [actual root runner](code/intake-167-root-primary-replay.py), [execution](data/intake-167-primary-execution.json), [terminal result](data/intake-167-primary-verification.json), raw child logs and [independent metadata review](data/intake-167-primary-review.json) preserve the executed paths and checks. Historical absolute paths in these records are evidence, not required replay locations.

The unused `code/check_whole_frame_candidate.py` has an indentation defect at line 22 and must not be substituted for the valid expanded command. The original defect remains preserved. The unchanged baseline245 suite was not rerun: 292 substantive inherited payload files were byte-compared to the earlier reviewed package. This reuse does not count as fresh ancestor execution.

## Auxiliary results and research regeneration

The [auxiliary plan](data/intake-167-auxiliary-replay-plan.json) lists exact entrypoint hashes, working directories, arguments, dependencies, outputs and suggested process-group caps for 16 direct checks/family regenerations plus two optional selected seed regenerations. The readable [command table](intake-167-auxiliary-replay-plan.md) accompanies it. Those proposed caps are safety limits, not expected runtimes. Root has since completed all 16 direct checks/family regenerations, counting the separate logical check once; the two optional selected seeds remain unrun. See the [actual auxiliary record](data/intake-167-auxiliary-execution.json) and [independent output review](data/intake-167-auxiliary-review.json). All15 later jobs finish in less than one second each, and their exact regenerated outputs match delivery where counterparts exist.

The separately completed root logical check is:

```bash
cd "$QT_PACKAGE/research/formalisms"
python3 -B formalism_verify.py
```

It checks the two condensed-detachment certificates and three finite propositional matrices. Its PASS is not a full CP/GIC countermodel or a premise needed by the QT machine. The other formalisms regenerate symbolic source contracts and matched public-backend controls; grammar verification replays retained witnesses without searching. `seed_variants.py` catches some failures into `summary.json`, so exit zero alone is insufficient: require `SEED_CREATED` for the selected mask and independently inspect the resulting grammar audit.

The split-bundle backend is the exact 31,486-byte public `TMBuilder.py`, SHA256 `03d3a636404e1bcdeceafd98b9478b7a367ab334f3ab9f8a00df1d5c03fdf517`, already preserved in the repository and several prior source intakes. The [reuse record](data/intake-167-backend-reuse.json) binds current copies and original Git history. Each of its 192 finite helper cases has a 5,000,000-source-step cap. Its generated 281/281/290/288-state controls have no new complete runtime or initialization proof.

Optional heuristic grammar campaigns and condensed-detachment searches require C++17 and elapsed-time seeds. They were not rerun for this intake; delivered outcomes are retained with their finite scope. No minimality or lower bound is inferred. The large family regenerators and optional seeds are also distinct from the primary 244-machine proof. Preserve all outputs on a new copy rather than overwriting delivered certificates.

## Separate combined243 evidence

The combined243 candidate was developed after intake by applying the compensated fold to the rotated table and checking its complete local hypotheses. It is absent from the incoming ZIP. The linked [ordinary comparison](data/intake-167-ordinary-review.json) and [quick root record](data/intake-167-combined243-quick-verification.json) are subsequent evidence. The quick record has its own adapted sources, 407,967-step startup and 6,473,394-step finite regression; it is not reproduced by the seven unmodified QT244 commands above. Its separate [expanded record](data/intake-167-combined243-expanded-verification.json) now passes 8,390 cases/2,314,868 rules in 509.285 seconds. Its [relative Lean comparison](../../../../../../Computability/BusyBeaver/Research/ZFC/combined243_simulation.md) proves 243↔QT244 halting; it is not a complete consistency endpoint. These results have their own sources and records and are not reproduced by the unmodified QT commands.

The host uses the reconciliation-note route: delivered article/TeX/PDF bytes are preserved, so no merged host PDF is built. The collection's catalogue manifest is updated and built separately. This intake performs no internal PA calibration, asserts no absolute consistency, and treats the current compensated244 external Lean endpoint as a distinct checked artifact.
