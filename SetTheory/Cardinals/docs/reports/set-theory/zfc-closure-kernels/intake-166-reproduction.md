# Batch 166 recovery and reproduction

Source70 came from `248bc0593651331065ae558802a914110562d20a:docs/incoming/zfc244-compensated-routing-20261018.zip`. Placement `6619bd0002a0771284cfda26d0e734f76cffaaa4` preserves 170 ancillary files, with 21 archive-only originals. The [map](data/intake-166-placement.json) records all 191 exact nested names, including `.log` files placed as `.log.txt`; flattened collection names are not executable package layout. Delivered source and data stay unchanged. No checksum-manifest audit or line-ending normalization is part of this procedure.

From the repository root, recover to a **new external directory**:

```sh
uv run --no-project python -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_166.py \
  --repo "$PWD" --output /tmp/zfc-intake166-recovered
```

The helper uses `git show` on the exact arrival, restores all191 members, compares all170 placed pairs and prints the package root `/tmp/zfc-intake166-recovered/zfc244-compensated-routing-20261018`. It runs no verification suite, compiler or build. The [actual root recovery](data/intake-166-recovery.json) passes. `py -B` or the checked Linux `python3 -B` can replace `uv run --no-project python -B` where appropriate.

Make a separate working copy before any suite, because several regenerate their own evidence:

```sh
uv run --no-project python -c 'import shutil; shutil.copytree("/tmp/zfc-intake166-recovered/zfc244-compensated-routing-20261018", "/tmp/zfc-intake166-work")'
uv run --no-project python -c 'from pathlib import Path; Path("/tmp/zfc-intake166-work/SHA256SUMS").unlink(missing_ok=True)'
cd /tmp/zfc-intake166-work
uv run --no-project python -B verify.py --output /tmp/zfc-intake166-portable.json
```

Removing only that delivery manifest on the copy omits the optional manifest loop; every supplied Python source and all semantic table/input identity checks remain intact. Assertions must remain enabled. Python3.10+ standard library suffices. The portable replay reconstructs all three variants, checks both local proofs and the principal startup, binds the archived full certificate, executes **one** symbolic smoke case, regenerates the equational backend and checks its artificial contradiction demo. It does not claim a fresh full8,391-case run. Root's [portable record](data/intake-166-portable-execution.json) passes in1.367seconds; the [separate review](data/intake-166-portable-review.json) confirms its scope.

For the complete principal whole-frame replay, on the working copy:

```sh
uv run --no-project python -B runtime/code/full_symbolic_parametric.py \
  --table runtime/candidate_1_244_old.tm --all-values \
  --sites runtime/certificate/sites_physical.json \
  --output /tmp/zfc-intake166-full-symbolic.json
```

Root ran this exact substantive command with a600-second process-group bound; it passed in540.786seconds with8,391cases,2,315,075rules,488rows and positive duration at least13. The [fresh result](data/intake-166-full-runtime-verification.json) agrees with the delivered result in every field except elapsed time. The [execution record](data/intake-166-full-runtime-execution.json), [raw stdout](data/intake-166-full-runtime-stdout.log.txt), [raw stderr](data/intake-166-full-runtime-stderr.log.txt) and [existing-evidence review](data/intake-166-full-runtime-review.json) are retained. Machine speed varies; a timeout remains an incomplete replay, not a success. The supplied `verify.py --full-runtime` also performs this job but its temporary child directories discard detailed outputs after completion, so the direct command is better for retained evidence.

For the shortest independent check of the actual state saving:

```sh
uv run --no-project python -B runtime/verify_local_stuttering.py \
  runtime/reference/zfc245_old.tm machine/zfc_compensated244_old.tm \
  --output /tmp/zfc-intake166-local.json
```

For permanent detailed reconstruction/local/boot outputs, run these from the copied package's `runtime/` directory:

```sh
uv run --no-project python -B rebuild_candidates.py
uv run --no-project python -B prove_contextual_fold.py
uv run --no-project python -B verify_local_stuttering.py \
  reference/zfc245_old.tm candidate_1_244_old.tm --output retained-independent.json
uv run --no-project python -B check_new_boot.py candidate_1_244_old.tm retained-boot.json
```

They recreate the three table pairs/mappings, overwrite `contextual_fold_proof.json` and write the two explicit outputs. Root's [retained-local record](data/intake-166-retained-local-execution.json) confirms all four commands pass and the local/boot outputs equal the delivered records exactly. This repeat retained detail discarded by the portable driver; it was not an additional independent checker.

The main driver also runs `equational/verify_backend.py` and the artificial `equational/equational_search.py … --search-below 184` demo on temporary copies. For retained equational outputs, copy `equational/` separately, run `verify_backend.py` from it, then `equational_search.py demo_theory.json --proof demo_proof.json --search-below 184`. The verifier regenerates packet, metrics, demo and verification files. These tests do not establish the cited Boolean-basis theorem or refute ZFC.

No discovery search, C++ compiler, Lean/Rocq proof check or TeX build ran in these substantive replays. The optional compensation search requires C++17 and decompression of `runtime/reference/cases.txt.gz`; the supplied README records its finite fuel/tape/fixture bounds. It is unnecessary for the direct proof and is not silently replayed here. The ancestor context246/prior250 drivers target different historical tables; do not run their `verify_all.py` as though it were an additional244 check. In particular, the historical checksum wrappers are not intake work.

The original `report.tex`, its includes and `report.pdf` are recoverable. The chosen collection reconciliation does not rewrite/build that article; the collection catalogue's `manifest.pdf` is rebuilt separately. Supplied PDF-quality/build records remain delivered evidence. The [main reconciliation](intake-166.md) and [candidate page](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-compensated244/README.md) keep ordinary proof, fresh finite replay and absent244kernel/PA endpoint status distinct.
