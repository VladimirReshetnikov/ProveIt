# Final integration review

Reviewed the current `article/07_implementation.tex`, `08_experiments.tex`, and
`10_reproduction.tex`, the production changes against commit
`8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`, the 17-file integration overlay,
the manifest, the focused-test runner, and the retained evidence. This was a
read-only integration review; no production or article files were changed and
no tests were rerun.

## Concrete corrections identified

1. **Implementation order, minor prose mismatch.** The opening of section 7
   says the adapter runs after construction of both parallelity geometry and
   marked boundary data. In `normal_cut_handlebodies`, top reduction runs
   immediately after parallelity construction and **before**
   `normal_parallelity_boundary_words`. Boundary words are independently
   reconstructed from the original source/vector afterward. The whole-cut
   verifier does authenticate both original proofs before replaying the top
   reduction, exactly as the later section correctly says. Suggested wording:
   “operating after construction of the original compressed parallelity
   geometry; marked boundary data are then reconstructed from the original
   source before terminal processing.” This is a documentation correction,
   not a source-authentication defect.

2. **Residual-audit reproduction command, concrete clean-checkout failure.**
   `residual_kernel_audit.py` unconditionally reads
   `FAST/core_top_research/forest_exchange_audit.json` when native checks are
   enabled. The printed preceding command writes
   `/tmp/forest-exchange-audit.json` instead, and the integration overlay does
   not include the data JSON at the hard-coded native path. Thus the printed
   sequence fails late in the residual audit on a clean patched checkout.
   The description that the neighbouring file is optional or read “when
   present” is inaccurate for the reviewed code. The smallest correction is
   to add this before the residual-audit command:

   ```bash
   cp /tmp/forest-exchange-audit.json core_top_research/forest_exchange_audit.json
   ```

   Alternatively, copy the retained package evidence to that location or
   direct the preceding forest-audit output there and adjust the chain-audit
   input accordingly. An explicit `--subdivision-source` option would also
   solve this, but is a code change rather than the smallest documentation
   repair.

3. **Asymptotic wording precision.** The exact old-loop count
   `(7*q*q+q)/2` is a count of row scans. The faithful old implementation also
   invokes `sorted(remaining)` on every pass. Replace “the old scan is
   quadratic” by “the old scan performs quadratic row-scan work” unless an
   additional sorting-cost argument is intended. All reported exact row and
   endpoint counts are correct. This does not affect the measured timing
   comparisons or the queue's linear structural bound.

## Claims and files that match

- Exactly two maintained files are modified. Five new `fastunknot` modules
  provide the top producer, independent top verifier, template API, abstract
  forest producer, and abstract forest verifier. The default integration
  does not invoke the abstract forest planner or residual quotient.
- The strict top-proof and version-6 wrapper schemas match the article.
  Nested versions 1–5 are accepted with their exact original field sets;
  nested version 6 and duplicate nested source/census fields are rejected.
- Both original source proofs are checked before reduced geometry is
  derived. The independent top replay imports neither the top producer nor
  queue, retains cap multiplicities, and checks exact survivor IDs.
- Surviving attaching records and marked-interface records are preserved;
  the original source summary remains original provenance. The no-three-
  handle producer path retains the previous schema behavior. The existing
  six-orbit-operation gate is unchanged.
- All 17 overlay files match the reviewed repository byte for byte; all
  manifest source hashes match. The two recorded baseline hashes also match
  `git show` at the pinned commit. The patch SHA-256 at review time is
  `fbb0c0e86685f2321116a0a4d3591951a7da0d7ad46a2d490eddf713ba7cdcf7`.
- The eight named test modules contain exactly **67** named methods:
  top reduction 9, whole cut 7, core handlebody 7, core primitive annuli 8,
  bundle boundary kernel 7, source handle reduction 12, template 5, forest
  exchange 12. This agrees with the section's 50 + 5 + 12 decomposition and
  the packaged runner. Passing status here refers to retained earlier
  evidence; the root agent owns the clean integration rerun.
- Coverage counts, all seven displayed histograms, 193-byte template trace
  lengths, abstract finite-case totals, forest applicability totals, and
  residual-quotient totals match their retained evidence.
- All six benchmark medians and ratios match the JSON. At `q=256`, the
  reviewed values are 47.097627 ms versus 1.635521 ms, ratio 28.796712;
  combined times are 88.425486 ms versus 45.654607 ms, ratio 1.936836.
  Shared source reconstruction is 45.540805 ms. A/A qualifications and all
  exact work counts match. Every benchmark source hash still matches the
  reviewed implementation. No full-recognizer speedup is claimed.

## Smallest portable replay of the seven saved whole-cut proofs

With `FAST` and `PACK` already set as in section 10, the following command
uses the supplied exact inputs and the independent whole-cut verifier. It
does not invoke the certificate producer or rerun the corpus/oracle audit.
The explicit count check prevents a missing directory from silently passing.

```bash
python - "$FAST" "$PACK/evidence/new_certificates" <<'PY'
import json
import sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies

files = sorted(Path(sys.argv[2]).glob("*.json"))
if len(files) != 7:
    raise SystemExit(f"Expected seven saved certificates, found {len(files)}")
for path in files:
    packet = json.loads(path.read_text())
    case = packet["case"]
    if not verify_normal_cut_handlebodies(
        case["triangulation"], case["coordinates"], packet["certificate"]
    ):
        raise SystemExit(f"Replay failed: {case['id']}")
    print(case["id"], "OK")
PY
```

The command's field names were checked against all seven retained packets.
It was not rerun during this final read-only gate because all seven already
have independent replay evidence and the root agent is performing the clean
release checks.
