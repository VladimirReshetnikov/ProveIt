# Reproduction

Run these commands from the extracted package root. Core checks use Python
3.10 or newer and its standard library. Run auxiliary and formal scripts
without `-O`, because their checks use assertions. The primary machine
verifier uses explicit checks. Verify the delivered manifest before
regenerating outputs:

```sh
sha256sum -c SHA256SUMS
```

## Main machine and independent verification

```sh
python3 code/verify_reduction.py
```

This checks the pinned predecessor, exact candidate and renumbering,
3,888 local Boolean obligations, symbolic whole-tape blocks, and the
407,967-to-407,979 initialization comparison. It also runs the canonical
table through a separate dense interpreter. Expected results are
`PASS_FINITE_REDUCTION_CERTIFICATE` and
`PASS_INDEPENDENT_BLANK_COMPARISON`. Add `--build` to regenerate the exact
machine files; `--skip-blank` checks only the finite proof certificate.

The separately implemented checker takes explicit inputs:

```sh
python3 discovery/check_borrow242_independent.py \
  --baseline reference/zfc_combined243_old.tm \
  --candidate machine/zfc242_old.tm --blank-prefix \
  --output /tmp/zfc242-independent.json
```

## Fresh Lean build and literal table generation

Install official **Lean 4.32.0**; Mathlib is unnecessary. Choose a fresh,
nonexistent or empty output directory:

```sh
python3 formal/verify_formal.py \
  --lean /absolute/path/to/lean --output /tmp/zfc242-formal-replay
```

The verifier first binds every literal array entry to both `.tm` files,
then compiles copied sources into a separate object directory. Success
requires 18 named axiom reports, 13 typed callers, zero warnings, permitted
axioms only, and unchanged input files. The delivered run is preserved as
`evidence/formal/verification.json` and four accompanying logs.

Regenerate the table module without overwriting the delivered proof:

```sh
python3 formal/generate_tables.py \
  --baseline reference/zfc_combined243_old.tm \
  --output /tmp/Tables242-regenerated.lean
cmp formal/Tables242.lean /tmp/Tables242-regenerated.lean
```

These modules prove the relative machine theorem. The complete inherited
consistency calibration is not an additional theorem checked by this build.

## Selected discovery recipe

```sh
python3 code/discovery/compensated_search.py \
  --input reference/zfc_combined243_old.tm \
  --expected-sha256 4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300 \
  --dead 15 --keep 27 --bit 1 --radius 5 --bound 64 \
  --output /tmp/zfc242-selected-discovery.json
```

This checks exactly one successful recipe. Omitting the three control/bit
restrictions reruns the optional 116,644-recipe family. The adjacent
discovery README explains its six historical successes and why rejected
bounded certificates are not lower bounds. Discovery is unnecessary for
the primary proof.

## Optional source and encoding experiments

The independent four-loop source check is self-contained:

```sh
python3 alternatives/source-rotation/check_source.py \
  --baseline alternatives/source-rotation/baseline_sites_logical.json \
  --output /tmp/zfc242-source-rotation
```

It verifies the transformation to 6,455 leaves and 8,386 guarded cases.
The optional affine replay requires the inherited `baseline245` directory
recovered with the pinned repository's `recover_167.py`; see the auxiliary
README for that dependency:

```sh
python3 alternatives/source-rotation/check_affine.py \
  --reference /absolute/recovered/zfc244-loop-rotation-20261018/reference/baseline245 \
  --baseline-table reference/zfc_combined243_old.tm \
  --source alternatives/source-rotation/sites_logical.json \
  --output /tmp/zfc242-source-affine
```

This auxiliary transformation saves four source leaves and no binary states;
its evidence does not provide a new expanded or bootstrap proof.

The orientation experiment requires a ProveIt checkout containing the
pinned Git objects, ZFC research helpers, and closure-kernels source 08/19
helpers at commit `e58338db7545909907e07a7603e8eb88625c527a`:

```sh
python3 alternatives/orientation/orientation_control.py \
  --repo /absolute/ProveIt --seeds 256 \
  --out /tmp/zfc242-orientation
```

The driver verifies helper identities and extracts the vendored backend
from Git. Its 268-to-267-state control improvement is supplementary compiler
evidence; it is not used to calibrate the 242-state machine.

## PDF

With `pdflatex` and the report's TeX packages installed:

```sh
python3 code/build_report.py
```

The builder regenerates all 484 appendix transitions from the hashed
canonical table, compiles three passes, and checks layout/reference errors.
`--table-only` regenerates just the transition appendix. The scientific
content is reproducible; PDF metadata can prevent byte-identical rebuilds.
