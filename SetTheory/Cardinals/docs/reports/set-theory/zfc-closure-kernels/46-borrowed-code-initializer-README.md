# Initializer engineering artifacts

The final complete compiler controls have **299 states from zero registers**
and **300 states from nextproof = 2** on the retained 202-node decoder. The
matched earlier source34 controls had 309 and 311 states. These are initializer
and compiler improvements; the existing public 253-state consistency machine
is still smaller. No new end-to-end consistency theorem is claimed.

The full ordinary proof, exact formulas, provenance, comparison, and scope are
in `initializer_proof.md`. All tables start in state 0 on an all-zero binary
tape, move left/right on a two-way infinite tape, and have a separate terminal
label equal to the number of working states. Every working state has both
binary rows.

## Fast verification without a repository

From the archive root:

```sh
python code/initializer/verify_initializers.py
```

The verifier uses only Python's standard library. It independently parses all
eight selected source/quotient pairs, checks each complete transition-map
certificate, runs every raw blank initialization, and checks the entire finite
tape support and absolute head. It also regenerates the two standalone frame
instances and rejects two deliberately corrupted certificates. The recorded
run took less than one second on the execution host. This is finite artifact
verification, not a Lean or Coq build.

For a different layout, pass `--data-dir` and `--machine-dir` explicitly.
Assertions must remain enabled; the tools reject `python -O`.

## Full regeneration using the pinned repository

The full integrator requires a checkout of ProveIt at
`61e77836565f63582561f54745f633d50efd9c7d`, including the pinned upstream
snapshot and the closure-kernel data. It checks that the necessary backend
and DAG files still equal that commit. The checkout is used as input, and all
generated output must be outside it.

```sh
python code/initializer/integrate_odometer.py --repo /path/to/ProveIt --output /tmp/odometer-base
python code/initializer/share_odometer_exit.py --controls /tmp/odometer-base --output /tmp/odometer-shared
python code/initializer/integrate_odometer.py --repo /path/to/ProveIt --output /tmp/odometer-refined --one-sentinel-only
python code/initializer/share_odometer_exit.py --controls /tmp/odometer-refined --output /tmp/odometer-refined-shared
```

These commands regenerate the original controls as well as the final selected
ones. Fourteen complete integrations each passed 8,391 affine instruction
cases, totaling **117,474** evaluations. The shared-return variants retain
the exact same runtime rows and gap, so their earlier runtime checks transfer
by literal row identity; their changed blank initializations are replayed
separately. No runtime check is silently counted twice.

The independent standalone constructor boundary suite is:

```sh
python code/initializer/odometer_initializer.py > /tmp/standalone36_checks.json
```

It contains 36 whole-tape checks, including all auxiliary-counter bit counts
1 through 9 with three payloads, and the register-clock variants at 9, 10,
and 11 bits. The supplied `data/initializer/standalone36_checks.json` records
the completed suite.

## Files

* `code/initializer/`: independent initializer constructors, complete integrator,
  shared-return adapter, exact quotient checker, offline verifier, and proof.
* `data/initializer/final_controls_summary.json`: the eight final controls,
  pins, row counts, initializer contracts, whole tapes, hashes, and check scope.
* `data/initializer/*-quotient.json`: complete source-to-quotient state maps.
* `data/initializer/full_integrations.json`: all fourteen full compilation and
  affine-check records; intermediate regression tables can be regenerated.
* `data/initializer/quick_verification.json`: the successful packaged verifier.
* `machines/initializer/`: eight final raw tables and their eight quotients.

| Decoder | Zero quotient | Seed-2 quotient |
|---|---:|---:|
| Original219 | 316 | 317 |
| Rebracket207 | 304 | 305 |
| Rebracket206 | 303 | 304 |
| Decoder202 | **299** | **300** |

All final zero initializers have gap 513 and exactly 269,348 steps; all seed-2
initializers have gap 513 and exactly 269,349 steps. The raw and quotient
versions have identical tape/head behavior at every step because the
certificates are exact transition homomorphisms. The quotient counts in the table
refer to the complete emitted machine size, including initialization.

## Attribution and license boundary

The register engine and original optimized machine are Mira-Cult's; Jeff
supplied the upstream Coq verification; Andrew James Wade supplied the
underlying binary/register framework. The public 253 reduction is attributed
to mira-emmy. The new initializer and glue were written for this report.
The final dispatcher-return sharing follows earlier source34, and all decoder
inputs preserve their existing ProveIt provenance.

Upstream pin: `jeff87654/busy-beaver` at
`297ab8df7e5de329605c3875b4934643b371a5e3`.
The ProveIt import's `lib/jeff-busy-beaver-zfc254/README.proveit.md` records that
there is no upstream-wide license in that pinned tree and excludes its
snapshot from a blanket MIT-0 grant. These derived machine artifacts retain
that boundary; this report does not relicense upstream work. Wade's retained
MIT-0 notice is included as `LICENSE.wade` for attribution. No Coq vendor code
is bundled in this initializer subpackage.
