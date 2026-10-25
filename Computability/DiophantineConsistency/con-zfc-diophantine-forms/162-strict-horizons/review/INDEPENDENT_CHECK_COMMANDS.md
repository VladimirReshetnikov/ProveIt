# Independent checks

Run the following commands from the extracted package root. Each script
uses Python's standard library only. All default inputs are resolved
relative to the script, so the scripts also work when invoked by absolute
path from another working directory. These commands overwrite only their
named review receipts.

## Strict-horizon signed-power interface

```sh
python3 code/check_power_interface.py --output review/POWER_INTERFACE_CHECKS.json
python3 -O code/check_power_interface.py --output review/POWER_INTERFACE_CHECKS_OPTIMIZED.json
cmp review/POWER_INTERFACE_CHECKS.json review/POWER_INTERFACE_CHECKS_OPTIMIZED.json
```

Default input: `direct/source/raw_source.json`. An optional positional
argument selects a different raw-source file. This checker imports no
producer or transformation module. It checks seventeen scalar requests,
the complete deduplicated frame, fourteen principal pairs, all signed-cap
rows and anchor attachment, all digit/range denominator identities, and
twelve deliberate corruption controls. See `POWER_INTERFACE_REVIEW.md`
for the precise scope.

## Compact ten-positive-variable equations

```sh
python3 review/check_compact_independent.py --output review/COMPACT_INDEPENDENT_CHECKS.json
python3 -O review/check_compact_independent.py --output review/COMPACT_INDEPENDENT_CHECKS_OPTIMIZED.json
cmp review/COMPACT_INDEPENDENT_CHECKS.json review/COMPACT_INDEPENDENT_CHECKS_OPTIMIZED.json
```

Default input directory: `compact/`. An optional positional argument
selects a different directory containing the two equation JSON files.
This checker independently reconstructs the displayed formulas and
checks topology, operation counts, liveness, total-degree upper bounds,
and 80 modular formula evaluations per equation. The exact degrees and
the unbounded arithmetic argument are assessed in
`COMPACT_INDEPENDENT_REVIEW.md`; finite evaluations alone do not prove
them.

## Cofinal Pell experiment

```sh
python3 experiments/cofinal_pell/verify_pell_generator.py --output experiments/cofinal_pell/PELL_CHECKS.json
python3 -O experiments/cofinal_pell/verify_pell_generator.py --output experiments/cofinal_pell/PELL_CHECKS_OPTIMIZED.json
cmp experiments/cofinal_pell/PELL_CHECKS.json experiments/cofinal_pell/PELL_CHECKS_OPTIMIZED.json
```

This standalone arithmetic experiment reads only its adjacent `PROOF.md`
to include the proof's SHA-256 in the receipt. It checks 560 exact small
Pell pairs, 4661 Taylor congruences, 34 cofinal horizon examples, and 464
matrix-lifting examples. It also records the explicit counterexample to
the initially overbroad congruence claim at horizon 16. The universal
proof is in `experiments/cofinal_pell/PROOF.md`; this experiment is not a
selected equation or a claimed variable-count improvement.

## Recorded outcome

All six release-version runs pass. In each pair the normal and `-O`
receipts are byte-identical. None of these checks attempts to establish
`Con(ZFC)`, solve the consistency equation, or replace the inherited
C222/ZFC calibration proof.
