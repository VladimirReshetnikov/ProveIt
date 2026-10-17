# Attribution and third-party materials

The report and new audit code build on the following credited sources.

## Machine lineage

- Mira-Cult: the 254-state binary machine.
- Jeff Ketchersid and contributors: the upstream set-theory/calculus,
  register-machine and binary-machine verification, symbolic executor,
  and register-box summaries.
- mira-emmy / public PR 20: the 253-state reduction, generator,
  and associated proof bridge.
- Andrew James Wade: the underlying compilation framework.

Pinned upstream main:
297ab8df7e5de329605c3875b4934643b371a5e3.

Pinned public 253-state head:
0d544f2a2e3c18f12278441a74b7879f31cbe856.

## ProveIt research lineage

- Batch 153 source 35 supplies the prior safe-start and dirty-root proofs
  and the fixed-gap adapter. Its adapter is included byte for byte as
  code/machine/source35_runtime252_short_gap.py.
- Batch 153 source 36 already supplies the normalized two-cycle support
  countermodel, EPSC1/Pairing/EPSC2 separation, and empty-replacement
  obstruction. This report adds the integer-ray acyclicity refinement,
  fixed finite support capacities, and source-covered Replacement.
- Earlier sources supply the EPSC2 calibration, EPSC1 + adjunction
  comparison, saturation constructions, and complete-program controls.
  The report's bibliography pins the inspected intake files.

ProveIt novelty-audit pin:
ba00775e2bf56b184d071346867db74f2eb0c621.

The report makes no general historical-priority claim for support models,
parameter elimination, the inner-model consistency method, or the
elementary image/Pairing repair.

## Preserved notices

Original component notices are retained under:

- code/machine/upstream/ZF/generator/LICENSE.wade
- code/machine/upstream/ZF/stdzf_r3/vendor/busycoq/LICENSE
- code/machine/upstream/ZF/stdzf_r3/vendor/busycoq/LICENSE-LibTactics
- code/machine/upstream/ZF/stdzf_r3/vendor/undecidability/LICENSE

The retrieved upstream tree did not expose a repository-wide top-level
license. The m253 README states that it supplies no new license grant.
The component notices are preserved as given; this package does not
assert that one notice relicenses every external contribution.

Exact source origins and hashes appear in
data/machine/machine_manifest.json. The included source tree is the
minimal functional Python replay input, not the full Lean/Rocq dependency
closure. External scholarly PDFs are cited rather than redistributed.

