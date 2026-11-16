# Pentagonal tilings in intuitionistic primitive recursive arithmetic

Research package prepared 2026-11-16.

## Start here

- `pentagonal_tiling_ipra.pdf` - full human-readable report.
- `pentagonal_tiling_ipra.tex` - editable LaTeX source.
- `THEOREM_LEDGER.md` - claim-by-claim coverage and limitations.
- `FORMALIZATION_PLAN.md` - dependency-ordered route to actual `Prf PRAAx`
  derivations.
- `code/verify_pentagonal_tilings.py` - exact finite reference checker.
- `verification/results.json` - concise machine-readable results.
- `verification/periodic_witnesses.json` - edge pairings, bounded translate
  instances, and explicit exact separating axes.
- `lean/PentagonalTilingBlueprint.lean` - no-sorry host-Lean blueprint and
  completed arithmetic sanity lemmas.

## Reproduce

```bash
python3 -m pip install -r requirements.txt
./build.sh
```

Equivalently, run `make`.

The decisive certificate arithmetic uses exact fractions, `Q(sqrt(d))`, and
an explicit ordered quartic field for the Type 14 radical tower.  SymPy is used
only to render the Type 14 figure; Shapely is only a secondary numerical sanity
check after exact planar-complex verification of the nonconvex subdivisions;
Matplotlib produces diagrams.

## Formal status

The report gives constructive mathematical proofs and a complete encoding path
into iPRA.  The supplied Python checker passed all assertions.  The Lean file
contains no `sorry`, `admit`, or new axiom, but was not compiled here because
Lean/Lake are absent.  No main result is falsely advertised as an already
constructed `Prf PRAAx` value.

The full Rao classification, the 24-isohedral classification, the all-orders
nonperiodic rotational construction, and the irregular hyperbolic catalog are
not proved in this archive.  Their exact boundaries and import plans are in the
ledger and report.
