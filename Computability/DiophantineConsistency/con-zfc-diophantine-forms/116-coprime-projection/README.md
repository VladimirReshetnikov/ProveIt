# Coprime fusion and low-degree Diophantine projections

Research release for incorporation into ProveIt, 24 October 2026. The
manuscript is `report/report.pdf`, with editable sources in `report/`.
The report and component proofs distinguish new ordinary mathematical
reductions, finite computational checks, and inherited source calibration.

## Main completed constructions

- `integer/`: four single ordinary polynomials in 11 unrestricted integer
  variables. The principal trade-offs are degree 688 / 126 binary
  operations, degree 728 / 122 operations, and degree 1632 / 114 operations.
  The degree-1892 companion has 114 operations.
- `positive/`: a single ordinary polynomial in 10 strictly positive integer
  variables, exact degree 266, 96 live binary operations.
- `lowdegree/`: four single polynomials over unrestricted integers: 15
  variables / degree 56 / 110 operations; 14 variables / degree 108 / 119
  operations; 13 variables / degree 274 / 129 operations; and 12 variables /
  degree 500 / 148 operations.
- `alternative/`: a standalone positive-exponentiation graph with 9
  auxiliary natural variables and exact degree 20, and simultaneous-graph
  and four-corner tiling compositions. The 9-auxiliary graph has 12 variables
  in total. These are not newly calibrated Con(ZFC) equations.

Every listed equation is an actual finite polynomial circuit using fixed
integer coefficients and explicitly declared variables and domains.
Intermediate registers are polynomial abbreviations, not extra quantified
variables. Fixed numeral payloads are authenticated binary files, not free
parameters. A circuit is an unexpanded specification of one ordinary
polynomial, not an appeal to a universal interpreter or a hidden
exponentiation predicate.

The new consistency-facing arithmetic equivalences compose with the named,
pinned ordinary native/compiler/refutation calibration. If that inherited
calibration is not taken as established, the unconditional new claim is the
explicit predecessor-source zero-existence equivalence. No proof of
consistency, global minimum, new internal object-ZFC derivation, or new
end-to-end Lean/Rocq certificate is asserted.

## Reproduce the entire iteration

Requirements: Python 3.10 or newer and SymPy 1.14.0. The build scripts and
producer checkers use Python's standard library; several separately written
reviewer audits require SymPy. The delivered run used Python 3.12.14.
Install the optional-review dependency into a suitable environment with:

```sh
python -m pip install -r requirements.txt
```

The reproduction runner itself never installs anything, fetches from the
network, clones a repository, or runs a proof assistant. After the dependency
is available, all new checks run offline:

```sh
python -B reproduce.py
```

The command can be invoked by absolute path from any current directory. It:

1. Verifies all delivered producer manifests and any root release manifest.
2. Makes independent temporary copies for normal Python and optimized `-O`.
3. Executes every new builder from an unrelated working directory and
   compares all regenerated equation/specification bytes with the delivery.
4. Runs all producer and independent reviewer audits in both modes.
5. Demonstrates rejection of a changed byte, missing file, and added file,
   and of a corrupted actual integer circuit outside any manifest guard.
   The component checkers additionally exercise their own mathematical
   mutation controls.
6. Verifies that the original release tree is unchanged. Temporary work is
   removed automatically.

To save a new receipt, use `--receipt /path/outside/the/release/recheck.json`.
The supplied `REPRODUCE_CHECK.json`, when present, records the packaging run.
Receipt fields that refer to historical Git comparisons may differ when
rerun without the original research clone: local size/hash checks remain
mandatory, and the optional Git comparisons are labelled rather than
pretended to have been replayed.

## Contents and provenance

- `report/`: editable manuscript and compiled PDF.
- The four component directories: equations, ordinary proofs, builders,
  checks, coefficients or fixed literals, and retained licensing/provenance.
- `review/`: independent review prose and executable audits; low-degree
  variant audits are also distributed next to their respective components.
- `baseline/`: pinned comparison, citation, and source records, including
  a bounded late comparison review. The construction pin remains
  `84e16e43092614bae262ca59651cb9d77e31a255`; the late comparator pin is
  `56b4d15d128be25688c20a39049c10a59b0e9cb3`.
  The 545 MB research clone and incoming ZIP archives are intentionally not
  redistributed and are not needed for the new offline checks.
- `DEPENDENCIES.md`: runtime requirements, mathematical dependency map, and
  limits of excerpted historical source material.

Producer manifests are preserved exactly. A root manifest, if present,
seals the complete release without rewriting those producer records.

## Recorded validation summary

The release includes 36 successful builder/audit executions across normal
and optimized Python: 7 builders and 11 audits per mode. Twenty generated
files rebuild byte-identically in each mode, and three exact certificate
contents agree. The recorded controls reject 109 corruptions per mode.
These finite checks do not replace the ordinary unbounded proofs.
See REPLAY_SUMMARY.json and REPRODUCE_CHECK.json for their exact scopes.
