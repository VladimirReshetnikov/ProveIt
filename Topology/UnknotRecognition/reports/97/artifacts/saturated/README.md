# Saturated-bundle source evidence

This directory contains the completed native audit for the accompanying opt-in
saturated-bundle census. The source baseline is ProveIt commit
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb`, with the source changes supplied in
this delivery applied to that checkout.

## Completed result

The operator completes **85 of 106** retained normal-cut cases, preserving all
**78** previous successes and adding **seven** saturated nondisk cases. All
85 complete source certificates independently replay. Fresh Regina calls
construct 99 literal cuts and agree with all 78 successful censuses below the
expansion cap, including all seven new cases. Seven large-coordinate successes
use independent source replay without expansion. The remaining 21 cases are
inconclusive: eleven stalled raw matrices and ten cores with three-handles.

The focused suite records **17 passing tests**. Whole-project validation is
reported separately in the delivery's main validation artifacts.

## Contents

- `audit.json`: all 106 cases, outcomes, timings, fresh oracle comparisons,
  corpus and baseline hashes, and changed native-source hashes.
- `audit_stdout.txt`: the original completed audit log.
- `new_cases.json`: exact seven new sources, normal vectors, isomorphism
  signatures, base topology, old reasons, new censuses and certificate hashes.
- `worked_case_019.json`: the exact labelled aggregate matrix, core forest,
  source certificate hash and cancellation sequence for `pilot/lst_4_7/0`.
- `stopping_obstructions.json`: exact uncapped matrices, canonical stopping
  sets, source packet hashes and independent checks for all eleven raw stalls.
- `extract_stopping_obstructions.py`: portable extraction and authentication
  driver restricted to those eleven cases.
- `certificates/`: the seven complete source-bound proofs and their exact inputs.
- `unit_tests.txt`: the completed focused test log.
- `environment.json`: recorded Python, Regina and platform versions.
- `provenance.json`: repository checkpoint, archive hashes, source hashes and
  scope of the targeted incoming-package audit.
- `run_audit.py`: portable reproduction driver.
- `artifact_manifest.json` and `SHA256SUMS`: packaged-file integrity records.

The raw audit log retains its original output-location record. That location is
historical metadata and is not needed to reproduce the experiment.

## Reproduce

Apply the accompanying integration changes to the baseline checkout. The audit
uses its existing marked-parallelity corpus and saved primitive-annulus audit.
Run the following from this delivery's root, replacing the example checkout
path:

```sh
export PROVEIT_CHECKOUT=/path/to/ProveIt
python artifacts/saturated/run_audit.py --fresh-oracles --output reproduced/saturated/audit.json
```

Alternatively pass `--checkout /path/to/ProveIt`. The driver does not require the
original workspace layout. Omitting `--fresh-oracles` reruns the source pipeline
and compares against the saved historical Regina results. Fresh oracle runs
require Regina and retain the existing per-case expansion cap.

To regenerate the eleven obstruction records with fresh source authentication:

```sh
python artifacts/saturated/extract_stopping_obstructions.py --output reproduced/saturated/stopping_obstructions.json
```

The recorded matrices split into six cases whose old-core rows already contain
a stopping set and five whose obstruction requires saturated attachment rows.
All saturated bases in the latter five cases are disks. All eleven source
packet pairs independently replay; every obstruction passes the independent
checker, and an opposite-order peeling implementation confirms the canonical
residual. The full source packets can be regenerated from the pinned corpus;
their exact canonical JSON hashes avoid duplicating the orbit proofs here.

To rerun the focused tests, execute this command from the checkout's
`Topology/UnknotRecognition/fast` directory:

```sh
python -m unittest tests/test_normal_cut_saturated.py -v
```

The production source requires the accompanying
`core_handlebody.column_cancellation_plan` update. The new independent saturated
verifier imports neither that planner nor the saturated producer.

## Interpretation

These certificates establish the unmarked handlebody census of a supplied
source cut in the supported geometric class. They are not standalone unknot
verdicts. Raw-cancellation failure remains inconclusive. No general boundary
pattern transport, useful-surface discovery, or global quasi-polynomial
recognition bound is claimed by these artifacts.

Joint cancellation does not repair a stopping set already present among the
original core rows: those rows form a submatrix of the joint system. Its role
is to establish cancellation compatible with the full saturated attachment
data. The worked example explicitly records a successful old-core-only order.
