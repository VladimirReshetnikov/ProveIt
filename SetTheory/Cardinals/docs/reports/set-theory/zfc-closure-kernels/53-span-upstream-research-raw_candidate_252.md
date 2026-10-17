[`raw-candidate-252.tm`](raw-candidate-252.tm) is a complete **252-working-state,
two-symbol research candidate**, with start state 0 and terminal target 252.
It has 504 transition rows and SHA-256
`58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142`.
The full ordinary equality-free theory and the emitted code calculus have
different strengths. The reviewed finite-sort model in
[typed_countermodel.md](typed_countermodel.md) satisfies every emitted C/G
bundle and retained logical row while making target code 1 false. Thus the
intended abstract enumerator has a ZFC-formalizable nonhalting proof and cannot
provide the proposed consistency calibration. Applying this conclusion to the
literal table still requires its unproved compiler simulation. The numerical
count is below 254; this table is a compiler benchmark, with no proved
ZFC-consistency endpoint.

This candidate derives from Mira-Cult's published register program and
container/collection calculus, preserved by Jeff's attributed verification
snapshot at commit `297ab8df7e5de329605c3875b4934643b371a5e3`.
It uses Andrew James Wade's public MIT-0 `TMBuilder` backend. The edited
equality-free rows, dual quantifier row, base-3 constructors and code-sharing
recipe are this project's experiments; the baseline authors' verification
does not certify these changes.

The generator's `rho6`-dual/base-three variant produces the named source
`AX-raw_equality_free_C_G_shared_dual_base3.tm`, SHA-256
`06feea82f1ea6cbd7a93458d00e76c4afb14ab18e1cade3bb4afe1740dc48cab`.
See `theory_backend_experiment.py` and its evidence for the theory-emission
construction. The source has 252 working names and 503 rows; the only missing
row is `1.inc/read1`. The unchanged `audit_raw_candidate.py` validates the
source pin, fills that row with `write1, R, halt`, orders the start first and
the other working names lexicographically, and numbers halt last. In the
canonical table the added row is `13 1 1 R 252`.

Under the public backend's convention that an undefined transition halts,
this totalization preserves halting and the final tape: reading 1 and writing
1 changes no cell. It adds one final head move. No working state is added and
the terminal state is excluded from the count.

`PartialTotalization.lean` proves this generic normalization rule preserves
blank halting and final tape score. Its partial machine counts an undefined
transition as one attempted step that halts in place; the normalized machine
makes its final right move on that attempt. Their states and tapes agree at
every time, and their heads agree while running. This does not verify the
Python normalizer or certify the actual parsed rows of this candidate.

The conservative audit finds all 252 states graph reachable, with 252 singleton
exact step-bisimulation classes after 11 refinement rounds. There is no
startup-state reuse. At radius four and at most 64 local steps per side, the
finite-window search checks 24,604 abstract configurations and 63,252 ordered
state pairs, permits all 504 transition rows, and finds no safe single-state
merge. These checks establish neither global minimality nor the candidate's
intended mathematical meaning.

A one-million-step operational prefix from blank does not halt. The final
configuration has state 24, head 248, and 223 one-cells; 133 states and 253
transition pairs were observed. An independent simulation of the named source
agrees with the numbered table throughout that prefix and has the same final
configuration hash
`fbe8133c0bdf91b636fb874702396caf107525c3f0b906ce2b4e5e43c94c49db`.
This finite run does not establish future behavior or marker invariants.
It does not reach the edited AX theory-emission routine, so this prefix alone
does not test that routine's operational behavior.

Reproduce normalization and the radius-four audit from the generated named
source, preserving the separate 255-state evidence:

```sh
python3 Computability/BusyBeaver/Research/ZFC/audit_raw_candidate.py \
  /tmp/zfc-theory-backend/AX-raw_equality_free_C_G_shared_dual_base3.tm \
  --expected-sha256 06feea82f1ea6cbd7a93458d00e76c4afb14ab18e1cade3bb4afe1740dc48cab \
  --expected-states 252 --scratch /tmp/zfc-raw-candidate-252-audit \
  --window-radius 4 --macro-steps 64 \
  --output-evidence /tmp/raw-candidate-252-normalization.json
```

Its scratch `raw-candidate-total.tm` is byte-for-byte the checked-in research
artifact. Audit that artifact directly, including the operational prefix:

```sh
python3 Computability/BusyBeaver/Research/ZFC/audit_tm.py \
  Computability/BusyBeaver/Research/ZFC/raw-candidate-252.tm \
  --expected-sha256 58f8aab7fcc21a7e3a88e6250bf05b7a97eaafd340f75ea8117b6d8f989f3142 \
  --expected-states 252 --expected-halt 252 \
  --window-radius 4 --macro-steps 64 --self-test --trace-steps 1000000 \
  --output /tmp/raw-candidate-252-prefix-audit.json
```

[`raw-candidate-252-audit.json`](raw-candidate-252-audit.json) combines the
normalization provenance, exact research-artifact identity, conservative audit,
and prefix comparison. The normalizer's seven regressions and auditor's eleven
tests pass. No Lean or Coq build, compiler simulation proof, or consistency
calibration theorem is supplied by this artifact.
