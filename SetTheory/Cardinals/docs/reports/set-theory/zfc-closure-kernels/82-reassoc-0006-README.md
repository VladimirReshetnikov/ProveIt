# Independent audit contribution

All files in this directory are independent analysis or audit code produced
during this research session. No Lean or Rocq compilation was performed.

## Files

- `audit_notes.md`: endpoint provenance, Foundation/Regularity distinction,
  distinction between an external formal theorem and an internally coded
  first-order ZFC theorem, and independently reviewed candidate boundaries.
- `generalized_associativity.md`: a complete ordinary proof that
  `A;(B;C)` and `(A;B);C` have the same finite exit relations when A has no
  escaping Break and C has no escaping Continue. B is unrestricted.
- `generalized-associativity.tex`: the same complete proof as a LaTeX
  section suitable for direct inclusion in the report.
- `check_rm_certificate.py`: portable, standard-library-only checker of
  finite register-program operation bisimulation certificates.
- `rotation178_rm_audit.json`, `rotation226_rm_audit.json`: independent
  successful register-layer replays, including both outcomes of all
  decrements. Binary-table verification is explicitly outside this check.
- `mtf_local_audit.json`: independent parsing and literal verification of
  the local move-to-front table's exact row patch, block identities, state
  count, and incompatible header continuation. Its universal local proof
  is reviewed in `audit_notes.md`.

## Portable replay

The checker takes its three input paths explicitly and never changes them:

```sh
python3 check_rm_certificate.py OLD_PROGRAM NEW_PROGRAM CERTIFICATE
```

OLD_PROGRAM may be the pinned upstream `Prog254.v` or the same JSON node
format as NEW_PROGRAM. An optional `--output AUDIT.json` saves the result.
Paths in stored SHA-256 audit objects identify the exact original inputs;
they do not constrain where the files are placed when replaying.

For rotation 178, the inputs were:

```text
upstream_snapshot/ZF/m254/coq/tm/Prog254.v
incoming_research/rotation_candidates/rotation178_source.json
incoming_research/rotation_candidates/rotation178_bisimulation.json
```

The rotation 226 inputs use the corresponding `rotation226_...` names.
The 178 audit refers to the nine-occurrence source variant, including
source node 4364. Its changed binary table still fails the first universal
affine case described in `audit_notes.md`. The 226 source preserves the
register operation trace and its separate literal table passes the
sibling affine checker, but has 246 working states.

The operation checker proves a finite graph obligation. The mathematical
use of this obligation is induction on executed register operations:
identical opcode/register labels preserve equal register vectors; the
zero and positive successor edges select the same paired operation;
control normalization consists only of finite, register-preserving steps;
the paired halt labels then coincide. It establishes no property of a
binary table, startup, source logic, or ZFC on its own.

Pinned primary source URLs are recorded in `audit_notes.md`. The local
source snapshot contains `E2E254.v`. `Z_main.v` was additionally read
through the GitHub file connector at the same exact upstream commit;
its Git blob SHA is `7f6707cda4ba42f5eacd08fefe7f59e1beb06c4f`.

## Overall scope

These artifacts do not establish a complete consistency machine with
fewer than 246 working states. They supply a valid source reassociation
criterion, an independent source certificate replay, a valid local
arithmetic transformation, and concrete evidence identifying the missing
binary integration contracts.
