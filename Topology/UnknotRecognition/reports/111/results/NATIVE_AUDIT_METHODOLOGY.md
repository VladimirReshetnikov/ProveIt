# Native coverage and independent replay

`native_audit.json` contains 120 source records and a finished audit flag.
The sources are the copied 106-case historical corpus and 14-case interior
extension.  The current default, the new group terminal, and a separately
isolated deferred-forest runtime were each evaluated on every source.
Every positive was independently replayed against its triangulation and normal
coordinates.  All positive histograms agree where their domains overlap.

The fresh counts are:

| Method | Historical | Interior extension | Total |
|---|---:|---:|---:|
| Current canonical default | 92 | 12 | 104 |
| New direct group terminal | 64 | 12 | 76 |
| Deferred-forest comparison | 99 | 12 | 111 |
| Current default plus group terminal | 95 | 12 | 107 |
| Deferred forests plus group terminal | 100 | 12 | 112 |

All **291 positive outputs** across the three separately evaluated methods
passed independent replay.  Fresh literal Regina cuts and exact handlebody
recognition completed on 113 sources.  Seven binary sources exceeded the
4,096-normal-disk expansion cap and were not expanded.  Agreement counts are
97 canonical, 69 group, 104 deferred and 105 for their union.  All eight union
refusals have a literal component recognized as nonhandlebody by the oracle.
The new recognizers nevertheless report `INCONCLUSIVE` for these refusals.

The current pinned baseline has 104 default positives.  The earlier incoming
deferred-forest article had 102 canonical positives at its older baseline.
The present default already solves `interior_loop/empty` and
`interior_loop/boundary_link`; those are not credited as new gains here.

The new group terminal adds three current-default successes:
`pilot/finite_trefoil/0`, `pilot/finite_figureEight/0`, and
`pachner23_5_8_2/mixed`.  Only `pilot/finite_figureEight/0` adds to the preceding
deferred method.  The earlier exploratory shortest-donor group producer is
not the final minimum-resulting-length producer; its smaller coverage count
is not used in the article's final results.

## One harness transport correction

The first run completed and retained 105 cases.  At case 106,
`binary/1/16384`, the isolated deferred worker correctly transported the very
large histogram multiplicity as a hexadecimal string, while the parent held
the equal native integer.  A direct Python comparison in the audit harness
therefore reported a false histogram disagreement.  No source or group
certificate checker failed.

The harness now decodes the specified histogram integer fields using the
established exact integer codec before comparing them.  The final fifteen
cases were run afresh after a resume guard verified that every production
Python source, both fixture files and all four deferred comparison modules
had exactly the same SHA-256 as in the retained first 105 cases.  The final
report records this prefix and resumed work.  This is a completely checked
120-case audit assembled from a preserved prefix and a corrected continuation,
not a claim that the first invocation finished without a harness error.

The incomplete prefix is retained separately for provenance; it is superseded
by the finished `native_audit.json`.  The portable command works from scratch
with the corrected comparison, and `--resume` remains available for interrupted
audits with unchanged source identities.

## Timing scope

This run is a coverage/replay/oracle audit.  Its elapsed administrative runtime
was affected by concurrent work and is **not** a benchmark or speed claim.
Source hashes, fixture hashes, dependency versions and exact per-case outputs
are preserved.  All 76 group positives retain full source-bound certificates in
`certificates/group/`; `tools/audit_native.py --replay-only` checks them again.

The separately replayed packets in `certificates/euler_defects.json` retain
the free-group and source proofs for the five Euler-mismatch cases.  Their
strictly positive total second Betti numbers are reconstructed from the
certificates; these are not merely unverified producer statistics.
