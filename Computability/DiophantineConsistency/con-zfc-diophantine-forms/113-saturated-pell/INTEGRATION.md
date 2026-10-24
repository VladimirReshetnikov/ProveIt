# Suggested ProveIt integration

This submission is pinned to commit
`84e16e43092614bae262ca59651cb9d77e31a255`.

## Primary review targets

| Candidate | Domain | Operations | Exact degree | Defining artifact |
|---|---|---:|---:|---|
| Saturated upper center | 10 positive integers | 92 | 283 | `equations/saturated_upper.json` |
| Saturated sharp center | 10 positive integers | 93 | 278 | `equations/saturated_sharp.json` |
| Direct saturated upper | 10 positive integers | 98 | 258 | `equations/direct_saturated_upper.json` |
| Direct saturated sharp | 10 positive integers | 99 | 254 | `equations/direct_saturated_sharp.json` |
| Saturated scalar carrier | 12 unrestricted integers | 123 | 1084 | `integer12_saturated/rational.json` |

The four positive points offer different operation/degree choices. The
twelve-integer point improves both metrics of its rational 145/1200 and
integral 141/1456 parents. `RESULTS.json` distinguishes these primary
results from the dominated controls.

## Arithmetic review

The principal ten-positive proof is in report Sections 3–5. Its important
interfaces are the product-square recovery, the `E | 1` obstruction to
cancellation, changed strong witness with `c^2 tau | I`, and the retained
source61 auxiliary-completeness theorem. The direct chart uses q^4 in P1
and delays q-divisibility until after projection.

The principal unrestricted-integer proof is report Section 6 and
`integer12_saturated/PROOF.md`. Its important interface is the
full-residue theorem with N=s tau, followed by the old residue tau a
modulo I. The exact restorations I=U tau and T_old=tau T require the
literal auxiliary term 4 U E T.

Both constructions inherit the named ordinary native/refutation
calibration. They provide new arithmetic reductions and finite algebraic
certificates. Their proof status should retain that distinction from
an end-to-end proof-assistant or encoded internal-ZFC endpoint.

## Reproduction and provenance

Start with `python3 -B check_manifest.py`, then follow the commands in
`README.md`. The polynomial builders are deterministic, and the complete
fixed coefficients reconstruct offline. The source34 integer tuple and
the compact44 BFS positive tuple have separate payloads and provenance.
Keep each tuple complete when moving candidates into repository packages.

The relation-algebra appendix is an explicit local research component.
Its seven coordinates count one inference kernel; they do not give a
seven-variable consistency equation.
