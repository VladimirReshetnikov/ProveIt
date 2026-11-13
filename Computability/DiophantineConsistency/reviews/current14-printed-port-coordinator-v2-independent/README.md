# Independent review of the v2 printed-port extension coordinator

The pinned coordinator, terminal verifier, reviewed v2 driver and owned-session helper were reviewed without launching the coordinator or Lean. The final source hashes are recorded in [result.json](result.json). The successful extension path remains **untested**; this review does not establish that the fresh base has finished or independently authenticate its final evidence.

The coordinator's success path captures the actual driver child PID and `wait()` exit code, requires zero, reads a terminal `PASS`, and invokes the verifier with that PID. It rechecks base/provider preflight and code/state hashes before and after terminal validation. The verifier requires exactly 61 ordered source/object/log rows and the final overlay inventory; checks direct base, external and output guards; compares each captured `lean --deps` stdout with its recorded declared direct dependency paths and requires empty deps stderr; and checks both per-row owned-session receipts for the driver parent, matching PID/group/session, drained session, reaped child and zero exit. Receipt fields are reported by the driver and pinned helper, not independent process tracing. Current source, selected objects, paths, hashes and complete logs are checked at terminal audit points; transient and inherited package-transitive/dynamic ancestry is not eliminated.

An initial review found that a non-`OSError` from emergency state saving could bypass the live-driver wait. The author changed that path to catch `BaseException`, retry `proc.wait()` after exceptions with a one-second delay, and retain the possibility of an indefinite passive wait. Their new controls inject a failed emergency save and a transient failed wait. Forced process death, escaped sessions and kernel or observation failures remain outside the guarantee. Resource samples are observational; the coordinator does not enforce a running memory stop. The verifier rejects the specified error and `sorry` patterns but **permits warnings**.

The author's controls record a synthetic 61-row positive terminal, rejection cases and an earlier refusal while the base was running. Independently, [nonempty-controls.py](nonempty-controls.py) exercised the pinned verifier with a fresh 61-row synthetic project: a base object reached by a symlinked overlay, a toolchain `Init` dependency, and a chain of 60 freshly produced project dependencies. It accepted that fixture, then rejected a wrong producer hash, a wrong project route, an extra declared import, an owned-session group mismatch and an unexpected overlay file; it rechecked the restored fixture. No actual subprocess receipt or Lean output is validated by these synthetic records.

No additional blocker was found in this scoped source review. Before a real launch, the live base must pass and its terminal evidence be independently audited, as required by the coordinator's own [README](../../research/current14-printed-port-extension-coordinator-v2/README.md); all pins and available resources must still match. The 61-module extension is not the printed-port assembly or endpoint join.

Read-only reproduction from any directory:

```
python3 -I -S -B path/to/current14-printed-port-coordinator-v2-independent/nonempty-controls.py
python3 -I -S -B path/to/current14-printed-port-coordinator-v2-independent/check.py
```

The resulting observations are frozen as `nonempty-result.json` and `result.json`.
