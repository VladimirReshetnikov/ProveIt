# Fresh current14-base model and iPRA client for the 67/106 expression

The corrected [client](FreshModel106.lean) has compiled against sixteen new
source-snapshot modules on the existing, source-built current14 project base.
It checks three no-premise declarations:

* `sameZero106`: in every model of IΣ₁, the positive-shifted 67/106 expression
  and the current14 expression vanish at exactly the same valuation;
* `bridge106`: the corresponding all-model polynomial/machine bridge; and
* `standard_equivalence106`: standard intuitionistic PRA derives the
  equivalence between the 67/106 no-positive-zero sentence and the
  intuitionistic negation of the mapped native ZFC-refutation predicate.

The last theorem states existence of an internal derivation, not either side
alone. The all-model argument uses the model difference ring and the existing
scaled-carrier `zero_iff106`; the local bridge adapts the general same-zero
argument before applying the existing iPRA transfer. The 67-row graph and degree
106 evidence remain separately described in `../normalized106-graph-syntax-binding/`
and `../normalized106-historical-finite-replay/`. This client does not parse
JSON, TeX, PDF, or coefficient bytes, and does not prove a Lean total-degree
theorem.

## Runs and evidence

* [Attempt 01](attempt01/) built eight new modules before the runner rejected
  a missing dependency path. Lean's namespace search selected the first project
  root for a later base module, so a second project root did not provide a
  fallback. Outer session 80956 exited 1. This was a provider-layout failure.
* [Attempt 02](attempt02/) used [build-v2.py](build-v2.py), copying all 16
  preflight-pinned source files into a fresh snapshot and linking 1,000 base
  object files into one combined project namespace. All sixteen module
  compilations exited 0. The source copies, direct inputs, companion/shadow
  observations and outputs are recorded in the state. Existing source
  modules produced warnings, including deprecation and linter warnings; their
  captured logs are retained. The final client failed because its source
  omitted `open ModelCarrierCurrent`, and outer session 13350 exited 1 before
  the driver's final authentication phase. Its failed client and `sorryAx`
  output are retained and are **not** the successful endpoint.
* [Attempt 03](attempt03/) adds that namespace opening and runs
  [check-client.py](check-client.py) against those same sixteen objects. It
  verifies the recorded source/object/log hashes and 1,860 direct-input
  companion/shadow observations from the successful extension records, checks
  the base links, and runs the existing full sixteen-module source/base
  preflight both before and after the client. Both preflight outputs match the
  pinned result exactly. The corrected client checks 210 direct-input
  companion/shadow slots before and after. Its dependency and Lean compile
  commands exited 0, and its own compile log has no warnings or errors. All
  three axiom reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx` appears. Outer session 52686 exited 0.

The successful client object is at
`/tmp/normalized106-fresh-model-client-20261105/FreshModel106.olean`, SHA-256
`d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942`.
The compiled source hash is
`61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769`;
the captured attempt-02 state hash is
`c42e5d49c4234ff93e61b7dbadf63fe8e2d465f470f4772879694796d898272c`,
and the attempt-03 state hash is
`dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23`.

Each Lean invocation used `-M2800`, one thread, idle I/O, nice 19, and a
180-second GNU foreground timeout. There was no automatic process-group RSS
or host-memory stop. The extension's sixteen successful dependency and compile
runs totalled 65.477 seconds; the corrected client's compile took 2.999
seconds. These checks observe and authenticate recorded direct inputs and
point-in-time base inventories. They do not independently rebuild or fully
authenticate the base, external package-transitive dependencies, dynamic
imports, toolchain dependencies, or transient mutations between observations.
This is one extension build, not a separate independent rebuild. The existing
base and Foundation provider retain their own recorded ancestry limitations.
