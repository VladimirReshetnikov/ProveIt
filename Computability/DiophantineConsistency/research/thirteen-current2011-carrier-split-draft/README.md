# Split thirteen-variable carrier: generic core

The earlier adapted carrier source failed at the 2.8 GB Lean interpreter
limit after seven predecessor modules had passed. Its exact five-import
probe subsequently passed. This draft mechanically splits the unchanged
literal syntax and generic replacement section into
`ModelThirteenCarrierCore.lean`; the remaining model and bridge body is
retained in `ModelThirteenCarrier.lean` and imports that core. The generator
pins the earlier adapted source and refuses to overwrite existing files.
The split retains the original generic and model section bodies; it has not
yet checked the remaining model body or constructed a 13-variable endpoint.

The bounded `run-core.py` check used the exact five original imports and
rechecked the seven prior source/object/guard records, 1,016 base links,
source/provider preflights, direct dependency paths and companions before
and after the check. The actual outer session 58572 exited 0, with the
recorded output `PASS split carrier generic core`. The nested dependency
and Lean compilation exits in [state](attempt01/state.json) are both 0; the
compile log is empty. The output object at
`/tmp/thirteen-carrier-split-core-20261105/lib/DiophantineConsistency/ModelThirteenCarrierCore.olean`
has SHA-256 `023005d35e7c8a460213270f9b7ec013954b1010c9d80945db918baee919d319`.
The state SHA-256 is
`442fc30b210d475f8b3de2f5b9910fe515849c0a80d91d196b39cc9881a29973`.
The successful generic core cannot by itself establish the model bridge or
an internal consistency equivalence. The current output depends on the same
captured seven predecessor objects and package provider; it is not an
independent full rebuild or dynamic/package-transitive load trace.

The run used `-M2800`, one Lean worker, a 180-second GNU foreground timeout,
nice 19 and idle I/O with memory/disk prechecks. It did not provide automatic
group-RSS or host-memory stops during Lean. The checked runner SHA-256 is
`022001410a713b18111c8986fad108d102974196afd2561993213eeaed901373`.

A separate check of the remaining model/bridge source was attempted with an
isolated overlay that authenticates the passing generic core and seven prior
outputs. The dependency run exited 0; compilation exited -6 after 11.5 s
with the Lean interpreter memory exception at the same `-M2800` limit.
Actual outer session 67406 exited 1. The complete failure and direct guard
state are retained in [attempt02](attempt02/state.json), SHA-256
`abd4db9e4bd36ae93f863b7d531673d0d584cb196716091fb390fb33ea6d76b2`.
The runner SHA-256 is
`7336813fc18deae45227047b0b8d16d97fde35e6300ba709110c2550bf126a10`.
The failure occurred before postflight and produced no successful remaining
module; it does not indicate a mathematical error or establish an endpoint.
