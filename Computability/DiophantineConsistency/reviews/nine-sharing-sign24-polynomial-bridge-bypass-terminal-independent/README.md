# Independent audit of failed sign24 sign26-bypass attempt

Author outer session 33816 exited 1. Independent checker session 28359 exited
0 and saved `result.json`. It validates the attempted source and logs, all
four direct provider bindings, direct guards, overlay links and upstream
audits. The first checker invocation found an incorrectly transcribed expected
sign26 object hash in the checker itself; after correcting the pin to the
independently recorded object hash, the completed audit passed.

The dependency scan succeeded, but Lean compilation exited `-6` with an
interpreter memory exception under `-M2800`. No bridge object or final
postflight exists; no new sign24 bridge or endpoint is established. Provider
checks are point observations and Lean was not independently replayed.
