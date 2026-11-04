# Independent factual audit: split natural-cover timeout

Attempt01 is FAILED and excluded. The author reports actual outer session 12320 exited 1 and was reaped. Retained outer terminal SHA-256 `5784dd617424edd20dd2ba3126435e7b9bbda539ca0806ae297c7b86b3602480` records child exit 1/FAILED, points to child result `94c0ab7dfb678c51f5a06dffdfe3d7a3ecb8b51716d7a373c378fdd3ce15d6c2`, and records stable wrapper/input hashes. The child records stage `Trace74SymbolicCoverNat`, Lean exit −9, monitor reason `timeout` and elapsed 601.494 seconds. Independently verified both empty stage logs and outer stdout/stderr against their receipt hashes. No Lean replay was run here.

No natural cover theorem is accepted by this attempt. Empty logs do not identify an elaboration hotspot or establish a source error, and the timeout does not invalidate separately accepted component theorems. It does not establish a model cast, fixed-port graph guard, external-file binding or iPRA.
