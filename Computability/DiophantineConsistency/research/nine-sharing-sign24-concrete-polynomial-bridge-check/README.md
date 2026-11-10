# Sign24 concrete polynomial bridge guarded check

This single-stage client proposes transferring the checked sign25
`PolynomialBridge` to the sign24 Fin24 expression through the audited
sign24/sign25 model-zero equivalence. It does not itself derive an iPRA
endpoint or bind external coefficient bytes or degree metadata to Lean.

The guard surveys the generic transport and sign25 bridge producer rows and
their overlays against the sign24 expression-equivalence base. The generic
provider has 1,058 matching overlay entries and 20 extras; the sign25 bridge
provider has 1,064 matching entries and 317 extras. Shared extra bytes must
match. These are point observations of an inherited provider union, not a
complete transitive or dynamic load trace. The inherited syntax heartbeat
option is 4,000,000; this client adds none. Each Lean invocation uses
`-M2800`, one thread and 120 seconds, with a monitored 4 GiB RSS cap, 10 GiB
available-memory floor and a 5 GB free-disk precheck.

Author no-Lean preflight exited 0 (`preflight-author-record.json`). After
independent prelaunch review, attempt 01 failed with author-observed outer
session `56027` exit 1 due to an interpreter memory exception; see
`attempt01/README.md`. The [independent failure audit](../../reviews/nine-sharing-sign24-concrete-polynomial-bridge-terminal-independent/README.md)
passed and the packet is frozen. The separate sign25 endpoint attempt
previously failed similarly, and the sign24 endpoint remains unproved.
