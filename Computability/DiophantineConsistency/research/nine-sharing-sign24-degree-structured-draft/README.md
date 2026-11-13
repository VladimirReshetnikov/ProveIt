# Compositional sign24 degree upper bound draft

The previous monolithic `rfl` syntax-degree computation exceeded its guarded
120-second limit. This source-only retry separates the generic expression
degree bound, an inductive substitution bound and list-of-squares bound, the
individual residual degree checks, and final composition through input
removal. Only the finite residual checks use a local 4,000,000-heartbeat
option, matching the prior syntax setting. No theorem has yet been checked.

The proposed conclusion is polynomial total degree **at most eight** for the
actual Lean abstract expression at any integer ports and for current ports.
It does not assert an exact lower bound or bind JSON, coefficient bytes or PDF
semantics. The existing `-M3600`, 4 GiB sampled RSS, 10 GiB host-memory floor,
120-second timeout and provider guards are unchanged; independent prelaunch
review and an assigned Lean slot are required.
