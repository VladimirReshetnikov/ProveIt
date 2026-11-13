# Sign23 Lean polynomial degree upper bound draft

This source-only draft adapts the checked compositional sign24 degree upper
bound to the sign23 seed, which has one fewer residual and one fewer witness.
The proposed theorem bounds the actual Lean direct expression's polynomial
total degree by eight for every integer port vector, then specializes to the
current ports. The finite residual checks retain scoped 4,000,000-heartbeat
settings; other guard limits are unchanged.

The source is uncompiled. A matching lower bound, external JSON/port-byte or
PDF binding, and a Jones reduction do not follow from an upper bound.
Independent prelaunch review and an assigned Lean slot are required.
