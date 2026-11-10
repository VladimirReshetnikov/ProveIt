# Sign24 Lean degree upper-bound local-heartbeat retry

The first attempt checked the generic expression degree bound but its concrete
reflexive syntax-degree calculation hit the default 200,000-heartbeat limit.
This source-only retry adds `set_option maxHeartbeats 4000000 in` **only** to
the concrete syntax-degree theorem; other declarations keep the default. The
sign24 seed syntax itself already uses a 4,000,000-heartbeat option, so this
is an explicit narrow retry at the established syntax limit rather than a
global runner change. All resource, time, provider and no-sorry guards remain
unchanged. The resulting source is uncompiled and may still time out.

Even if successful, the exact polynomial lower bound, external JSON and port
byte correspondence, and PDF semantics are not established. Independent
prelaunch review and an assigned Lean slot are required before the run.
