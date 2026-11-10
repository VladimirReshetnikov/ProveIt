# Sign24 N0 specialization Fin-index retry

The first lower-bound attempt failed because generic simplification left Fin
index tests unresolved in the N0 axis identity. This source-only retry adds
five reflexive local equalities for the exact finite indices used by N0,
then simplifies with those equalities and invokes `ring`. The row identification
and generic diagonal-degree source are unchanged. The retry is uncompiled and
may expose additional issues. It does not yet prove the full degree lower
bound, or bind JSON, coefficient bytes or PDF semantics. Independent
prelaunch review and an assigned Lean slot are required.
