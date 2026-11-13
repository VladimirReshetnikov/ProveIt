# Sign24 compositional degree residual-check retry

The first structured attempt checked the generic and structural lemmas, but
its residual stage failed because `simp [degree]` did not unfold overloaded
Expr arithmetic. This source-only retry changes only the finite residual proof
steps to kernel `decide`, so each concrete syntax tree is reduced separately;
the scoped heartbeat option and all runner limits are unchanged. `decide` is
not `native_decide`; no new axiom is introduced. The proof remains uncompiled
and may encounter additional errors or resource limits.

The proposed result is the actual Lean sign24 expression's polynomial degree
at most eight for arbitrary integer ports and current ports. Exact degree,
external JSON and coefficient-byte correspondence and PDF semantics remain
separate. Independent prelaunch review and an assigned Lean slot are required.
