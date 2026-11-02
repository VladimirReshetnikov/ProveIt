# Generic kernel-shape identity and failed closed link

`oldAt_eq_param` proves the old-shaped finite-sum expression equals `paramKernel r` for an arbitrary natural radix r. Lean session 39958 actually exited 0 and reports `[propext, Classical.choice, Quot.sound]`. This is a single-side exploratory check over the earlier symbolic-kernel overlay, not a paired or independently audited result.

The separate attempt `kernel_eq_oldAt` exposed the old definitions, generalized the radix and tried to close the equality. Session 73654 actually exited 1 at the 3,000 MB Lean kernel limit; the log's self-referential axiom report is a failed declaration, not a proof. The old closed kernel and parameterized expression have therefore not been proved equal. No raw-byte or displayed-expression binding, graph semantics or iPRA conclusion follows from the generic identity.
