# Direct conditional exact degree: function-equality retry

Outer session 79666 exited 0: the direct conditional polynomial exact-degree
theorem compiled. The [independent terminal audit](../../reviews/current14-carrier65-degree-direct-retry-terminal-independent/)
passed. This retry replaces the failed simplifier step in `diagonal_value` by
explicit function equalities for the mapped port and variable assignments.
The theorem statements and other proofs are unchanged. The upper-bound source
is replayed exactly; the audited direct-attempt failure and its missing
object, both earlier import-collision failures, and provider points are
pinned. No-Lean preflight and [independent prelaunch review](../../reviews/current14-carrier65-degree-direct-retry-prelaunch-independent/)
passed.

The intended conclusion is exact total degree 150 for `Carrier65.polynomial`
under p0 nonzero. Current-port and expression specializations remain separate.
