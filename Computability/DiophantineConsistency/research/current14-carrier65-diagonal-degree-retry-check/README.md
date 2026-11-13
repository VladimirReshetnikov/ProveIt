# Diagonal degree transport: type-annotation retry

Outer session 50189 exited 1: the final proof used incompatible syntactic
forms for its intermediate bounds, and no object or postflight exists. The
[independent failure review](../../reviews/current14-carrier65-diagonal-degree-retry-failure-independent/)
passed. This retry adds the missing `Polynomial ℤ` coefficient type in the final
generic transport statement. The no-Lean preflight and [independent prelaunch
review](../../reviews/current14-carrier65-diagonal-degree-retry-prelaunch-independent/)
passed. The audited failed attempt, its missing object,
and direct point providers remain pinned. The proposed result is generic
diagonal degree transport only, not the actual diagonal's degree.
