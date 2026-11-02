# Symbolic-port specialization: exploratory

The single-side exploratory theorem `CompactSymbolicPorts.graph_digits` constructs its four natural ports from beta, an explicit arbitrary natural `K`, and the two symbolic finite-list masks. It thereby removes the two symbolic mask port-equality assumptions from the preceding conditional graph-digit theorem. The statement still assumes graph zero, positive variables and beta, both port inequalities, beta at least 46, the radix and repunit equations, and the high-mask product bound. The generic intermediate retains natural low/high equalities; the specialized wrapper supplies them by reflexivity.

Actual single-side Lean session 10245 exited 0 without warnings and reported `[propext, Classical.choice, Quot.sound]` for both the generic and specialized theorems. The earlier direct tuple attempt exited 134 at Lean's 3,000 MB memory limit; the generic-entry intermediate passed. Their sources and observed outputs are retained under `observations`. The provider is an author-side exploratory symbolic-join overlay, not a paired audited provider, and this packet is not a paired replay.

`K` is arbitrary: this applies to a fixed K only after choosing that value and does not identify it with retained K bytes or a decimal literal. No equality of the symbolic masks to retained coefficient bytes, machine simulation, or PRA theorem is claimed.
