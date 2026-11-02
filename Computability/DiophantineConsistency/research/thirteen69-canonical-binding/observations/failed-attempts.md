# Exploratory binding attempts that did not succeed

The initial direct literal-row proof used `simp` followed by a global `ring`
expansion ([source](expand-full-ring.lean)). After a failed attempt to import
`ModelDifferenceRing` from a shadowing overlay (actual exit 1), the same
proof was retried with a correctly linked coherent parent. It exhausted Lean's
`-M2400` memory limit, with actual exit 134; the tool printed a
`lean::memory_exception` and `timeout: the monitored command dumped core`.
It is not a successful compilation or evidence for the theorem.

A second attempt used global associativity/commutativity simplification
([source](expand-ac-simp.lean)). After observing approximately 1.96 GiB RSS,
we stopped its `timeout` supervisor; its actual exit was 143. Its theorem was
not established. This is a manual termination, not a reported timeout or proof
failure. Neither full command transcript was retained beyond these observed
terminal results. The successful canonical theorem uses a structurally aligned
expression and does not purport to close the 69-row comparison.
