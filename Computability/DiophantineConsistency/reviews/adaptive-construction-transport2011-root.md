# Reverse adaptive transport from the maintained equation system

`adaptive_transport_cut` proves, over each selected IΣ₁ model, the algebraic
transport identity needed for the adaptive graph from the old transport
equation, a gap decomposition and the two displayed subtraction-cancellation
identities. `adaptive_transport_of_equations` supplies those conditions from
the actual positive 14-coordinate equation system, deriving the positive gap
using the existing first-index scalar-window lemma. The result is one piece of
the reverse witness map; it does not construct the other adaptive coordinates,
prove the adaptive polynomial vanishes, or establish a converse.

Two fresh root builds against the independently replayed adaptive window
provider `/tmp/adaptive13-window-client-gl1jcjjp/lib` passed with identical
source, object and complete-log hashes. Both axiom reports contain `propext`,
`Classical.choice`, and `Quot.sound`. The [drivers, snapshots, logs, provider
inventories and states](adaptive-construction-transport2011-replay/) are
preserved. Initial exploratory attempts had a subtraction rewrite error and
a missing positivity argument; their terminal output was not retained in the
packet. Foundation/packages and inherited project objects remain cache
boundaries, not a fresh transitive source audit.

A subsequent upstream merge changed `ArithmeticCarrierRadix2011.lean`. This
receipt authenticates the earlier dependency snapshot; the affected
source-current downstream replay is pending.
