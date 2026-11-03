# Trace75 K2 root extraction

`Trace75Root.roots_of_representatives` is checked for arbitrary difference-ring
ports in every `IΣ₁` model. For a zero of the Lean trace75 ring value, it
assumes positive natural representatives of the graph registers Δ, U, E and M
and natural square representatives of the signed V and Z registers, with the
representative of V positive. It concludes positive `tau,f0` with
`E=tau*tau` and `1+Delta*U*U*E=f0*f0`. The generic internal gcd and square
extraction are reused from `TenPositiveProductRoot.doubled_product_roots`;
ring rewrites use the actual trace75 register identities, and `ring` acts on
registers as atoms.

This conditional result does not establish the required representatives from
positive graph witnesses, a halt bridge, the direct-BFS tuple identification,
a 74 guard, or an iPRA equivalence. It uses the Lean source for trace75 and no
formal JSON/file correspondence.

The accepted source `Trace75Root.lean` SHA-256 is
`bbf09b1f041ddd25c0c4c72c9c46738b51d6ee8964ec423d37c22943aeeba296`.
`run-v2.py` accepted `observations/root-attempt02/`; its object
`/tmp/trace75-root-wxe5rr8_/Trace75Root.olean` SHA-256 is
`bf8d56a7526a5324d04c7178d8265e619a15aa624d117d11ba8b864831624958`.
Its `#print axioms` output is `[propext, Classical.choice, Quot.sound]`.
The first source and failed attempt are retained as `run.py` and
`observations/root-attempt01/`. The runner records/pins selected direct
provider objects and enforces the 8-GiB/two-Lean-process guard. It creates a
fresh symlink overlay to combine the separately compiled trace75 provider
with the pre-existing project library. Project, package and dynamic transitive
ancestry remain inherited; this is not a complete selected-closure audit.
