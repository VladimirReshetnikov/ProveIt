# Positive affine-carrier helper

The checked fixed-port-free lemma takes a positive model `b`, a positive ring
transport `G` factored as `ι b * g`, the signed residue witness, and the
auxiliary size bound. It constructs a positive ring carrier satisfying the
same signed affine equation used in the thirteen-variable completion proof.
This is a conditional algebraic helper, not the completion or iPRA endpoint.

Actual outer session 68312 exited 0; both nested Lean runs exited 0 and the
explicit axiom report contains only `propext`, `Classical.choice`, and
`Quot.sound`. The [state](attempt02/state.json) SHA-256 is
`4abd80dfee0afc2be06d8f27576e88e7558b724af2c0ec311dfcef247d058c6f`;
the output object SHA-256 is
`d362bdd5b7b7d720b5443f58612468d921e23e2c08f479f3ba6ea34340b31cf8`.
The source SHA-256 is
`eea57a6e0eaf7d8bc58bcd3e0756a719ff26b35782f164af0ce33a3baf10138e`;
the runner SHA-256 is
`96d1a2ccb3a4dd5a92153ad8cb1e07016c990a375cb3500929342c1165644729`.
The earlier [failed attempt](../thirteen-current2011-affine-carrier-draft/README.md)
is preserved; this revision changes only the namespace opening needed for
`modelFacts`.

The run checked the model prelude, generic core, seven captured predecessors,
direct guards and isolated overlay around the check. It used `-M2800`, one
worker, a 180-second GNU foreground timeout and resource prechecks, without
automatic group-RSS or host-memory stopping or a complete dynamic/transitive
provider trace.
