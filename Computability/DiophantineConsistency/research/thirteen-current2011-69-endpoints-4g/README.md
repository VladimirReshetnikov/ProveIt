# Fresh 13/69 standard and translated endpoints

This client imports the fresh checked 13/69 completion/bridge provider and
checks two standard iPRA derivability statements for the positive-shifted
`expressionAt69` at `CurrentWindowCarry2011.ports`. The first is the existing
biconditional with negated mapped native ZFC refutation; the second composes
that statement with `IPRABoundedRhoZFC.zfcEquiv` to obtain the mapped
Gödel–Gentzen translation of the formal ZFC consistency sentence. These are
Lean theorems about represented internal proof existence. The separately
checked [graph](../thirteen-current2011-69-174/README.md) is connected by an
external source-level comparison, not by a Lean JSON parser.

Actual outer session 74499 exited 0, and both nested Lean runs exited 0.
The retained [compile log](attempt01/compile.txt) reports exactly `propext`,
`Classical.choice` and `Quot.sound` for each endpoint. The
[state](attempt01/state.json) SHA-256 is
`d06d30d141b4d68ad01b6e635700c7c570e6b43232eba64f77bfb35e0ea4c3a1`;
the object SHA-256 is
`876ed4ed0ef309ec8d22ded066e716c06c6e2321324a21a7418962367b296aaf`.
The source SHA-256 is
`86daa6a753c70336455ced8a2be6ac7883e478e071a3d284763e3f3448c72203`;
the runner SHA-256 is
`dedef3db90ea928df6cd0307f372651c2b2eed7a4dcb310324b1eee894cb0061`.

The guarded run rechecked the fresh completion's source/object/logs, outer
exit, direct guards and isolated provider links. Compilation took 2.223
seconds, with peak sampled session RSS 2,865,975,296 bytes, minimum sampled
host available memory 18,838,781,952 bytes, and no sampled stop, descendant
or monitor error. Resource limits are sampled; transient spikes, escaped
descendants and complete dynamic/package-transitive ancestry remain outside
scope.
