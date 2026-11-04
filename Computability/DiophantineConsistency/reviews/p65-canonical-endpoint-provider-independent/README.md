# Independent audit of the canonical P65 captured-provider replay

This is an audit of the recorded replay and its scope, not a new Lean build.
The current canonical endpoint source SHA-256 is
`675eafadc49f1248e80a965d834b702d073eafda4c0aff5f0cc84f1fb1c9d7f1`;
the replayed endpoint source is byte-identical to it by an independent `cmp`.
The endpoint object hash is
`67ee78d4c54c3bd0baa2b3734a4d11a70d3b199557839b08b4faa1cad1adfb19`.

The final compiler log records exit 0 for `IPRAPositive65.lean` and reports
`[propext, Classical.choice, Quot.sound]` for `positiveBridge` and the native,
standard and equality-only iPRA equivalence declarations. In the source these
are unconditional Lean theorems for the positive-shifted fixed-port package-65
graph and the repository's mapped Foundation refutation predicate. The
separate alternate-endpoint review checked the identical graph expression and
port definition; neither replay alone establishes external artifact identity.

I independently reran the supplied read-only manifest checker and audit. They
reported 30 source shims, 24 captured direct-object bindings, the shared graph
shim, and 30/30 final objects. The repository and temporary manifest hashes
both equal `bb0488e85aa2d8a2c3ba6943cddcb208a1b1e9704913ec6ba6d2cc82e3894a00`;
the corresponding results hashes both equal
`4c19cd870cce5cb41e12be93f0b0ddc3b3eca4010bdf6e86a737db2c0cfe7044`.
The manifest checker compares each canonical source with its generated shim
after the declared import substitutions, and checks selected provider-object
hashes. The shared graph shim is the same object as in the reverse provider.

The check is a captured-provider replay layered on the 62-module reverse
provider, not a clean rebuild of the full current source tree. The selected
direct objects are hash-pinned but their complete transitive source/object
ancestry was not established by this audit. The recorded cached replay checks
existing hashes; it is not a second compilation. The absence of printed
unexpected axioms and placeholders is evidence about these compiled objects,
not independent verification of all imported theorem bodies. Separate
artifact-correspondence checks are required for JSON, TeX, or PDF claims.
