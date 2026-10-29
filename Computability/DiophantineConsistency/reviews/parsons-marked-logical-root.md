# Remaining ordinary marked principal rules

`ParsonsMarkedLogical` implements the ordinary principal disjunction,
conjunction, and existential rules with an arbitrary marked nonprincipal
context. Each constructs the exact marked premise entries, obtains their Π₂
certificates from the principal side formula, and invokes explicit local
recursive hypotheses on cut-free derivations strictly below the enclosing LK
inference. Existential inversion is proved for Foundation's non-prenex Π₂
hierarchy before specializing the witness. Together with
`ParsonsShift.marked_universal`, these give the four ordinary logical
constructors when the principal occurrence is tagged as a Π₂ side.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`. Both objects and complete logs match. Five
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-marked-logical-replay/FILES.json) has SHA-256
`95cf1b340c009ac1f18ca4ca5b503913fff221b05b80b0770f2fcedd6520f1d7`.
Direct `ParsonsShift` source/object hashes are
`cae209be8847f09d58ee5b142114a6fecf3d42f2230879f8ecb779c7f1a537f0` /
`cb5b43c8187cc894279de8f2a18c174e75e82c8db7407c77b6b22b709368f437`;
`ParsonsLogicalCases` hashes are
`f00188fca71f773461419202fc212f99f036d42dc5ce6e171b6bb7f758266b68` /
`2695c7fcf17dcf3deb0758c2577277dcb60374adfec0ca5a5a1532db8fe525e5`.
Their earlier provider chains, Foundation/Mathlib, and completeness objects
remain an inherited boundary, not a fresh transitive audit.

These are not a complete strong induction. A principal rule can also act on
a marked negative PA-minus axiom: some such axioms are Π₂, so their negations
cannot uniformly be reclassified as Π₂ sides. Partial decomposition of these
base entries needs its own invariant. The final induction-block case still
requires a Σ₁ guard, whereas an arbitrary marked output is only certified Π₂.
No global conservation or PRA witnessing theorem is claimed.

## Independent root replay

A third build at `/tmp/parsons-marked-logical-build-endfymou` passed; source,
object and complete-log hashes match both author runs. Both direct providers
match independently rebuilt objects. The [independent artifacts](parsons-marked-logical-replay/root-build/)
are preserved; Foundation/Mathlib remains an inherited boundary. The source
disables the `flexible` linter locally for `pi_body_of_exists`; it does not
disable proof checking.
