# Finite graph objects before Infinity

`FiniteSets.lean` supplies pairs, singletons, unions, binary union, insertion,
von Neumann successors and Kuratowski ordered pairs from Extensionality,
Pairing and Union. Its base inherits actual formula-indexed Separation from
`SingletonInfinity.Base`; the elementary constructors do not use that field.
There is no Infinity, Foundation or object-level Choice premise.

The operator and ordered-pair injectivity proofs adapt the existing local
`SetTheory/ZF/Lean/ZF/Zf.lean` proofs while reducing their bundled hypotheses.
The singleton is exactly `SingletonInfinity.singleton B.toBase`, so the
singleton index and graph construction share the same successor operation.
`kpair_inj` requires no Foundation. `insert_spec` gives the union of the old
graph and one graph point, and `succ_spec` gives precisely x∪{x}.

The literal `pairForm`, `kpairForm`, `appForm` and `succForm` macros each have
checked satisfaction lemmas. Input slots are absolute de Bruijn indices;
all added quantifiers shift the retained parameters. In particular,
`appForm f x y` says that the represented graph in slot f contains the
Kuratowski pair of slots x and y, and `succForm i j` says that slot j is the
von Neumann successor of slot i. No atomic graph oracle is assumed.

The actual CP/GIC quotient supplies `FiniteSets.quotientBase`. The subsequent
[finite-attempt construction](inductive_attempts.md) instantiates these atoms
and finite graph operations to obtain ordinary Infinity noncircularly.

Pinned Lean4.32 compiled this source in the scoped integration in0.453seconds;
its ordered-pair and atom audits use at most the standard `propext`,
`Classical.choice` and `Quot.sound`. Independent full-source review checked
the finite operators, injectivity and binder shifts. Initial development
needed explicit base arguments for two rewrites and the current structure
syntax; the final source has no warnings or admissions. Commands and source
identity are in `results/infinity-l2-integration-verification.json`.
