`EqualityGIC.lean` supplies a conditional finite adapter for the equality
obligation exposed by `DuplicateProfiles`. Its extra hypothesis is
outgoing-profile faithfulness:

```text
∀x y, (∀z, x∈z ↔ y∈z) → x=y.
```

The module gives this condition both as the semantic `Faithful` interface
and as one actual `faithfulForm` sentence, with checked satisfaction.
This compares receiving sets, rather than asserting incoming-profile
Extensionality. The hypothesis is explicit throughout. Equality-free
CP/GIC alone is not claimed to supply it.

Under `Faithful`, native equality x=y is represented by the equality-free
formula ∀z(x∈z↔y∈z). `equalityForm i j` shifts both free endpoints under
its new local De Bruijn binder. `eraseEquality` recursively applies this
replacement to every native equality atom and preserves all seven other
`Form` constructors. Its satisfaction theorem holds for every formula and
valuation. The translated formula is equality-free, including when the
original formula has native equality under further quantifiers.

`collection_of_matrix` applies the original, actual `ModelsGIC` schema only
to the literal formula `eraseEquality phi`. The satisfaction theorem then
transfers that collection instance to the matrix defined by phi.
`modelsFullGIC` consequently supplies GIC for every actual `Form` and
parameter valuation. This remains a formula-indexed schema; the proof
does not postulate collection for arbitrary external semantic relations.

Literal singleton existence is a sufficient finite set-construction
resource for `Faithful`: test the outgoing profiles of x,y at the singleton
of x. Ordinary native-equality Pairing supplies these singletons by pairing
x with itself. Both implications are proved. Neither CP, IR, a domain
witness, an internal omega nor a complete ZF model is needed by this
conditional adapter. No implication from ZF0 to GIC is assumed.

The construction uses the same outgoing membership direction as
`OutgoingProfile.outgoingForm`, with both directions expressed under one
biconditional binder. It does not use RawPSC's twin-singleton resource or
identify its full observational equivalence with raw identity. Native
identity here is obtained precisely from the additional `Faithful` premise.

Pinned absolute Lean 4.32.0 checked the source on its first attempt in
0.336 seconds and nine theorem axiom audits plus three caller examples in
0.298 seconds. Seven audited theorems are axiom-free; the two collection
transfer theorems depend only on `propext`. There are no admissions,
custom axioms, `Classical.choice`, `Quot.sound`, or `native_decide` dependencies
in these audited theorems. Both independent reviewers found the formula
bindings and hypothesis boundaries sound.

The callers check full GIC from explicit Pairing plus equality-free GIC,
the same result from the literal faithfulness sentence, and composition
with `NamedForm254.sat_matrix` for arbitrary named formulas and input/output
labels. Even that last composition establishes collection instances rather
than the full numerical bundle: the original gates, relative falsity,
degenerate equal input/output names and all-code freshness remain separate
numeric adapter obligations. No proof-code translation, Foundation/Choice
consistency bridge, enumerator or binary-machine endpoint is proved here.

The scoped check reused the source-verified 84-module cache at
`/tmp/zfc-zero331-integration-4hq283ka`; no full closure or bootstrap was
rebuilt. Exact commands, source/dependency hashes, caller source and complete
axiom output are in `results/equality-gic-verification.json` and
`/tmp/zfc-equality-gic-0vtdqkel`.
