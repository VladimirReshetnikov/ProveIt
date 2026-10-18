# Native models of the original decoded numerical bundle

`NativeDecoded254.lean` proves an explicit sufficient interface for the
original four-tag calculus:

```text
ProfileCollection.Containers mem
+ GIC for every actual native SetTheory.Form and every parameter valuation
+ ∀x, ¬mem x x
⇒ Code254Models.ModelsDecoded mem.
```

The GIC premise includes native equality; equality-free CP/GIC by itself
is insufficient here. The new `FullGIC` definition states the actual
`gicForm` schema. It adds no collection principle for arbitrary semantic
relations. `matrix_instance` requests exactly
`NamedForm254.matrix (Code254.dec c) a b`, so every matrix is an actual
finite formula even when its code has zero children or native Eq atoms.
No assumption that the code is in the named encoder's image occurs.

`sat_dec_bundle_named` identifies decoded satisfaction with the exact
named C/G/vacuity tree by the existing constructor-semantic lemmas.
This is a semantic comparison, without the false claim `enc(dec c)=c`.
Global raw IR validates the relative-falsity atom under every binder,
including a binder of label0. Neither the falsity alias nor decoded truth
zero is treated as a syntactically closed genuine Bottom constructor.

Both machine gates `c ≠ a` and `c ≠ b` remain in the final theorem. The
proof also retains the allowed case `a=b`:

- For C with distinct input/output names, raw CP supplies exactly the
  container, its transitivity and its raw-subset power bound. When a=b,
  the guarded universal clause tests `mem x x` and is vacuous by IR;
  CP still supplies a container containing the original root at c.
- For G with distinct input/output names, native GIC supplies the matrix's
  global support and domain cover. The support clause reverses input/output
  update order, so `support_matrix` commutes only those distinct updates.
  A selected output overwrites the prior output binder. The original
  own-code update is ignored only by the all-code semantic freshness lemma
  from `DecodeFresh254`; this includes c=0 truth and nested zeros.
- When a=b, the cover guard again tests `mem x x`. A false-matrix GIC
  instance supplies an empty output, making support vacuous. Applying a
  distinct-name matrix argument to this case would be wrong.
- Membership and equality vacuity follow exactly from the two gates,
  without requiring a≠b.

`modelsDecoded` is universal over the valuations in the interface and
therefore requires no separate inhabitant. `no_refutation` supplies an
actual valuation when invoking numerical soundness, so it cannot exploit
an empty-domain premise. In particular it proves
`¬Code254.C254 Code254.F` from a supplied native model and valuation.
It proves neither the existence of such a model nor a consistency bridge.

The existing `Code254GIC.collection_of_matrix` already supplies every
native Form instance from `ModelsEncodable`, even though the old
`modelsGIC_of_encBundle` conclusion exposed only its EF restriction.
`fullGIC_of_encodable` retains that full conclusion. Combining it with
`containers_of_encBundle` proves `decoded_of_encodable`. The existing
`encodable_of_decoded` gives the other direction, so
`modelsDecoded_iff_modelsEncodable` closes the exact theory-model interface
gap on an irreflexive structure with a supplied valuation. This uses no
quotient and proves no existence or consistency comparison.

The actual quotient separately has CP and full native GIC by `QuotientCPGIC`.
Using that quotient here still requires its **own** IR proof. The fifth
caller states that condition explicitly; raw IR is not transported through
bisimilarity. The separate ordinary target-permutation obstruction note
explains why that distinction matters. Foundation/Choice transport,
model existence, the opposite consistency implication and the final
binary-machine simulation remain outside this module. No table changes.

The206-line source compiles with the explicit pinned Lean4.32.0 compiler
in0.46seconds. Fourteen theorem axiom audits and six callers pass in0.36seconds.
Only `propext`, `Classical.choice` and `Quot.sound` occur; no admissions or
custom axioms occur. Callers fix matrix codes0,35 (Eq1,2) and4 (nested
zero), exercise both colliding/distinct binders, compose the actual
quotient interfaces with a separately supplied quotient-IR hypothesis,
and feed completeness's EncBundle class into numerical soundness via
the newly proved decoded-model adapter.
Binder labels remain general in these caller statements to avoid expanding
an enormous closed numerical bundle during elaboration. A first source
check needed only unfolding the definition of raw Sub in a simplification;
no hypotheses or statement were changed. Commands, caller source and full
axiom output are in `results/native-decoded254-verification.json`.

An independent full source review found the binder collision, gate,
freshness and valuation scopes correct. The native equality and all-code
freshness interfaces were separately checked in their existing modules.
