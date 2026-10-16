# From encoded bundles to the existing container resource

`Code254Containers.lean` isolates the first model adapter for the original
four-tag numerical calculus. In an irreflexive model of every
`Code254.EncBundle` formula, with an explicit valuation, it derives
`ProfileCollection.Containers`. The fixed instance uses
`(a,b,c) = (2,3,1)` and matrix `Rel(0,0)`, whose encoding is exactly `1`.
Both gates, `1 != 2` and `1 != 3`, hold. Its complete C/G/vacuity conjunction
is an actual `EncBundle` formula; C is projected semantically under global
irreflexivity. The proof retains all nested variable updates and obtains
the transitive container and its raw subset bounds. No large closed numeral
needs evaluation: a generic constructor identity proves the encoding.

This is a finite adapter, not the full GIC interpretation or a consistency
endpoint. Supplying `Nat → V` makes nonemptiness explicit and avoids the
historical empty-domain error in the first `Code254.c254_complete` premise.
The new module follows the named trees in upstream `Codes254.v` and
`Bundle254.v`, pin `297ab8df7e5de329605c3875b4934643b371a5e3`, and the
container-instance argument of `Comp_Bundle254.TB_CP`. That proof uses the
equally valid labels `(1,2,3)` and matrix `Eq(0,0)`; our chosen instance
uses only membership in its matrix. Attribution does not relicense the
upstream snapshot.

## What this connects

`Code254.c254_sound` assumes all decoded gated bundles in an irreflexive
model. Its corrected `c254_complete` has a different hypothesis: no
irreflexive model with a valuation of the literal encodable bundles. The
new adapter works on the latter theory. It neither equates those theories
nor assumes that every decoded natural is the literal encoding of an
ordinary named formula.

The current semantic path is:

1. EncBundle model plus IR and valuation gives Containers, by this adapter.
2. A remaining GIC syntax adapter should give
   `ProfileModel.ModelsGIC`, hence `ModelsCPGIC` together with the container
   satisfaction theorem in `ProfileModel.lean:32`.
3. `ProfileModel.lean:137` supplies profile pairs and bisimulation
   reflexivity/symmetry; `CompositionModel.lean:100` supplies transitivity.
4. `QuotientModel.lean:164` supplies quotient satisfaction, and line 200
   supplies quotient Extensionality. This is not yet a theorem that the
   quotient satisfies every ZF axiom.
5. `ProfileAxioms.lean:127,185,221` give Separation, Power and Replacement
   under explicitly named invariant relation instances;
   `PowerSyntax.lean:41` supplies one actual matrix instance. Uniform
   formula-indexed adapters for the other resources and the complete
   quotient axiom theorem remain separate. The singleton-closed-container
   infinity lemma at `ProfileAxioms.lean:242` is not already the usual
   von Neumann inductive-set axiom.

These equality-free models suffice for a one-way bridge out of EncBundle:
EncBundle allows native equality in matrices, so it supplies at least the
equality-free instances needed by this interpretation. Conversely, merely
assuming `ModelsGIC` for equality-free matrices does not establish all
decoded bundle instances with native equality.

## The next GIC adapter and its gates

The existing schema uses de Bruijn `SetTheory.Form`: input slot 0, output
slot 1 and parameter slots `2+k`. The numerical frontend uses named `NF`
and natural binder labels. A useful next theorem is:

```text
irreflexive mem → valuation → models EncBundle mem
  → ProfileModel.ModelsGIC mem
```

It needs a hygienic `Form → NF` conversion with a checked satisfaction
equivalence. Preserve slots 0/1 and the parameter environment, and choose
each bound name outside the finite support of the current free-name map.
`Form.bound`, `free_lt_bound` and the existing environment-update lemmas
provide the elementary resources. Expand conjunction, disjunction and
existence using implication and genuine Bottom, then replace Bottom by
`Rel(0,0)`. Global IR makes this replacement semantically correct even
under binders of label 0; no reserved-point argument is being assumed.

For a resulting Bottom-free matrix f, prove:

```text
0 < enc f
Occurs i f → i < enc f
```

The second statement includes bound labels. Both follow structurally from
the pair bounds. Choosing `c = enc f` then makes c fresh for the whole
matrix. It does **not** by itself prove the two gates for fixed input and
output names: f can be `Rel(0,0)`, with code 1 equal to output label 1.

One uniform repair is `pad f := (f → f) → f`. It is equivalent to f in
every structure and preserves Bottom-freeness. Its code is greater than
the positive code of f, hence greater than 1. With names `a=0`, `b=1`
and `c=enc(pad f)`, both gates hold and c is absent from all matrix
labels. This padding selects existing numerical schema instances; it
changes no literal machine or state count. The exact named G tree in
`Code254Containers` is already available for that next proof.

Do not replace the definable schema by collection for arbitrary semantic
relations. The satisfaction conversion must recover each requested
`MatrixRelation` and its parameter environment.

## Zero alias and the upstream proof boundary

Upstream `Wff254.v:19` chooses a **closed** truth formula for `D 0`.
Its `Sound254.D_fr_self` therefore holds at zero as well as positive
codes. Current `Code254.dec 0` is `Rel(0,0) → Rel(0,0)`, a tautology with
syntactically free label 0. Thus the literal assertion
`not Free c (dec c)` is false at c=0 in this decoder. A blanket port of
the upstream syntactic freshness claim would be wrong.

For the soundness direction, prove positive-code label bounds and treat
zero separately by semantic invariance of the tautology, or deliberately
choose a closed truth representative and update its proofs. For the
EncBundle-to-GIC direction above, every selected matrix is an ordinary
positive encoding; no arbitrary-natural inverse or zero normalization is
required.

Upstream `SoundBW254.V_BW` explicitly splits `a=b` from `a!=b`. When
names collide, IR makes the `x in x` antecedents vacuous and the false
GIC matrix supplies an empty output set. This case must be retained when
establishing soundness of **all** machine bundles. The new fixed container
instance has distinct labels and does not claim to discharge that case.

## Pinned upstream and current Lean scope

The reusable upstream proof chain is precise:

- `Comp_Bundle254.v:97,114,122,128,208` proves occurrence/code bounds,
  exact named-bundle encoding, gated bundle derivability, CP and all closed
  GIC instances. Its GIC conversion uses odd free labels and a fresh
  additional universal binder, rather than treating a code number as
  automatically distinct from arbitrary input/output names.
- `SoundBW254.v:112,127,181,216` handles the collision cases, the distinct
  collection case and the whole bundle. `Sound254.v` supplies decoder
  freshness and the relative-falsity semantic comparison.
- `S_quot.v:94,135,168,261,341` proves bisimulation equivalence,
  Extensionality and formula invariance. The existing Profile/Quotient
  modules mirror these semantic resources, with equality-free profile
  coding rather than silently assuming raw Extensionality.
- `S_ax.v:214,257,303` proves translated Separation, Replacement and
  `ZF0 + INF_lib`; `S_main.v:23,35,41` joins the refutation comparisons.
- `S_sound.v:65,226,267,301` proves the source axioms in the constructible
  interpretation and transfers source refutations to ZF. Neither a model
  of bare Extensionality nor a local container lemma replaces this work.

The independent numerical relations `Numeric254.NumThm` and
`Code254.C254` have the same twelve constructors and the same nineteen
nonpair constructor expressions. A scratch Lean proof checked their
pairing equality by triangular-number induction. A small future bridge
can prove `NumThm n ↔ C254 n` by induction on the twelve constructors,
using those definitional identities and the pairing equality. This avoids
maintaining two independently assumed code calculi, and lets the numerical
proof adapter and semantic decoder share results. It is not needed for
the container extraction itself, and is not added as a claim here.

No code/table reduction or ZFC endpoint is asserted by this note. The new
module compiles with the explicit pinned Lean 4.32.0 compiler in 0.42 seconds.
All eight theorem axiom audits and a caller with an explicit inhabitant pass;
the two encoding identities use no axioms, and the main adapter uses only
`propext`, `Classical.choice` and `Quot.sound`. Reproducible commands and
scope are recorded in `results/code254-containers-verification.json`.

The subsequent [GIC adapter](code254_gic.md) now completes steps 1–2 above,
using odd free names and even bound names, with selected input/output names
1/3. Its padding proves both actual gates. The
[numerical calculus bridge](numeric_code254.md) also proves the all-code
`NumThm ↔ C254` identification proposed above. The quotient-ZF and decoded
soundness obligations retain their separately stated scope.
