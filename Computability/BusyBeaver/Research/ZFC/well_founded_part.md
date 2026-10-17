# A direct well-founded-part closure argument

This route uses the additional formula-indexed GIC resource already proved
in `QuotientCPGIC.lean`. It avoids choosing canonical transitive witnesses,
and does not infer Collection from functional Replacement in a theory
without Foundation. The elementary definitions follow the attributed
well-founded-part interpretation in
`lib/jeff-busy-beaver-zfc254/ZF/stdzf_r3/regcon/WF.v`, at upstream pin
`297ab8df7e5de329605c3875b4934643b371a5e3`. The direct GIC witness
collection is a different hypothesis interface from that file's canonical
witness/Replacement proof.

This note first gives the ordinary proof and its exact object-theory
resources. `WellFoundedPart.lean` is the corresponding checked Lean
checkpoint. The checkpoint supplies neither all interpreted ZF axioms nor
a Foundation refutation transport. Choice remains a further comparison.

Let `mem` be the membership relation of an arbitrary first-order structure.
All sets and quantified subset witnesses below are objects of that
structure. Define

```text
Sub(s,t)     := ∀z (z∈s → z∈t)
Trans(t)     := ∀x∈t Sub(x,t)
Nonempty(s)  := ∃x x∈s
Min(m,s)     := m∈s ∧ ∀z (z∈m → ¬z∈s)
Wellf(t)     := ∀s (Sub(s,t) → Nonempty(s) → ∃m Min(m,s))
TW(t)        := Trans(t) ∧ Wellf(t)
WF(x)        := ∃t (TW(t) ∧ x∈t).
```

`Wellf` asserts the minimal-element property for every **represented**
nonempty subset. It does not assert external well-foundedness of `mem`,
nor quantify over arbitrary external subsets. This distinction matters in
nonstandard models.

The precise set-existence resources for closure are Pairing, Union,
Separation for the single membership matrix `Mem(0,1)`, and GIC for the
single parameter-free matrix

```text
R(x,t) := TW(t) ∧ x∈t.
```

The formula contains no equality, so equality-free GIC already suffices.
Full native-Form GIC in the actual quotient supplies it immediately.
Neither Infinity, Power Set, Replacement, Regularity, raw irreflexivity nor
object-theory Choice is used in this closure argument. The Lean finite
base also exposes Extensionality and all actual-Form Separation, as
existing reusable interfaces; its proof below instantiates Separation only
with `Mem(0,1)`. It never assumes Separation for an external predicate.

## A set meeting a TW set has a minimal element

Suppose `TW(t)` and some `x` belongs to both `s` and `t`. Form
`b={z∈s : z∈t}` by the stated Separation instance. This is a represented,
nonempty subset of `t`, so `Wellf(t)` supplies `m∈b` with no member in
`b`. In particular `m∈s` and `m∈t`. If `z∈m` and `z∈s`, transitivity of
`t` gives `z∈t`, hence `z∈b`, a contradiction. Thus `Min(m,s)`.

No hypothesis `s⊆t` is needed for this lemma. The intersection makes the
subset required by `Wellf(t)`, and transitivity lets its minimality extend
to the whole represented set `s`.

## A union of TW sets is TW

Suppose every member of a represented family `c` is TW. Let `u=⋃c`, using
Union. If `x∈u` and `z∈x`, choose a witness `t∈c` containing `x`.
Transitivity of `t` gives `z∈t`, hence `z∈u`. Therefore `u` is transitive.

For a represented nonempty `s⊆u`, take one `x∈s`. There is a `t∈c` with
`x∈t`. The preceding intersection lemma gives an `s`-minimal member.
Thus `Wellf(u)`. These are successive existential eliminations from the
given witnesses, not a function selecting an element or witness for every
member of a family. No Choice axiom is needed. The empty family causes no
special problem: there is then no nonempty subset of its union.

## Adjoining a set whose members lie in a TW set

Suppose `TW(u)` and `a⊆u`. Pairing and Union form `w=u∪{a}`.
For `x∈w`, either `x∈u` and its members lie in `u`, or `x=a` and its
members lie in `u` by hypothesis. Hence `w` is transitive.

Let `s` be a represented nonempty subset of `w`. If `s` meets `u`, the
intersection lemma provides an `s`-minimal member. If it does not meet
`u`, choose `x∈s`. Since `x∈w`, necessarily `x=a`. Therefore `a∈s`.
Every `z∈a` belongs to `u`, so no such `z` can belong to `s`. Thus `a`
itself is `s`-minimal. This is a classical case distinction on one
existential proposition, not an appeal to object Choice or Foundation.
It proves `TW(w)` and `a∈w`.

## WF is closed under represented sets of WF members

Assume `∀x∈a WF(x)`. Apply just the displayed actual GIC instance to
`a`, obtaining a represented set `c` with

```text
∀t∈c ∃x R(x,t)
∀x∈a ((∃t R(x,t)) → ∃t∈c R(x,t)).
```

The first condition makes every member of `c` TW. Its existential `x` is
global; it need not be in `a`, and no such restriction is used. For every
`x∈a`, its WF hypothesis supplies a witness, so the second condition
gives some `t∈c` with `x∈t`. Consequently `a⊆⋃c`. The union lemma makes
`u=⋃c` TW, and the adjoining lemma makes `u∪{a}` a TW witness containing
`a`. Therefore

```text
(∀x∈a WF(x)) → WF(a).
```

GIC chooses enough witnesses as a set; the proof never defines a witness
selection function. It never invokes a principle saying that functional
Replacement implies arbitrary Collection without Foundation.

Hereditary membership is immediate: if `WF(x)` has witness `TW(t)` and
`x∈t`, then every `y∈x` lies in `t`, so the same `t` witnesses `WF(y)`.
An actual empty object `e` is WF without GIC: its singleton `{e}` is
transitive and every represented nonempty subset of it has minimal member
`e`. The actual quotient already has an empty object, so its WF subtype
is explicitly nonempty.

## Literal formula interface

The Lean file uses de Bruijn builders with the displayed object in slot
`i`; each builder increases existing indices beneath its own quantifier:

```text
transitiveForm i    = ∀x (x∈i → Sub(x,i))
nonemptyForm i      = ∃x x∈i
minimalElementForm m s = m∈s ∧ ∀z (z∈m → z∈s → Bottom)
minimalForm i       = ∃m minimalElementForm m i
wellFoundedForm i   = ∀s (Sub(s,i) → nonemptyForm s → minimalForm s)
twForm i           = transitiveForm i ∧ wellFoundedForm i
wfForm i           = ∃t (twForm t ∧ i∈t)
witnessForm        = twForm 1 ∧ Mem(0,1).
```

Every satisfaction theorem identifies these actual finite formulas with
the corresponding semantic definition. `wf_closure` takes the exact
premise `Sat mem (fun _ => a) (gicForm witnessForm)`; it does not take
closure or collection for all external semantic relations. `gicForm`
already universally quantifies its input set, and the witness matrix has
no extra parameters. `quotient_wf_closure` obtains that premise from the
existing actual `QuotientCPGIC.quotient_fullGIC` theorem.

The WF subtype already satisfies the **actual** `Reg_form`: for a WF
object `a`, its transitive witness contains every member of `a`. Internal
well-foundedness therefore supplies an `a`-minimal member `m`, and
heredity supplies `WF(m)`. The absence of a common member remains true
when the quantifiers are restricted to WF objects. This is Regularity of
the subtype, not Regularity of the raw quotient. It is compatible with
the raw-IR/quotient-IR obstruction recorded in
`quotient_ir_obstruction.md`.

## The remaining interpretation can reuse this closure

The following is an ordinary schema-level plan, not a claim that the
current Lean checkpoint proves all these interfaces. Suppose the ambient
quotient also has its already established `ZFAxioms` and Power Set.

* Extensionality restricts to WF because every member of a WF object is
  WF; equality of membership on the subtype is therefore equality on all
  ambient members. Empty and Pairing restrict using the empty lemma and
  WF closure. Union restricts by heredity twice and WF closure.
* For `a` in WF, every ambient subset `b⊆a` has only WF members, hence is
  itself WF by closure. Every member of the ambient power set `p=P(a)`
  is consequently WF, so closure also makes `p` WF. The actual ambient
  power set therefore serves as the interpreted power set, including all
  subset representatives rather than an assumed bounded collection of
  external subsets.
* Relativize an actual Separation matrix to the unary formula `wfForm`.
  Apply ambient actual-Form Separation to a WF domain set `a`. Its result
  is a subset of `a`, so closure makes the result WF. A generic checked
  unary-formula relativization/subtype-satisfaction bridge is still needed;
  the existing first-order `Relativization.lean` fixes the different guard
  `¬x∈x` and cannot be substituted without proving this bridge.
* For interpreted functional Replacement, use the **actual** ambient
  matrix `WF(x) ∧ WF(y) ∧ phi^WF(x,y,parameters)`. Both guards are
  essential to making the relation globally partial-functional from its
  functionality on the subtype. Ambient formula-indexed Replacement then
  gives an image all of whose members are WF, and closure makes that image
  WF. This step uses functional Replacement in its own stated scope;
  Collection is not inferred from it.
* Ordinary Infinity need not be assumed in the WF subtype. The ambient
  `ZF.Zf.omega_ind` uses actual formula Separation and already available
  ambient Infinity, without Foundation or Power Set. Instantiate its
  induction formula with `wfForm 0`: the empty case is above; the
  successor case follows from heredity and closure. Thus every ambient
  natural belongs to WF. Closure then makes the ambient `omegaV` itself
  WF. Its empty member and successor closure give the interpreted
  ordinary Infinity axiom. No object-level recursion is used to construct
  ambient Infinity; that resource was already proved by the finite-attempt
  quotient construction.

This would build an actual model of the repository's `ZFax_s` from the
current CP/GIC quotient while avoiding any attempt to pass raw IR to the
quotient. It would not by itself prove the more general relative
consistency theorem from bare ZF0: the present construction explicitly
uses the extra fixed GIC witness instance. That stronger hypothesis is
already available on the route from the exact numerical/native theory.
Choice removal or a constructible-part interpretation and the intended
arithmetic proof internalization remain separate work.

The 258-line source passes the explicit official Lean 4.32.0 compiler in
0.53 seconds. Twenty-two theorem assumption audits and four caller examples
pass in 0.32 seconds. Only `propext`, `Classical.choice` and `Quot.sound`
occur. The callers check the exact one-formula GIC premise, its availability
under the actual equality-free schema, a nonempty quotient WF subtype
satisfying the literal `Reg_form`, and internal minimality without any
external `WellFounded` hypothesis. An independent full read found no
semantic or formula-index error. Commands, exact caller source and all
audited axiom sets are in `results/well-founded-part-verification.json`.
The scoped check reused the source-verified 93-module cache; it did not
rebuild the large blank bootstrap or run any Coq build.
