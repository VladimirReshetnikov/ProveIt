# Raw and tagged transitive containers: next source-proof checkpoint

This is a read-only proposal. No new Lean source, overlay, compiler invocation,
or dependency refresh was made. The recommended pair is
`ValidatorSeedTransitive222.lean` and `ValidatorSeedTransitive222Checks.lean`,
with the sole import `ZFCinPA.ValidatorSeedLogicalImages222`.

The substantive new result is an actual source proof of a transitive raw
container containing any given object. The fixed seed matrix is singleton
membership with the output/input slots in the correct order. Guarded
transitivity and exact tagged pairs then follow from already accepted source
proofs. No transitive-envelope premise is supplied to the public endpoints.

## 1. Exact proposed formulas and endpoints

Work over `{V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* IΣ₁]`, keeping the
Type-0 boundary of the selected import. Write `Source V` for the existing
`ValidatorSeedSourceBasis222.Source V = seedTheory.internalize V`.
All `a,t,x,y` below are arbitrary `Term V ℒₛₑₜ`, including internally
nonstandard free-variable indices. No distinctness, positivity, freshness,
standard-code bound, or supplied set-model-validity premise is imposed on them.

Here `mem`, `eq`, `sing` are the existing `memTerm`, `eqTerm`, `singTerm`;
the displayed `#i` are typed bound variables. Define exactly:

```text
transitiveMatrix : Semiformula V ℒₛₑₜ 2 := sing #1 #0

rawTransitiveBody a : Semiformula V ℒₛₑₜ 1 :=
  mem a.bShift #0 ∧
  ∀⁰ (mem #0 #1 → ∀⁰ (mem #0 #1 → mem #0 #2))

taggedTransitiveBody a t : Semiformula V ℒₛₑₜ 1 :=
  mem t.bShift #0 ∧
  (mem a.bShift #0 ∧
   ∀⁰ (mem t.bShift.bShift #0 → mem #0 #1 →
       ∀⁰ (mem t.bShift.bShift.bShift #0 →
           mem #0 #1 → mem #0 #2)))

taggedPairBody x y t : Semiformula V ℒₛₑₜ 1 :=
  mem t.bShift #0 ∧
  ∀⁰ (mem t.bShift.bShift #0 →
      (mem #0 #1 ↔
       (eq #0 x.bShift.bShift ∨ eq #0 y.bShift.bShift)))
```

The public proposed source judgments are:

```lean
theorem raw_transitive (a : Term V ℒₛₑₜ) :
  Source V ⊢ ∃⁰ rawTransitiveBody a

theorem tagged_transitive (a t : Term V ℒₛₑₜ) :
  Source V ⊢ emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t

theorem tagged_pair (x y t : Term V ℒₛₑₜ) :
  Source V ⊢ emptyAt t 🡒 ∃⁰ taggedPairBody x y t
```

These are unconditional metatheorems yielding source proofs of the displayed
formulas. `emptyAt t` and `t∈a` are literal source antecedents, not supplied
Lean hypotheses or image oracles. The pair endpoint is slightly stronger
than the tagged-domain guide: it restricts the membership test to tagged
objects even when x or y is untagged. The usual pairing law follows after
adding the source antecedents `t∈x` and `t∈y`. It remains meaningful when
x=y, x=t, or a=t; the relevant guards are retained rather than replaced by
external disequalities.

For each conclusion provide an explicit `Source V ⊢! ...` proof chosen from
the proved judgment and a theorem
`Proof seedTheory proof.val conclusion.val`, as in the accepted Guarded
packet. Thus the result provides proof witnesses inside every selected
arithmetic model, not just proofs for each standard numeral instance.
Using `.get` does not by itself prove a Σ₁ graph for the whole proof selector;
no such complexity claim is proposed.

## 2. Actual full-seed matrix and raw proof

The existing semantic guide `KLowerRaw.raw_transitive` (lines 88–99) uses
`singF 1 0`. It is only a guide. The new implementation will use the actual
typed `transitiveMatrix = singTerm #1 #0` and bind its quotation/raw code.
For any typed terms v,p, its literal substitution is:

```text
transitiveMatrix.subst ![v,p] = singletonAt p v.
```

Slot 0 is the output; slot 1 is the input. Expanding the singleton binder
gives `∀⁰ (#0 ∈ #2 ↔ #0 = #1)` at semiformula arity 2. The matrix has no
free parameters and is shift-fixed, but none of the ambient a,t,x,y terms
are assumed shift-fixed. This matches the accepted
`ValidatorSourceFullSeed222.fullSeedBody` exactly, including its distinct
support and request clauses.

The finite source proof follows this chain:

1. Use `SourceBasis.singleton_object a` to obtain a source witness s with
   `singletonAt s a`. Instantiate `SourceBasis.openSeedProof
   transitiveMatrix` at s. Its existential container witness C satisfies
   the full seed pair, not just the projected image body.
2. Specialize the request conjunct at a. The input relation is
   `singletonAt s a`, so obtain a witness z with
   `singletonAt s z ∧ z∈C`. Prove singleton uniqueness using the source
   equality axioms. This yields a=z and, by actual source membership
   congruence, a∈C.
3. For arbitrary y∈C, invoke the public
   `RawComprehension.full_member_closure transitiveMatrix s C y`.
   It yields the actual closure formula `memberClosure` without a
   supplied closure premise in the final theorem. The hidden support
   witness has already been eliminated by that accepted theorem.
4. For arbitrary z∈y, use `singleton_object z` to obtain p={z}. Its
   defining universal formula proves `subsetTerm p y`, using source
   equality replacement and the existing premise z∈y.
5. Specialize the closure at input p and output z. The relation is
   `singletonAt p z`. Obtain z' with `singletonAt p z' ∧ z'∈C`.
   Singleton uniqueness yields z=z', and source membership congruence
   gives z∈C. Reclose z and y in the correct order and reassemble the
   existential container.

This uses the full closure of the same seed container selected in step 1.
It does not choose unrelated containers for different y or assume a
transitive container through a premise. Raw transitivity itself needs no
empty-marker hypothesis. The ambient source theory already contains
irreflexivity, but this proof chain does not use it to fabricate membership.

The public seed APIs needed here already exist:

| Source | Public API |
| --- | --- |
| `ValidatorSeedSourceBasis222` | `openSeedProof`, `openSeed_isProof`, `singleton_object`, `singletonBody`, `singletonAt`, `term_is_fvar` |
| `ValidatorSeedRawComprehension222` | `singTerm`, `subsetTerm`, `seedPairAt`, `memberClosure`, `full_member_closure` |
| `ValidatorSourceFullSeed222` | `fullSeedBody`, `fullSeedBodyVal_eq`, `fullSeedBody_quote` |
| `SetCongruence` | actual source equality/replacement lemmas, with literal equality-theory inclusion in seedTheory |

The older `pair_exists`, `pair_request`, `closure_step`, and singleton helper
proofs are private. The new leaf will not refer to their private generated
names. Small local specialization lemmas will be proved directly from
`openSeedProof`, the public pair/closure definitions and the actual source
equality axioms. The equality-theory inclusion is proved by the literal
union inclusion (as in TaggedCollection), not supplied as a hypothesis.
No new theory, general derivation interpreter or formula induction is
needed for this finite construction.

## 3. Guarded transitivity and exact pairs

Let `truthMatrix : Semiformula V ℒₛₑₜ 1 := ⊤`. Using truth instead of the
guide's `#0=#0` is an explicit choice of a literal source matrix; no semantic
identification of formulas is used. Its substitution and shift equations
are immediate source-syntax equalities.

For tagged transitivity, eliminate the actual raw witness U from
`raw_transitive a` and apply
`GuardedComprehension.guarded_comprehension truthMatrix U t` under the
source assumption `emptyAt t`. The resulting v satisfies

```text
t∈v ∧ ∀z, t∈z → (z∈v ↔ z∈U ∧ ⊤).
```

Together with t∈a and a∈U this gives a∈v. For tagged y,z with y∈v and z∈y,
first infer y∈U; raw transitivity gives z∈U; the tagged cut gives z∈v.
The accepted guarded theorem handles U=t itself, so the new theorem must
not add U≠t, a≠t, a marker-freshness bound or a transitive-envelope premise.

For exact tagged pairs, eliminate the public `raw_pair x y` witness U and
apply the same truth cut. Combine its restricted membership biconditional
with the exact `rawPairBody x y` biconditional. This derives the displayed
`taggedPairBody` directly and is small enough to include in this pair.
It does not yet prove the different profile `Pair` predicate involving
interpreted `Member` and `Eqv`; that conversion remains a later source
certificate, even though the semantic `KLowerEqv.tag_pairs` shows its shape.

## 4. Binder and raw-code obligations

Prove explicit `_shift`, `_free` and substitution equations for each new
body and its `At := body.subst ![container]` form. Existential eliminations
shift the entire finite context, including the marker, parameter a/x/y,
and earlier singleton/container witnesses. Reclosing the two universal
variables in raw transitivity must leave y at #1 and C at #2 beneath z.
Under the tagged universal guards, the marker has two and then three
`bShift`s. The generic proof cannot rely on all free labels being distinct.

The fixed singleton matrix receives a meta quotation and raw-code binding.
The three conclusion/body constructors receive total raw-code functions
with concrete Σ₁ graphs using already imported atom substitution, Boolean
connective and quantifier constructors. Parameters to these functions are
raw **term codes**, not bare variable indices. Typed binding theorems use
`term_is_fvar` and the exact `bShift` identities; behavior on ill-typed raw
inputs is just the defined total constructor and carries no proof claim.
This is formula-construction totality, separate from the proof-selector
complexity boundary stated in section 1.

Focused checks should cover the singleton matrix's slot direction and
literal one-binder expansion, all three raw-code/typed bindings, raw
transitivity and the two guarded conclusions, `a=t`, x=y, x=t, sparse
symbolic free labels, simultaneous parameter shifts, and actual
`Proof seedTheory` certificates. Axiom reports must use only the existing
standard axioms. No external KLower/NatForm theorem is imported as a source
proof resource; the already accepted source-calculus dependencies are reused
with their existing provenance and assumptions.

## 5. Exact authenticated proposed cache

The accompanying JSON records the complete current source/import DAG and
actual first artifact providers for the one-import proposal. The read-only
auditor completed successfully with **5,971 distinct path/hash
observations**, **217 cached modules**, **136 Foundation modules**,
**625 cached artifacts**, **45 external boundaries**, and **670 actual
first artifact providers**. It includes implicit Init and public/meta
imports. There are 262 primary providers (217 custom plus 45 boundaries).
There are **zero prerequisite refreshes** and only the proposed two fresh
leaf compilations if separately authorized.

Selected accepted ROOT Logical provider:

```text
/tmp/validator-seed-logical-images222-root-sx91r5e8/lib
main source: 10bc7d953a9eff96977689b0229dd7c9ba8e3495492113125115a8335c39bd4f
main object: a3d3f29e897ec9ff7a4fa7436552689f985ff3fcd08b71c85b6e4faff50bd7c4
ROOT packet: 97e86d457fa22c4adc6ad0db0b427084a3e8d52430bc6cafa1a9f375d167d9db
ROOT 13-file manifest: 7eded66b85380e049713de51c4b70566a8cea4a7a4651976c186457344cf2491
plan JSON: ab31208a45cd28e5950c62b6133d4f79a8f650bdc31838028a0a22f3d7ea8f43
```

Both original author and independent ROOT evidence are pinned. The ROOT
provider is selected directly; all first-provider resolution is checked
through that explicit overlay and package paths. Historical qualifications
about source-run provenance and missing companions remain inherited;
reauthentication does not turn them into fresh builds. External semantic
guide sources are separately pinned as source-only and are not new compiled
dependencies. Future fresh commands retain the existing memory/thread cap,
512MiB reserve, full source/check/driver reads and every failed attempt.

## 6. What this advances, and what remains

`KLowerEqv.tag_tc` and `tag_pairs` identify the immediate use of this pair:
transitive containers plus exact pairs and the already accepted GIC images
support ordered-pair codes and the particular diagonal/reverse/fiber/
composition/union/matching instances used by the profile proofs. Genuine
source certificates for those profile constructions and the actual
`Eqv` reflexivity/symmetry/transitivity/extensionality laws still need to be
constructed. Raw source equality, the validator's Eind, and coded profile
Eqv are three distinct relations; none is silently substituted for another.

After those laws, interpreted `Member` congruence and the nine-field
`KQHyp.QHyp` contract remain: GIC, the four Eqv laws, profile pairs,
interpreted union, interpreted power, and singleton-closed containers.
Raw transitivity is not literal NativeTheory CP and does not supply
interpreted power or singleton closure. `KLowerQHyp` uses further raw power,
tagged separation and profile arguments for these fields.

`KQ1Model` and `KQ1ZF` explain the semantic quotient and internally
well-founded-part route to ZF. Their external NatForm/BProv soundness results
do not provide the missing uniform internal Foundation proof transform.
Actual source axiom images, parameter/closure uniformity and the compatible
represented quotient/WF interpretation must still be discharged. The
accepted moving-marker theorem is available for the first guarded stage;
there is no blanket Good/shift-fixed assumption on a free marker.

The Choice step is separate and already has the actual all-internal API
`LSchema.provable_falsum_ZF_of_ZFC` under IΣ₁, with separation/replacement
schemas discharged there. Reuse it only after a real ZF-to-seed internal
calibration exists. This proposed pair proves neither that calibration nor
a current PA/HA equation equivalence.
