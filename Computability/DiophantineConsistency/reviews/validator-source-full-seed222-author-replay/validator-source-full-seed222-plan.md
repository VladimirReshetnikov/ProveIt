# Actual C222 full-seed images and the remaining tagged interpretation

Read-only source audit by `circuit_reduction`, 26 October 2026. The companion
JSON pins the inspected sources and the proposed narrow dependency closure.
No proof source, object, shared documentation, or Git state was changed; no
Lean compiler or dependency build was run. Proposed declarations below are
not yet theorems.

The next useful packet is **`ValidatorSourceFullSeed222` plus checks**: prove
the encoder image of the actual full seed sentence for every internally
typed two-slot matrix. Keep both `clos` and `req`. This is an unconditional
family of source axiom images, not an assumed image predicate or another
semantic wrapper. It is a necessary interpretation checkpoint; it does not
yet discharge raw CP/GIC or Collection. Root has agreed to this direction.

## 1. Why the old raw CP/GIC proof is not the next proof

The actual C254 theorem `ValidatorNativeGic254.cProv_native_pair` projects
`bundleC` and `bundleG` from the old checker bundle. Its `cProv_container`
and `cProv_internalGic` therefore have premises that are not C222 gates.
Changing the namespace or reusing the source skeleton cannot supply them.
The actual C222 bundle instead gives a subset-indexed seed.

With matrix relation `Q(input, output)`, the seed says that a collected
member `y` has a Q-preimage, and that every `x' ⊆ y` having a Q-image has a
Q-image in the collection. Raw GIC demands an image of every `x ∈ A` having
one. Neither `x ∈ A → x ⊆ y` nor a suitable collected `y` is supplied by
the seed. Encoding `x` by its singleton addresses that indexing difference,
but the root/envelope inserted to drive the construction need not itself
be a Q-image. Raw GIC's support clause forbids silently retaining it.

Likewise, `KLowerRaw.raw_transitive` and `raw_power` separately construct a
transitive superset and a raw power set. They do not establish the actual
CP requirement that one transitive container contain, for each of its
members, a bound for every raw subset of that member. Mere membership in a
container, such as `ValidatorSeedWitness222.membership_container`, is weaker.

This is a concrete obstruction to the inspected *proof route*, not a
countermodel or a claim that raw CP/GIC is unprovable. The source comment
in `KLowerRaw` about augmented rather than exact raw separation must not
be promoted to a new impossibility theorem.

The external proof actually takes this route:

```
FullSeed / FormSeed
  -> raw empty, singleton, pair, transitive, power, augmented separation
  -> tagged comprehension and tagged Collection
  -> tagged GIC, transitive containers and pairs
  -> represented bisimulation equality and interpreted membership
  -> quotient interface QHyp -> ZF consistency
```

`KLowerTag.tag_collection` works in `Tag mem t = {x // mem t x}`. Its
guarded matrix and tagged comprehension make the unwanted envelope and
empty marker invisible. `KLowerQHyp.tag_qhyp` supplies a quotient interface,
not the old raw `NativeSet.nativeTheory` CP/GIC image. Its final
`zf_consistent_of_formSeed` is an external semantic theorem and is not an
internal arithmetic derivation transformation.

## 2. The exact seed and the freshness already proved

Use `CProv`, `encode`, `clos`, `req`, `ex`, and `wal` from the accepted C222
modules, with their existing meanings. In particular the actual history
witness is `ArithmeticHistory222.value d = conclusion + 1`.

`ValidatorSeedPadding222.bounded_seed_image` already builds a certificate

```
(clos a b c c ∧ req b c c) -> (clos a b c P ∧ req b c P),
c = seedLabel bound P.
```

Its public conclusion then projects to `imageBody`. A new leaf can retain
the stronger intermediate and prove, without modifying that frozen file,

```lean
bounded_seed_pair (bound P a b : V) (ha : a ≤ bound) (hb : b ≤ bound) :
  CProv (ex (seedLabel bound P)
    (conj (clos a b (seedLabel bound P) P)
      (req b (seedLabel bound P) P)))
```

The proof is the existing matrix congruence certificate, `ex_mono`, and
the literal two guarded seed gates. It stops before `pair_image`.

For `P = encode F B r K`, `len B = 2`, and odd `r`, the existing
`typed_seed_vacuity` proves `Vac c P` when the bound includes `F`, `B`,
and the role labels. The label is even, exceeds the bound, avoids all
stored labels and fallback1, and avoids the entire odd binder stream,
including its nonstandard indices. It is not necessary to assume `Vac c c`.

The padding is on the **numeric encoded matrix**:
`c = ¬¬(((bound+1)→(bound+1))→P)`. Its actual CProv equivalence with `P`
is proved. No unproved equation between the code of a padded source
formula and this numeric label is needed. The final source schema contains
the original arbitrary matrix K.

Retaining the full pair matters. `imageBody`'s coverage leaves the input
label free; it cannot be generalized inside its already obtained
existential container without proving the relevant independence. The
literal `clos` already contains the required universal binder in scope.

## 3. Literal source sentence and proposed endpoints

Let K have source bound slots **0 = output, 1 = input** and any source free
parameters. Write `Q(x,y)` for this source K with those slots replaced by
`y,x`. Define `FullSeedBody(K)` to be the following formula with no bound
slots remaining (its original free parameters remain free):

```
∀ A ∃ C,
  (∀ y, y∈C -> ∃ x,
    Q(x,y) ∧ ∀ x',
      (∀ w, w∈x' -> w∈y) ->
      ∀ y', Q(x',y') -> ∃ z, Q(x',z) ∧ z∈C)
  ∧
  (∀ y, Q(A,y) -> ∃ z, Q(A,z) ∧ z∈C).
```

The order is closure then root request, matching `clos ∧ req`; the
external `SeedProp` has these conjuncts in the opposite order. Conjunction
commutation is a finite logical step, not a semantic identification.

The exact source substitutions are:

| Matrix occurrence | Current binder depth | K slot replacement `[output,input]` |
|---|---:|---|
| root premise `Q(A,y)` | 3 | `[#0,#2]` |
| root witness `Q(A,z)` | 4 | `[#0,#3]` |
| support `Q(x,y)` | 4 | `[#1,#0]` |
| closure premise `Q(x',y')` | 6 | `[#0,#1]` |
| closure witness `Q(x',z)` | 7 | `[#0,#2]` |

The root witness uses `mem(#0,#2)`. The closure antecedent is
`∀w (mem(#0,#1) -> mem(#0,#3))` at depth 6, and its final witness uses
`mem(#0,#5)` at depth 7. These indices must be checked literally, including
the binders that remain in scope but do not occur in a particular atom.

Proposed new definitions and primary endpoints (schematic Lean signatures):

```lean
fullSeedBodyMeta (K : SetTheorySemiproposition 2) : SetTheoryProposition
fullSeedBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
  Bootstrapping.Semiformula V ℒₛₑₜ 0
fullSeedBodyVal (k : V) : V

fullSeedBody_quote K : quote (fullSeedBodyMeta K) = fullSeedBody (quote K)
fullSeedBodyVal_eq K : fullSeedBodyVal K.val = (fullSeedBody K).val

full_seed_image [V ⊧ IΣ₂]
  (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)
  (F s : V) (hs : StreamFree s F) :
  CProv (encode F 0 s (fullSeedBody K).val)

full_seed_witness [V ⊧ IΣ₂] K F s hs :
  ∃ d : V, ArithmeticHistory222.value d =
    encode F 0 s (fullSeedBody K).val + 1
```

K and its syntax tree are internally coded and need not be standard. No
matrix-interpretation oracle, source proof, raw GIC premise, or semantic
FullSeed structure appears among the hypotheses. `StreamFree` is the
existing genuine encoder resource, not an extra semantic assumption.

Recommended first scope is these literal body/quote/image endpoints and
the retained numeric pair, approximately 300–400 main lines plus focused
checks. If the finite binder transport is larger, split it into a first
full-pair/binder leaf and a second literal source-binding leaf; neither
intermediate should be described as the full schema theorem.

## 4. Concrete proof route and classified invariants

1. Select an odd source binder start above `F` and fallback1, by explicit
   arithmetic, so the finitely many outer role labels are distinct and
   free-safe. Put the core's own binder stream strictly above those roles.
   Take `P = encode F (b∷a∷0) r K.val` with odd `r`, and a numeric bound
   covering this stack, F, and all role labels. Apply `bounded_seed_pair`
   and the already proved typed vacuity for its even self-label c.
2. Unfold the finite source skeleton with actual `encode_all`, `encode_exs`,
   `encode_and`, and `encode_or`. Source implication is NNF negation plus
   disjunction, so use `ValidatorSourceNegation222`'s actual CodeIff; it
   is not definitionally numeric `wim`.
3. Use `encode_subst_pair` for every matrix substitution in the table.
   Prove each replacement's exact bound-label lookup. For matrix copies
   at different streams/stacks use `encode_eq_under`, discharging the
   actual Eind-context or primitive-premise certificate. Same-parity or
   overlapping streams must go through an explicitly fresh opposite-parity
   stream above both stacks; `FreshPair` is not automatic.
4. Convert the repeated named a/b binders of `clos` and `req` to the finite
   source binders. Use `eqUnder_all_of_cons`, `eqUnder_ex_of_cons` or their
   finite relational components, with cross-body vacuity supplied by typed
   source matrices and literal membership atoms. Convert the even
   self-label existential to the source's chosen container binder with
   the same method. Only `weq -> Eind` is allowed in primitive witness
   precomposition; never `Eind -> weq` or primitive-equality vacuity.
5. Close the root label by actual GEN, and compare the resulting complete
   formula with any requested free-safe s using
   `encode_formula_relabel`. All source free parameters remain in F.

The finite skeleton and raw body graph use IΣ₁ total syntax operations.
Uniform alpha/vacuity/NNF compatibility use the accepted Π₂ induction
theorems under IΣ₂. There is no new induction over an arbitrary Lean
predicate. If a same-stream stack-congruence helper is factored out, its
uniform proof invariant is the existing typed Π₂ invariant with explicit
Π₁ freshness, not a guessed Σ₁ context rule.

After this first packet, a separately reviewed represented schema can be
defined by the actual range of `(fullSeedBodyMeta K).univCl`. Its raw
recognizer must support internally sized closure, actual substitution of
free variables, and a checked code bound. Reusing the generic
`SchemaRecognizer` design is reasonable; importing `NativeGicDelta1` or
its image theorem is not necessary. This recognizer and its additional
imports are **not included in the 166-module first-leaf cache below**.
An arbitrary-closure image uses an explicit Π₂/IΣ₂ induction and yields
genuine AxOK for that newly defined full-seed theory, rather than for the
old CP/GIC theory by a name change.

## 5. What substantive set interpretation remains

Once the full source seed image is bound, the useful next finite source
consequences are exact empty/singleton and the raw augmented/tagged
comprehension construction. The first Collection target justified by the
audited route is the **guarded tagged** image of `gicBodyMeta`, with
`D_t(x) := t∈x` and a source empty-marker hypothesis. A represented
relativization must restrict every quantifier and carry all free parameters
in that domain. `KLowerTag.tag_collection` supplies the precise matrix
recipe (`collSh`, root pair, envelope, singleton and domain guards) to
translate into finite source deductions; it does not itself supply such
deductions or their internally coded uniform witnesses.

Keep four notions separate throughout:

* source equality, interpreted by the actual encoder as numeric Eind;
* primitive numeric `weq`, used only by checked witness rules;
* tagged raw membership `tmem`, obtained by restricting the domain;
* `Profile.Eqv = ∃r (Bisim r ∧ App r x y)` and
  `Profile.Member x y = ∃u (mem u y ∧ Eqv x u)`, used by the later quotient.

Atomic Eind congruence suffices for the source equality calculus already
proved. It does not identify Eind with bisimulation or manufacture the
later quotient's extensionality/Collection axioms. The remaining tagged
and quotient transformations must be represented and proved before an
unconditional internal ZF→CProv theorem is claimed. No standard-Nat
completeness, `ProperOn`, or external model existence can replace them.

## 6. Checks and cache lead

Checks should bind the literal source body and all five replacement
vectors; preserve truth and falsum K, a matrix using both slots, duplicate
free parameters/fallback1, and a nested-quantifier K. They must expose the
actual history witness and the full `clos ∧ req` conclusion, not only its
imageBody projection. Check all original source free parameters survive;
do not claim bare numeric gate collisions satisfy the seed rule.

The minimal proposed imports are accepted `ValidatorSeedPadding222`,
`ValidatorSourceNegation222`, and `ValidatorExistentialRules222` (the last
already imports actual substitution/quantifier/alpha support). Traversal
of their authenticated records gives **166 cached custom modules,
117 Foundation, 517 object artifacts, and 40 explicit external boundaries
including Init and the public meta Aesop import**. No new Foundation
module is needed. SeedPadding's accepted independent primary is
`/tmp/seed-padding222-controller-peer-yfju0299/lib`; its source is
`8af4455583ad86ba7476154f08648a2e2b3d9766660d63a8bfcd4740eb5a6b6f`
and object is `09b592056fd7decdf0f723adbefb5121c92e49eacb384c19a15d9f652759cf76`.

The companion JSON records read-only rehashing of selected current sources,
objects, external primaries and provider records. This is a cache lead,
not execution of the proposed source. Before any approved build, freeze
the actual new imports and reauthenticate the complete selected provenance,
compiler/toolchain/manifest and all parent companion records. Only new
private outputs may be written; preserve every attempt and the 512MiB
reserve. No CP/GIC, full ZF/source interpretation, machine calibration or
HA equation endpoint is closed by this audit.
