# Actual full-seed theory recognizer and C222 AxOK: read-only plan

26 October 2026. This proposal follows the accepted literal body packet
`ValidatorSourceFullSeed222` (ROOT commit `f55b3eef90`). No new Lean source,
compiler invocation, overlay, dependency rebuild, shared object change or
Git operation was made for this audit. The proposed result is an actual
represented source theory with discharged `AxOK`, not a raw CP/GIC image
and not yet a source-ZFC interpretation.

## 1. Recommended next packet

One coherent new pair, `ZFCinPA.ValidatorFullSeedTheory222` and Checks,
can supply a concrete Δ₁ schema recognizer, an internal universal-closure
lemma, and `AxOK` for equality + irreflexivity + the full-seed schema. It
would import only:

```lean
import ZFCinPA.SchemaClosure
import ZFCinPA.ValidatorSourceFullSeed222
import ZFCinPA.ValidatorEqualityImages222
```

A reasonable implementation estimate is 350–450 main lines plus focused
Checks; this is not a line cap. If the fixed graph and closure proof need
separate owners, split them before execution rather than label an
intermediate as the complete theory image.

The concrete source theory is new and named explicitly. It is not an alias
for the old `NativeSet.Theory`, `gicTheory`, or an existing `FullSeed` semantic
structure. Its literal schema body is the already frozen
`ValidatorSourceFullSeed222.fullSeedBodyMeta`, with output in slot0 and input
in slot1, and every original free parameter retained:

```lean
def seedSchema : SetTheory :=
  Set.range (fun K : SetTheorySemiproposition 2 =>
    (fullSeedBodyMeta K).univCl)

def irreflexiveSentence : SetTheorySentence := “∀ x, x ∈ x → ⊥”
def seedTheory : SetTheory :=
  ((𝗘𝗤 ℒₛₑₜ) ∪ {irreflexiveSentence}) ∪ seedSchema
```

The first definition uses the actual `univCl`, not a fixed finite prefix or
an assumption that the matrix has no free parameters.

## 2. The recognizer and a necessary code-bound detail

`SchemaClosure.lean` already supplies the language-generic
`SchemaRecognizer L a Fval` and `schemaRecognizer_quote_iff`. Its internal
recognizer is exactly:

```text
∃ m≤p ∃ b≤p,
 p=qqAlls b m ∧ IsUFormula L b ∧ shift L b=b ∧ bv L b=m ∧
 ∃ K≤subst L (fvarVec m) b,
   IsSemiformula L a K ∧ subst L (fvarVec m) b=Fval K.
```

Its correctness theorem asks for a standard quotation identity and the
standard bound `⌜K⌝ ≤ Fval ⌜K⌝`. Neither theorem assumes that internal codes
are standard. Standard `IsSemiformula.sound` is used only inside the
existing quotation-level membership proof; it must not appear in the
arbitrary-model axiom-image extraction.

There is a small but real issue with using `Fval := fullSeedBodyVal`
directly: its identity vector `[0,1]` at depth6 is an implication antecedent,
so the raw body contains the NNF negation of that copy. It is incorrect to
apply the old GIC positive-subterm bound unchanged.

Use the following exact reparameterization instead:

```lean
def seedRecognizerBodyMeta K := fullSeedBodyMeta (∼K)
def seedRecognizerBodyVal (k : V) :=
  fullSeedBodyVal (Bootstrapping.neg ℒₛₑₜ k)
abbrev SeedR := SchemaRecognizer ℒₛₑₜ 2 seedRecognizerBodyVal
```

This recognizes the same schema, not a weakened or transformed theory:
`K ↦ ∼K` is involutive, so the two ranges of universally closed bodies are
extensionally equal. For the depth6 identity copy, actual quotation and
NNF involution give

```text
neg(subst [#0,#1] (neg ⌜K⌝)) = ⌜K⌝.
```

The identity substitution is `Rew.castLE` from level2 to level6;
`Semiformula.quote_castLE` erases this level change. The resulting code is
a positive child of the inner disjunction. Following `lt_or_left`, the
surrounding universal, right-disjunction, conjunction and outer quantifier
inequalities gives `⌜K⌝ ≤ seedRecognizerBodyVal ⌜K⌝`. No general monotonicity
of NNF negation or substitution is asserted. Truth, falsity and matrices
with free parameters must be included in the Checks.

Define a fixed Σ₁ graph for the actual raw body by composing existing
`negGraph`, all five literal substitutions, `impGraph`, `qqAndDef`,
`qqAllDef`, and `qqExsDef`. The actual vectors remain `[1,0]`, `[0,1]`,
`[0,2]`, `[0,2]`, `[0,3]`; their level annotations and the two membership
witnesses are unchanged. The graph must be proved to compute this exact
`seedRecognizerBodyVal` in every IΣ1 model.

The concrete Δ₁ formula follows the existing generic closure pattern:
its Σ-side existentially binds the total function graph values; its Π-side
universally tests those values. The bounded variables are `m,b≤p` and
`K≤openedBody`. The actual `isSemiformula` sigma/pi pair supplies the typed
core test. Totality/uniqueness of the function graphs gives literal
`SeedR.defined` in IΣ1. Then
`schemaRecognizer_quote_iff`, the quotation identity, code bound and
negation-range equality establish a genuine `seedSchema.Δ₁` instance.
This is a concrete fixed arithmetic formula, not a supplied predicate
whose membership is assumed to have the desired image.

`NativeGicDelta1.lean` is a source guide for this graph/recognizer shape
only. It is not imported and its old GIC formula or theorem is not used.

## 3. Internal universal closure, with arbitrary parameters

The needed closure theorem has the following scope under explicit IΣ2:

```lean
theorem closure_image {m b s : V}
    (hb : IsSemiformula ℒₛₑₜ m b)
    (hbs : shift ℒₛₑₜ b = b)
    (base : ∀ F : V, StreamFree s F →
      CProv (encode F 0 s (subst ℒₛₑₜ (fvarVec m) b))) :
    ∀ F : V, StreamFree s F →
      CProv (encode F 0 s (qqAlls b m))
```

Here `m,b,F,s` are all internal model elements. In particular, `m` is not a
standard Nat, and there is no odd-environment/even-stream restriction.

Use the internal invariant

```text
pc s m b F i = encode F 0 s
                (subst ℒₛₑₜ (fvarVec (m-i)) (qqAlls b i))
i≤m → ∀F, StreamFree s F → CProv(pc s m b F i).
```

`pc` is Σ₁ definable. `StreamFree` is Π₁ and has the accepted Σ₂ promotion;
`CProv` is Σ₁ and has the accepted Π₂ promotion. Thus the displayed
invariant is Π₂, and actual internal IΣ2 order induction applies. This is
not an unclassified induction over arbitrary predicates.

Only three short syntax helpers are needed:

* `fvarVec_isTermVec`: follows directly from `len_fvarVec` and
  `nth_fvarVec`, for arbitrary internal length.
* `shift_qqAlls`: actual Σ₁ induction using `shift_all` and
  `isUFormula_qqAlls`.
* `free_subst_qVec_fvarVec`: for a typed, shift-fixed `(k+1)`-body,
  opening `subst(qVec(fvarVec k))` gives `subst(fvarVec(k+1))`.
  This uses the actual `shift_substs`, `substs_substs`, and vector nth
  identities, with no source semantics premise.

The corresponding proofs are visible in `ModelCodedBindFree` and
`NativePeel`; those broad owners are not imported. The narrow helper proof
can be restated against the already imported syntax APIs. At the induction
step, use the actual `ValidatorQuantifierRules222.eigen F s`,
`fresh_resources F s hs |>.2.2.1`, and `all_rule`. The induction hypothesis
is instantiated at the extended free environment, so every free parameter
is preserved. This avoids an unjustified blanket GEN rule over a fixed
context. At `i=m`, typed `subst_eq_self` removes the empty free vector.

## 4. Concrete AxOK discharge and endpoint

Internal `SeedR p` supplies the actual `m,b,K` witnesses. From its typing
and `bv b=m`, derive `IsSemiformula L m b`. Apply `closure_image`. Its base
is exactly `typed_fullSeed_image hK.neg F s hs`, rewritten by the extracted
opened-body equality; no body-image premise remains.

Planned public results are:

```lean
theorem recognized_seed_image {p : V} (hp : SeedR p)
    (F s : V) (hs : StreamFree s F) : CProv (encode F 0 s p)

theorem axOK_seedSchema : ValidatorSourceDerivation222.AxOK seedSchema V

theorem axOK_seedTheory : ValidatorSourceDerivation222.AxOK seedTheory V

theorem seedTheory_refutation_witness
    (h : Provable seedTheory (^⊥ : V)) :
    ∃ d : V, ArithmeticHistory222.value d = 2
```

The final theorem uses the already accepted ten-case SourceDerivation
interpreter. Its hypothesis is an actual internal proof of falsity in this
newly defined concrete source theory, not an assumed source axiom map.

The equality recognizer must explicitly use
`ValidatorEqualityImages222.equalityDelta`; the singleton uses the actual
`Theory.Δ₁.singleton`; unions use `Theory.Δ₁.add`. Arbitrary internal
membership in those fixed formulas is split by their actual disjunctions.
The equality branch uses accepted `axOK_equality`; the singleton branch
extracts the literal sentence code and uses `irreflexivity_image`. The seed
branch uses `recognized_seed_image`. No broad ZFDelta1 or NativeTheory
instance is silently identified with these new names.

Meaningful Checks should expose nonstandard-length closure variables,
arbitrary free environments, both stream parities, matrix truth/falsity,
several sparse free parameters, the exact negative reparameterization,
literal recognizer membership, all finite union branches, and the actual
History222 value2 endpoint. Print axioms for each public graph, closure,
recognizer and AxOK theorem.

## 5. What this does not yet prove

The current literal body and new schema theory are not the old raw GIC or
container theory. The proposed packet does not claim raw CP/GIC images,
ZF axiom images, tagged Collection, a bisimulation quotient, or the HA
current-equation equivalence.

`KLowerSeed.formSeed_of_fullSeed` is an external semantic conversion
between named and de Bruijn formulas. `KLowerRaw` proves semantic raw empty,
singleton, power and tagged constructions. `KLowerTag.dt_comp` and
`tag_sep` use a tagged domain; its later collection proof additionally uses
an explicit guarded formula. These are useful guides for the next
source-proof construction, not internal C222 derivations or PA proof-code
transforms. In particular, neither model satisfaction nor standard-Nat
completeness can discharge a missing internal AxOK branch.

After this packet, the substantive remaining source-side task is a
represented syntactic interpretation from the required set theory into
this full-seed theory: the tagged-domain construction, all source matrix
rewrites/closures, and the equality/bisimulation quotient obligations.
The currently used numeric equality is Eind. Its proved congruence laws
do not identify it with primitive `weq` or the later quotient relation.

## 6. Exact read-only dependency plan

The companion JSON is `validator-full-seed-theory222-plan.json`, SHA256
`6a3af976c1889e38db37747c44a5aacfcc97ed5251e6a71f68a7eab2e32335c5`.
The source/header traversal selected **191 cached modules, 136 Foundation
modules, 599 artifacts and 45 explicit external boundaries**. All selected
sources, objects and boundaries were rehashed; 874 observations are saved.
No compiler was invoked and no overlay was constructed.

Relative to the previous full-seed cache this adds nineteen Foundation
modules from the already accepted fixed-consistency73 inventory, generic
`SchemaClosure`, the accepted FullSeed leaf, three accepted source-proof
context/derivation leaves, and EqualityImages. The five additional package
boundaries are `Mathlib.Computability.Halting`,
`Mathlib.Computability.PartrecBasis`, `Mathlib.Data.PFun`,
`Mathlib.Data.Vector.Basic`, and `Mathlib.Logic.Godel.GodelBetaFunction`.
Their exact existing paths/hashes are in the JSON. `Init` and the actual
meta import `Aesop` remain explicit.

Selected final providers:

* FullSeed: `/tmp/validator-source-full-seed222-root-zjtprxm7/lib`, source
  `d3c667ea9d23f0e7e91975bd2967eb8c9c2ebee9b9bb5f4e849430dc81b39c04`,
  object `47bf6d5008afd6356e89a061edee902b728507414feb21d5220b662892e8c9d4`.
* Equality: `/tmp/validator-equality-images222-root-_3yfo2wq/lib`, exact
  source/object and ROOT state pins recorded in the JSON.
* SchemaClosure: the source-identical historical object selected and
  accepted by fixed-consistency73, object
  `1d132a2dd2df2b38440a826bd19b7d35617cde4d0d240da816d66abb3309ab43`.
  Its historical compilation/provenance limitation is retained, not
  relabeled as a fresh current build.
* Nineteen additional Foundation objects: previously authenticated Lake
  source/trace/companions from the accepted fixed-consistency73 inventory;
  no Foundation build is proposed. Existing qualifications about observed
  rather than historically captured companions remain unchanged.

Only the two proposed new leaves would be freshly compiled after approval.
Their outputs must be private regular nonsymlink files; no selected cached
client may import either new leaf. Retain all attempts, actual toolchain
and source/header pins, explicit external paths, pre/post reauthentication,
`-M6000 -j1 -DElab.async=false`, one thread and the 512MiB reserve. No change
to the frozen FullSeed or equality packets is required.
