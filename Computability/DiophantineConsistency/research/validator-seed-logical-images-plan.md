# Next source checkpoint after the actual GIC images

This is a read-only implementation proposal, not an additional proof. The
recommended next pair is `ValidatorSeedLogicalImages222.lean` and focused
Checks, with the single import `ZFCinPA.ValidatorSeedGicImages222`. It closes
the finite equality/irreflexivity parts of the moving-marker image contract
and combines them with the already proved, internally unbounded GIC schema.
The resulting theory is deliberately smaller than `NativeSet.nativeTheory`.

## 1. Concrete theory and proposed endpoints

Work over `{V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* IΣ₁]`, retaining the
universe-0 boundary of the imported `NativePeel` helper. All formula codes,
marker labels, derivation codes and GIC closure counts remain elements of V;
no standardness restriction is imposed on them.

Use the existing `ValidatorFullSeedTheory222.irreflexiveSentence` unchanged.
Define a new, explicitly named theory in the new namespace:

```lean
def logicalTheory : SetTheory :=
  ((𝗘𝗤 ℒₛₑₜ) ∪ {irreflexiveSentence}) ∪ gicTheory
instance logicalTheory_delta1 : logicalTheory.Δ₁ :=
  (ValidatorEqualityImages222.equalityDelta.add
    (Theory.Δ₁.singleton irreflexiveSentence)).add gicTheory_delta1
```

The intended main interfaces are:

```lean
theorem equality_image (σ : SetTheorySentence) (hσ : σ ∈ 𝗘𝗤 ℒₛₑₜ) (j : V) :
  Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜σ⌝ : V)))

theorem irreflexivity_image (j : V) :
  Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜irreflexiveSentence⌝ : V)))

theorem axiomImages_equality :
  letI := ValidatorEqualityImages222.equalityDelta
  AxiomImages (𝗘𝗤 ℒₛₑₜ) V

theorem axiomImages_logicalTheory : AxiomImages logicalTheory V

theorem provable_falsum_of_logicalTheory
    (h : Provable logicalTheory (^⊥ : V)) :
  Provable seedTheory (^⊥ : V)

theorem logicalTheory_refutation_witness [V↓[ℒₒᵣ] ⊧* IΣ₂]
    (h : Provable logicalTheory (^⊥ : V)) :
  ∃ d : V, ArithmeticHistory222.value d = 2
```

The five individual literal image theorems may be public for checking. The
strong image formulas above hold for every marker j, including 0; the final
`AxiomImages` contract still retains its exact `p < j` argument. Neither that
argument nor the source axiom-image resource is replaced by a proof-transform
oracle. The last endpoint uses the already imported actual seed interpreter;
only it needs IΣ₂. It does not mention ZF, ZFC, or a Diophantine equation.

## 2. Literal finite cases and proof construction

The actual `Foundation.FirstOrder.Basic.Eq` defines the source theory by
`Theory.eqAxiom`, with cases refl, symm, trans, funcExt, relExt. The set language
has no functions and exactly equality/membership relation symbols, leaving
five cases. Their fully closed binders and normalized matrix shapes are:

| Actual source sentence | Universal binders | Matrix before closing |
| --- | ---: | --- |
| `Theory.Eq.refl ℒₛₑₜ` | 1 | `#0 = #0` |
| `Theory.Eq.symm ℒₛₑₜ` | 2 | `#1 = #0 → #0 = #1` |
| `Theory.Eq.trans ℒₛₑₜ` | 3 | `#2 = #1 → #1 = #0 → #2 = #0` |
| `Theory.Eq.relExt Language.Eq.eq` | 4 | `(#0=#2 ∧ (#1=#3 ∧ ⊤)) → #0=#1 → #2=#3` |
| `Theory.Eq.relExt Language.Set.Rel.mem` | 4 | `(#0=#2 ∧ (#1=#3 ∧ ⊤)) → #0∈#1 → #2∈#3` |
| `irreflexiveSentence` | 1 | `#0∈#0 → ⊥` |

The table is a binding target, not permission to substitute extensionally
similar axioms: each implementation/check must relate the actual quotation
and its exact binder order by definitional equality or the existing quotation
lemmas. In particular retain the terminal `⊤` in `Matrix.conj`; after NNF
negation its dual terminal is `⊥`.

A direct source proof avoids importing or asserting the desired interpretations:

1. Each original closed equality sentence is literally a member of
   `seedTheory`, by the first union component; irreflexivity is literally in its
   singleton component. Use `Δ₁Class.mem_iff`, `TProof.byAxm` or the explicit
   internal axiom constructor. This produces the original source proof, not a
   proof of its relativization.
2. For the fixed matrix b and binder count k from the table, bind its original
   source code to `qqAlls b k`. `ModelCodedSpecialization.specializedProofCode_isProof`
   (lines 268 onward) takes its actual proof code and yields a proof of
   `subst ℒₛₑₜ (fvarVec k) b`. The iterator is total on raw inputs and its
   correctness theorem applies in arbitrary IΣ₁ models. No new iterator is
   necessary.
3. The opened matrices contain only atoms, negative atoms, truth/falsity and
   propositional connectives. `tagRel` therefore leaves each matrix exactly
   unchanged; establish this finite syntactic equality using the existing
   `relativize_rel/nrel/and/or/verum/falsum` equations. There is no universal
   preservation lemma for arbitrary source formulas being assumed here.
4. Weaken the opened proof by `emptyCode (j+k)`. Invoke the accepted
   `ValidatorSeedGicImages222.close_guarded` with `m=k`. Its hypotheses are the
   actual typing of b and `shift b=b`, established for these closed matrices.
   The marker moves from `j+k` to j through the existing checked induction.
   Only the matrix is shift-fixed; the marker/domain are not.
5. Convert the guarded implication to the exact `AxiomImages` sequent using
   the same explicit EM resource and `NativePeel.derivable_mp` pattern as
   `axiomImages_gicTheory`. This use of source classical proof rules is
   permitted by the PA-to-HA route; it is not an additional HA axiom.

An alternative finite typed specialization/reclosure is possible if its literal
bindings are clearer. It must preserve the same six source sentences and not
use the earlier C222 equality images as source derivations. Those earlier
images establish `CProv (encode ... σ)` via Eind; they are a different target.
No theorem identifies Eind with primitive numeric equality or coded Eqv.

The explicit Δ₁ recognizer matters. Reuse
`ValidatorEqualityImages222.mem_ch_ofFinite` (line 173) with its actual
`equalityDelta` (line 155), not arbitrary Δ₁ membership. Extract the internal
code as the quotation of one of the five real standard axioms, then eliminate
`Theory.eqAxiom` and the empty function-symbol case. For `logicalTheory`,
normalize its specified nested `.add` recognizer into the equality,
irreflexivity, or actual GIC branch; use `axiomImages_gicTheory` directly in the
last branch. This yields a concrete, discharged image resource.

Finally apply `ValidatorSeedMarkerRelativization222.provable_falsum_of_tagged`
and its existing `refutation_witness`. There is no remaining `hAx` premise in
the proposed concrete-theory corollaries, although it remains explicit in the
underlying generic theorem.

## 3. What the quotient route actually still requires

`KQHyp.QHyp` is the relevant contract. Its source file explicitly says the
tagged domain lacks the literal power-container axiom of CP/GIC models. It
requires all nine fields: GIC; reflexivity, symmetry and transitivity of coded
bisimilarity Eqv; Eqv extensionality for interpreted membership; profile pairs;
interpreted union; interpreted power; and singleton-closed containers.

The distinctions are concrete:

* `ProfileCollection.Eqv` (line 108) is a coded bisimulation relation. It is
  not raw source equality and is not C222 Eind.
* `ProfileComposition.Member` (line 262) is raw membership followed by Eqv.
  It is not raw source membership. `KQ1Model.memberForm` (line 49) is its
  explicit first-order formula, while `ProfileSyntax.eqvForm` (line 74) is the
  explicit bisimulation formula.
* `KLowerEqv.tag_refl` needs a tagged transitive container, ordered pairs, and
  a diagonal collection instance. Symmetry uses reverse collection;
  transitivity uses fiber/composition/union instances; extensionality uses
  union/match/backMatch. GIC alone does not discharge their other hypotheses.
* `KLowerQHyp.tag_qhyp` (line 228) also uses interpreted union, power and
  singleton closure. Its power proof retains envelopes and separation of
  tagged representatives. There is no justified substitution of raw CP.
* `KQ1ZF.zfAxioms`, `closedWF`, `nonempty`, and `zf_consistent` are semantic
  results for the QHyp quotient and its internally well-founded part. The
  last theorem rejects ordinary external `BProv ZFax_s [] fBot`; it does not
  transport an arbitrary internally coded Foundation derivation in an
  arbitrary arithmetic model.

The first concrete set-theory prerequisite after this proposed finite logical
pair should be a separate raw-transitive/tagged-transitive source proof pair.
`KLowerRaw.raw_transitive` (lines 88–99) uses a singleton of a, the full-seed
singleton matrix, then singleton uniqueness twice. Its closure step uses the
full `clos` component, not just the projected image. The existing full-seed
source endpoint retained exactly that resource. `KLowerTag.tag_transitive`
(lines 122–129) then cuts the raw transitive envelope by the already proved
guarded comprehension. Its future source target has the shape

```
Empty(t) → t∈a → ∃v, t∈v ∧ a∈v ∧
  ∀y, (t∈y ∧ y∈v) → ∀z, (t∈z ∧ z∈y) → z∈v.
```

This is a proposed later proof target, not proved by this plan. It retains
arbitrary source parameters. Exact tagged pairs are another finite prerequisite
from raw pairs plus the same guarded cut. The proper profile-source images can
then be built from those finite resources and actual internally represented
GIC instances. No transitive-container or pair premise should be silently
added to the eventual actual seed-to-ZF theorem.

## 4. Existing machinery that can be reused, and its boundaries

`InternalInterpretation.interp` already represents simultaneous domain/atom
interpretation. Its `Good` requires a shift-fixed one-slot domain and both
shift-fixed two-slot atom meanings. Its actual `derivable_iSet` and
`provable_falsum_of_interp` accept explicit all-internal axiom images and domain
nonemptiness. This is suitable for a later **closed** Eqv/Member/WF
interpretation once the actual source theory and images have been supplied.
It is unsuitable for `domainCode j` with a free moving marker. The accepted
marker-family theorem supplies that distinct first stage.

`NativeInterp` has concrete closed `eqS`, `memS`, `domS` formulas and the
right syntactic pattern. However its semantic environment assumes
`NativeSet.nativeTheory`, whose fixed axioms include the literal
`containerAx`. `NativeSchema`/the old R2 source proofs do not automatically
apply to the smaller `logicalTheory`. They are guides for a QHyp-based
adaptation, not theorem aliases or usable missing-image oracles.

`OpenTemplateClosure.closeTemplate` can retain every free parameter of an
arbitrary internal matrix while closing finitely many ordinary source slots.
It is useful once an actual open template proof is available. It does not
itself provide that proof or close an arbitrarily long internal schema prefix.
The existing represented schema/peeling helpers can supply the latter once
the correct closed interpretation hypotheses fit.

`SetPlaceholderQuotient.complete_underSetPlaceholderCongruence` specifically
uses `templateZFC`; it cannot be invoked on a merely intended QHyp theory.
A finite semantic argument can yield a finite source proof through the actual
completeness/template compiler when its exact theory hypotheses are verified.
That does not eliminate the separate uniform internal matrix and recognizer
obligations. No standard NatForm semantic guide has been promoted here.

Choice already has a genuine all-internal route:
`LSchema.provable_falsum_ZF_of_ZFC` (line 57), in every IΣ₁ model, maps actual
Foundation ZFC refutations to actual Foundation ZF refutations. It discharges
its separation/replacement images in `hSchema` and then uses
`ConstructibleInterpretation`. Thus the needed future chain is ZFC→ZF→a
proper QHyp/WF-interpreted source theory→seed→C222. The middle ZF calibration
remains open. No new semantic Choice argument is needed for this plan.

## 5. Focused checks and exact cache boundary

Checks should bind all six literal source quotations and their 1/2/3/4-slot
bodies, both relation symbols, the terminal conjunction truth and falsity,
arbitrary internal j (including 0), and the exact finite-recognizer and
nested-union interfaces. Check both concrete refutation endpoints with no
axiom-image premise; the C222 endpoint must retain IΣ₂. Print axioms for the
six images, combined image resource, and refutation compositions. The future
pair must not import NativeTheory, NativeInterp, or LSchema merely to state
its limited result.

The complete read-only cache audit is
`validator-seed-logical-images-plan.json`, SHA256
`5a49e8f9459aa982d6e7fed9cf7ef082f5683340f3e8bbce3264f88fc3765054`.
It verifies 5,253 distinct path/hash observations, the exact reachable import
DAG and all 669 first artifact providers:

* 216 cached modules, including 136 Foundation modules;
* 624 custom cache artifacts and 45 explicit external boundaries;
* zero prerequisite refresh; only the eventual two new leaves would compile;
* sole new main import: `ZFCinPA.ValidatorSeedGicImages222`;
* selected accepted GIC provider:
  `/tmp/validator-seed-gic-images222-root-6oypgnsu/lib`;
* accepted ROOT packet `b474ac9fdcb1605fb958580f987ebfd0b0b5b85ce5ad92cce4577d23279820b7`
  and 13-file manifest `ced832bf35bf2f175378162c62d2e217928b7ec4dc73a0a6d3b1fccf0a90062e`;
* GIC main source `4a31b40bfb4fa78d61f77f095c09aabfb69b4addac61213552f691284d5e9643`,
  primary object `49a2dcac0ad06bb84cac793a9ec2c18073cf78c5327c997b994e03897d8dd860`.

The selected search path is the accepted explicit ROOT overlay followed by
package boundaries only. Six historical fallback roots are absent. Prior
source/trace/run and missing-companion qualifications remain recorded in the
inherited module records; no new cache provenance is fabricated. The pinned
semantic guide sources outside this dependency DAG have source-only status.
No Lean source, overlay, compiler command, or dependency refresh was created
or executed for this proposal. The read-only auditor passed on its first run.
Only the proposed two-leaf scope is ready for review; later QHyp/WF clients
need their own dependency and theorem-contract audit before implementation.
