import PAFlexibleOutput.Arithmetization
import PAFlexibleOutput.Functionality
import PAFlexibleOutput.Refutations
import PAFlexibleOutput.Search
import PAFlexibleOutput.MathlibAssembly

/-!
# A divergent program whose every output is possible in a model of `𝗣𝗔`

The main theorem of the project. There is a partial recursive function `f : ℕ →. ℕ`, given by a
program `e`, such that for every `o : Option ℕ` some model of `𝗣𝗔` satisfies "`f 0 = o`":

* for `o = some n` the model satisfies the halting sentence `haltSentence e 0 n`, and `n` is
  then the *only* output of `e` on input `0` in that model;
* for `o = none` the model satisfies `divergeSentence e 0`: no element of the model is an
  output. The standard model `ℕ` is such a model, because `e` really diverges.

## Statements

* `flexibleOutput`: the sentence form, with `outputSentence e o`.
* `flexibleOutputValue`: the semantic form, with `ValueIn M e o`, which says that the value of
  `e` on input `0` computed inside `M` is `o`.
* `exists_partrec_flexibleOutput`: the same, stated for the partial recursive function.
* `mainClaim`, `strongClaim`, `fullySpecifiedMainClaim`: the three propositions named in
  `PAFlexibleOutput.Statement`.

## Proof

`paBridge` instantiates the abstract `FlexibleOutputMathlib.ArithmeticBridge` with `𝗣𝗔`:

* consistency is soundness in `ℕ`;
* `finiteComputation` is `finiteProofAdequacy` (`𝚺₁`-completeness);
* `modelOfUnrefuted` is the completeness theorem.

`exists_searchImplementation` builds the proof search from `refutationsRE` and `exists_search`.
The recursion-theorem argument is `FlexibleOutputMathlib.exists_program_with_arbitrary_possible_output`.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ## The arithmetic bridge -/

/-- A model of `𝗣𝗔` with a small carrier, bundled. -/
structure PAModel : Type 1 where
  /-- The carrier. -/
  carrier : Type
  [oring : ORingStructure carrier]
  [models : carrier↓[ℒₒᵣ] ⊧* 𝗣𝗔]

attribute [instance] PAModel.oring PAModel.models

/-- `𝗣𝗔` as an instance of the abstract bridge of `MathlibAssembly`. -/
noncomputable def paBridge : FlexibleOutputMathlib.ArithmeticBridge.{0, 1} where
  Sentence := ArithmeticSentence
  Model := PAModel
  halts := haltSentence
  neg := fun σ => ∼σ
  provable := fun σ => 𝗣𝗔 ⊢ σ
  isModel := fun _ => True
  realizes := fun M σ => M.carrier↓[ℒₒᵣ] ⊧ σ
  consistent := fun p hp hnp => by
    have h₁ : ℕ↓[ℒₒᵣ] ⊧ p := models_of_provable (M := ℕ) inferInstance hp
    have h₂ : ℕ↓[ℒₒᵣ] ⊧ ∼p := models_of_provable (M := ℕ) inferInstance hnp
    exact Semantics.Not.models_not.mp h₂ h₁
  finiteComputation := fun h => finiteProofAdequacy _ _ _ h
  modelOfUnrefuted := fun p h => by
    by_contra hno
    refine h (Arithmetic.complete.{0} 𝗣𝗔 (∼p) fun M _ _ => ?_)
    exact Semantics.Not.models_not.mpr fun hp => hno ⟨⟨M⟩, trivial, hp⟩

/-- The proof search: a partial recursive function that returns an output refuted by `𝗣𝗔`
whenever there is one. -/
theorem exists_searchImplementation :
    Nonempty (FlexibleOutputMathlib.SearchImplementation paBridge) := by
  have hR : REPred (fun p : Code × ℕ => 𝗣𝗔 ⊢ ∼(haltSentence p.1 0 p.2)) := refutationsRE
  obtain ⟨search, hpart, hign, hsound, hcomplete⟩ := exists_search hR
  exact ⟨{
    search := search
    partialRecursive := hpart
    ignoresInput := hign
    returnsRefutation := fun h => hsound h
    findsRefutation := fun h => hcomplete h }⟩

/-! ## The sentence form -/

/-- The sentence "the value of program `e` on input `0` is `o`": the halting sentence for
`o = some n`, the divergence sentence for `o = none`. -/
noncomputable def outputSentence (e : Code) : Option ℕ → ArithmeticSentence
  | some n => haltSentence e 0 n
  | none => divergeSentence e 0

/-- **Main theorem, sentence form.** There is a program `e` that diverges on every input, such
that for every `o : Option ℕ` some model of `𝗣𝗔` satisfies "the value of `e` on input `0` is
`o`". -/
theorem flexibleOutput :
    ∃ e : Code, Partrec (Nat.Partrec.Code.eval e) ∧
      (∀ x : ℕ, ¬ (Nat.Partrec.Code.eval e x).Dom) ∧
      ∀ o : Option ℕ, ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔),
        M↓[ℒₒᵣ] ⊧ outputSentence e o := by
  obtain ⟨S⟩ := exists_searchImplementation
  obtain ⟨e, hpart, hdiv, hmod⟩ :=
    FlexibleOutputMathlib.exists_program_with_arbitrary_possible_output S
  have hdiv' : ∀ x : ℕ, ¬ (Nat.Partrec.Code.eval e x).Dom := fun x hx => by
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hx
    exact hdiv x y hy
  refine ⟨e, hpart, hdiv', ?_⟩
  rintro (_ | n)
  · exact ⟨ℕ, inferInstance, inferInstance, (standardDivergence e 0).mpr (hdiv' 0)⟩
  · obtain ⟨M, -, hM⟩ := hmod n
    exact ⟨M.carrier, M.oring, M.models, hM⟩

/-! ## The semantic form -/

/-- `y` is an output of program `e` on input `0`, computed inside the structure `M`. -/
def OutputIn (M : Type*) [ORingStructure M] (e : Code) (y : M) : Prop :=
  M ⊧/![y, ORingStructure.numeral (Encodable.encode e), ORingStructure.numeral 0] universalGraph

/-- The value of program `e` on input `0`, computed inside `M`, is `o`: for `o = some n` the
numeral `n` is the unique output, and for `o = none` there is no output. -/
def ValueIn (M : Type*) [ORingStructure M] (e : Code) : Option ℕ → Prop
  | some n => ∀ y : M, OutputIn M e y ↔ y = ORingStructure.numeral n
  | none => ∀ y : M, ¬ OutputIn M e y

section

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma outputIn_iff (e : Code) (y : M) :
    OutputIn M e y ↔
      (M ⊧/![y, ((Encodable.encode e : ℕ) : M), ((0 : ℕ) : M)] universalGraph) := by
  unfold OutputIn
  rw [numeral_eq_natCast_app, numeral_eq_natCast_app]

/-- A structure that satisfies `outputSentence e o` computes the value `o`. The uniqueness of
the output is the functionality of the halting formula. -/
theorem valueIn_of_models (e : Code) (o : Option ℕ) (h : M↓[ℒₒᵣ] ⊧ outputSentence e o) :
    ValueIn M e o := by
  cases o with
  | none =>
    show ∀ y : M, ¬ OutputIn M e y
    intro y hy
    exact (models_divergeSentence e 0).mp h ⟨y, (outputIn_iff e y).mp hy⟩
  | some n =>
    show ∀ y : M, OutputIn M e y ↔ y = ORingStructure.numeral n
    intro y
    have hn := (models_haltSentence e 0 n).mp h
    rw [numeral_eq_natCast_app]
    constructor
    · intro hy
      exact universalGraph_uniq ((outputIn_iff e y).mp hy) hn
    · rintro rfl
      exact (outputIn_iff e _).mpr hn

end

/-- **Main theorem, semantic form.** There is a program `e` that diverges on every input, such
that for every `o : Option ℕ` there is a model of `𝗣𝗔` in which the value of `e` on input `0` is
`o`. -/
theorem flexibleOutputValue :
    ∃ e : Code, Partrec (Nat.Partrec.Code.eval e) ∧
      (∀ x : ℕ, ¬ (Nat.Partrec.Code.eval e x).Dom) ∧
      ∀ o : Option ℕ, ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔),
        ValueIn M e o := by
  obtain ⟨e, hpart, hdiv, hmod⟩ := flexibleOutput
  refine ⟨e, hpart, hdiv, fun o => ?_⟩
  obtain ⟨M, inst, hM, ho⟩ := hmod o
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) hM
  exact ⟨M, inst, hM, valueIn_of_models e o ho⟩

/-- **Main theorem.** There is a partial recursive function `f : ℕ →. ℕ` such that for every
`o`, a natural number or `none`, the statement "`f 0 = o`" holds in some model of `𝗣𝗔`. The
function is given by a program `e`, and the statement is read inside the model through the
halting formula of that program. -/
theorem exists_partrec_flexibleOutput :
    ∃ f : ℕ →. ℕ, Partrec f ∧ ∃ e : Code, Nat.Partrec.Code.eval e = f ∧
      ∀ o : Option ℕ, ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔),
        ValueIn M e o := by
  obtain ⟨e, hpart, -, hmod⟩ := flexibleOutputValue
  exact ⟨Nat.Partrec.Code.eval e, hpart, e, rfl, hmod⟩

/-! ## The propositions of `Statement` -/

/-- `Statement.StrongClaim`: the program diverges on every input, and every halting sentence
for input `0` is satisfiable together with `𝗣𝗔`. -/
theorem strongClaim : StrongClaim := by
  obtain ⟨e, -, hdiv, hmod⟩ := flexibleOutput
  refine ⟨e, hdiv, fun n => ?_⟩
  obtain ⟨M, inst, hM, hn⟩ := hmod (some n)
  exact satisfiable_intro M (Semantics.ModelsSet.insert_iff.mpr ⟨hn, hM⟩)

/-- `Statement.MainClaim`. -/
theorem mainClaim : MainClaim := by
  obtain ⟨e, hdiv, hsat⟩ := strongClaim
  exact ⟨e, hdiv 0, hsat⟩

/-- `Statement.FullySpecifiedMainClaim`. -/
theorem fullySpecifiedMainClaim : FullySpecifiedMainClaim :=
  ⟨standardCorrectness, functionalityInPAModels, mainClaim⟩

#print axioms flexibleOutput
#print axioms flexibleOutputValue
#print axioms exists_partrec_flexibleOutput
#print axioms strongClaim
#print axioms mainClaim
#print axioms fullySpecifiedMainClaim

end PAFlexibleOutput
