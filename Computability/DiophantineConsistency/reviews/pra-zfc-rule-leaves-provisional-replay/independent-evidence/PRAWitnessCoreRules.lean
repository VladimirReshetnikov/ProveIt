import DiophantineConsistency.PRAWitnessDerivationCoreLeft
import DiophantineConsistency.PRAWitnessRefutationOuter

/-! Collect bounds for the individual derivation-rule disjuncts. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessCoreRules
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCalculus
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- The positive disjunction is bounded when each top-level disjunct is. -/
def PositiveLeaves {n : ℕ} (φ : ArithmeticSemisentence n) : Prop :=
  match φ with
  | .or a b => PositiveLeaves a ∧ PositiveLeaves b
  | φ => WB M φ

/-- The negation of a disjunction is bounded when each negated leaf is. -/
def NegativeLeaves {n : ℕ} (φ : ArithmeticSemisentence n) : Prop :=
  match φ with
  | .or a b => NegativeLeaves a ∧ NegativeLeaves b
  | φ => WB M (∼φ)

theorem wb_positive_of_leaves {n : ℕ} : ∀ φ : ArithmeticSemisentence n,
    PositiveLeaves (M := M) φ → WB M φ
  | .or a b, h => wb_or (wb_positive_of_leaves a h.1) (wb_positive_of_leaves b h.2)
  | .verum, h => h
  | .falsum, h => h
  | .rel _ _, h => h
  | .nrel _ _, h => h
  | .and _ _, h => h
  | .all _, h => h
  | .exs _, h => h

theorem wb_negative_of_leaves {n : ℕ} : ∀ φ : ArithmeticSemisentence n,
    NegativeLeaves (M := M) φ → WB M (∼φ)
  | .or a b, h => by
      change WB M (∼a ⋏ ∼b)
      exact wb_and (wb_negative_of_leaves a h.1) (wb_negative_of_leaves b h.2)
  | .verum, h => h
  | .falsum, h => h
  | .rel _ _, h => h
  | .nrel _ _, h => h
  | .and _ _, h => h
  | .all _, h => h
  | .exs _, h => h

section candidate
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessDerivationCoreLeft
variable {N : Type} [Nonempty N] [Structure language N] [Structure.Eq language N]
  [N↓[language] ⊧* PRA]
local instance : Zero N := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One N := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add N := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul N := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT N := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The actual sigma core follows from the positive rule-leaf bounds. -/
theorem wb_coreSigma_of_leaves (T : SetTheory) [T.Δ₁]
    (h : PositiveLeaves (M := N) (sigmaTail T)) :
    WB N (Derivation.blueprint T).core.sigma.val := by
  letI : N↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact wb_coreSigma_of_tail T (wb_positive_of_leaves _ h)

/-- The actual negated pi core follows from the negative rule-leaf bounds. -/
theorem wb_neg_corePi_of_leaves (T : SetTheory) [T.Δ₁]
    (h : NegativeLeaves (M := N) (piTail T)) :
    WB N (∼(Derivation.blueprint T).core.pi.val) := by
  letI : N↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : N↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact wb_neg_corePi_of_tail T (wb_negative_of_leaves _ h)
end candidate

section allModels
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessDerivationCoreLeft
  PRAWitnessRefutationOuter PRAStrictConReverse
local instance {N : Type} [Structure language N] : Zero N := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {N : Type} [Structure language N] : One N := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {N : Type} [Structure language N] : Add N := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {N : Type} [Structure language N] : Mul N := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {N : Type} [Structure language N] : LT N := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- A fixed proof predicate's PRA certificate follows from bounds on every
positive and negative rule disjunct in each candidate model. -/
theorem certificate_of_rule_leaves (T : SetTheory) [T.Δ₁] (σ : SetTheorySentence)
    (hpos : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], PositiveLeaves (M := N) (sigmaTail T))
    (hneg : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], NegativeLeaves (M := N) (piTail T)) :
    BoundCertificate (provabilityPred T σ) := by
  apply certificate_of_core T σ
  · intro N _ _ _ _
    exact wb_coreSigma_of_leaves T (hpos N)
  · intro N _ _ _ _
    exact wb_neg_corePi_of_leaves T (hneg N)
end allModels
end DiophantineConsistency.PRAWitnessCoreRules
