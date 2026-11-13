import DiophantineConsistency.PRAWitnessZFCAxioms
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Bounds for the two universal-quantifier code constructions inside
Foundation's actual induction-body graph. No whole-graph bound is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PA196InductionBodyAll
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessCalculus
open DiophantineConsistency.PRAWitnessArithmetic DiophantineConsistency.PRAWitnessTransfer
open DiophantineConsistency.PRAWitnessBoundTerms DiophantineConsistency.PRAWitnessPR
open DiophantineConsistency.PRAWitnessZFCAxioms DiophantineConsistency.PRAWitnessFormulaFunctions
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- The two exact universal-quantifier code subgraphs. -/
noncomputable def graphFirst : ArithmeticSemisentence 6 := Rewriting.subst qqAllDef.val ![#0,#1]
noncomputable def graphSecond : ArithmeticSemisentence 7 := Rewriting.subst qqAllDef.val ![#0,#6]
noncomputable def actualFirst : ArithmeticSemisentence 6 :=
  match indBodyValGraph.val with
  | .exs (.and _ (.exs (.and _ (.exs (.and _ (.exs (.and head _))))))) => head
  | _ => ⊥
noncomputable def actualSecond : ArithmeticSemisentence 7 :=
  match indBodyValGraph.val with
  | .exs (.and _ (.exs (.and _ (.exs (.and _ (.exs (.and _ (.exs (.and head _))))))))) => head
  | _ => ⊥
/-- The precise existential scopes and remaining conjunctions. -/
noncomputable def actualFirstExists : ArithmeticSemisentence 5 :=
  match indBodyValGraph.val with
  | .exs (.and _ (.exs (.and _ (.exs (.and _ (body)))))) => body
  | _ => ⊥
noncomputable def actualFirstTail : ArithmeticSemisentence 6 :=
  match indBodyValGraph.val with
  | .exs (.and _ (.exs (.and _ (.exs (.and _ (.exs (.and _ tail))))))) => tail
  | _ => ⊥

noncomputable def actualSecondExists : ArithmeticSemisentence 6 :=
  match indBodyValGraph.val with
  | .exs (.and _ (.exs (.and _ (.exs (.and _ (.exs (.and _ (body)))))))) => body
  | _ => ⊥
noncomputable def actualSecondTail : ArithmeticSemisentence 7 :=
  match indBodyValGraph.val with
  | .exs (.and _ (.exs (.and _ (.exs (.and _ (.exs (.and _ (.exs (.and _ tail))))))))) => tail
  | _ => ⊥

theorem tails_exact : actualFirstTail = actualSecondExists := by rfl

theorem firstExists_exact : actualFirstExists = ∃⁰ (graphFirst ⋏ actualFirstTail) := by rfl
theorem secondExists_exact : actualSecondExists = ∃⁰ (graphSecond ⋏ actualSecondTail) := by rfl

theorem firstTail_sigma : Hierarchy 𝚺 1 actualFirstTail := by
  simp [actualFirstTail, indBodyValGraph]
theorem secondTail_sigma : Hierarchy 𝚺 1 actualSecondTail := by
  simp [actualSecondTail, indBodyValGraph]

theorem first_exact : actualFirst = graphFirst := by rfl
theorem second_exact : actualSecond = graphSecond := by rfl

theorem wb_first : WB M actualFirst := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [first_exact]
  exact wb_rew _ (wb_qqAllDef (M := M))

theorem wb_second : WB M actualSecond := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [second_exact]
  exact wb_rew _ (wb_qqAllDef (M := M))

/-- Bound the first existential while preserving an arbitrary bounded tail. -/
theorem wb_first_exists (tail : ArithmeticSemisentence 6) (hsigma : Hierarchy 𝚺 1 tail)
    (htail : WB M tail) : WB M (∃⁰ (graphFirst ⋏ tail)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllDef (M := M)
  unfold graphFirst
  refine wb_exs_poly _ (by simp [hsigma]) ‘(6 + #0 + 1) * (6 + #0 + 1) + 1’
    (fun V _ _ e u h => ⟨u, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 0)
  · wb_auto

/-- Bound the second existential; its input is the original formula code. -/
theorem wb_second_exists (tail : ArithmeticSemisentence 7) (hsigma : Hierarchy 𝚺 1 tail)
    (htail : WB M tail) : WB M (∃⁰ (graphSecond ⋏ tail)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := DiophantineConsistency.PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllDef (M := M)
  unfold graphSecond
  refine wb_exs_poly _ (by simp [hsigma]) ‘(6 + #5 + 1) * (6 + #5 + 1) + 1’
    (fun V _ _ e u h => ⟨u, ?_, h⟩) ?_
  · have h' := h; simp at h'
    rw [h'.1]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 5)
  · wb_auto

/-- Apply the bounded steps to the exact recognizer subformulas. -/
theorem wb_actualFirstExists (h : WB M actualFirstTail) : WB M actualFirstExists := by
  rw [firstExists_exact]
  exact wb_first_exists actualFirstTail firstTail_sigma h
theorem wb_actualSecondExists (h : WB M actualSecondTail) : WB M actualSecondExists := by
  rw [secondExists_exact]
  exact wb_second_exists actualSecondTail secondTail_sigma h

theorem wb_both_actualExists (h : WB M actualSecondTail) : WB M actualFirstExists := by
  apply wb_actualFirstExists
  rw [tails_exact]
  exact wb_actualSecondExists h

#print axioms wb_both_actualExists
#print axioms wb_actualFirstExists
#print axioms wb_actualSecondExists
#print axioms first_exact
#print axioms second_exact
#print axioms wb_first
#print axioms wb_second
#print axioms wb_first_exists
#print axioms wb_second_exists
end PA196InductionBodyAll
