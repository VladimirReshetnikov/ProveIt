import ZFCinPA.ValidatorEnvironmentSubstitution222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorFormulaEncoder222 ValidatorEnvironmentSubstitution222
open ValidatorEnvironmentSubstitution254 (Matches matches_qVec)
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_label_opening {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F : V) :
    encode (0∷F) 0 0 (free ℒₛₑₜ p)=encode F (0∷0) 0 p := encode_free hp F 0 0

theorem fallback_one {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (index s : V) :
    encode 0 0 s (substs1 ℒₛₑₜ (^&index) p)=encode 0 (1∷0) s p := by
  simpa using encode_substs1_fvar hp 0 index s

theorem repeated_zero_labels {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p) (s : V) :
    encode (0∷0) 0 s (subst ℒₛₑₜ (^&0∷^&0∷0) p)=encode (0∷0) (0∷0∷0) s p := by
  simpa using encode_subst_pair hp
    (show IsSemiterm ℒₛₑₜ 0 (^&0 : V) by simp)
    (show IsSemiterm ℒₛₑₜ 0 (^&0 : V) by simp) (0∷0) 0 s

/-- The replacement is typed at depth3 but the label stack is empty. -/
theorem short_stack {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F s : V) :
    encode F 0 s (subst ℒₛₑₜ (^#2∷0) p)=encode F (0∷0) s p := by
  have h23 : (2 : V)<3 := by
    simpa only [two_add_one_eq_three] using (lt_add_one (2 : V))
  apply encode_subst hp (show IsSemitermVec ℒₛₑₜ 1 3 (^#2∷0 : V) by simp [h23])
  intro i hi
  have hi0 : i=0 := by simpa using hi
  subst i
  simp

theorem twice_pushed {n m F B B' w : V} (hw : IsSemitermVec ℒₛₑₜ n m w)
    (he : Matches F B B' n w) (s : V) :
    Matches F ((s+2)∷s∷B) ((s+2)∷s∷B') ((n+1)+1) (qVec ℒₛₑₜ (qVec ℒₛₑₜ w)) :=
  matches_qVec hw.qVec (matches_qVec hw he s) (s+2)

theorem malformed_zero_separate (F B s : V) : encode F B s 0=0 := encode_zero F B s

#print axioms ValidatorEnvironmentSubstitution222.encode_subst
#print axioms ValidatorEnvironmentSubstitution222.encode_subst_pair
#print axioms encode_substs1
#print axioms encode_substs1_fvar
#print axioms encode_free
#print axioms encode_all_opened
#print axioms encode_exs_opened
#print axioms zero_label_opening
#print axioms fallback_one
#print axioms repeated_zero_labels
#print axioms short_stack
#print axioms twice_pushed
#print axioms malformed_zero_separate
end LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution222Checks
