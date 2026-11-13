module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeClosureProof
public import M6PA.Calibration.FoundationPAeqCodeSubstitutionAgreement
@[expose] public section
/-! Open successor induction for a matrix extracted from an original closed
witness. Surplus parameters are ignored by proved numeric substitution agreement. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language
local notation "U" => Presentation.ordinaryPAeq

theorem canonical_matrix_opening_eq {m q : V} (hq : IsSemiformula PAeq (m+1) q) :
    subst PAeq (qVec PAeq (fvarVec (matrixParameterCount q))) q=
      subst PAeq (qVec PAeq (fvarVec m)) q := by
  have hn : matrixParameterCount q≤m := (IsSemiformula.all.mpr hq).bv_le
  have hnq := matrixParameterCount_valid hq.isUFormula
  have hwm := target_fvarVec_valid m 0
  have hwn := target_fvarVec_valid (matrixParameterCount q) 0
  apply subst_agree_on_bound hnq hwn.qVec hwm.qVec (le_refl _) (by simpa using hn)
  apply qVec_agree_on_bound hwn hwm (le_refl _) hn
  intro i hi
  rw [nth_fvarVec _ i hi,nth_fvarVec _ i (lt_of_lt_of_le hi hn)]

theorem successor_proof_to_additive {k : V} (hk : IsSemiformula PAeq 1 k)
    (h : Provable U (targetIndBody k)) : Provable U (targetAdditiveBody k) := by
  let p : Bootstrapping.Semiformula V PAeq 1 := ⟨k,by simpa using hk⟩
  have hi : (U).internalize V ⊢ typedInductionBody p :=
    (tprovable_iff_provable (T:=U)).mpr (by simpa [typedInductionBody_val,p] using h)
  have ha : (U).internalize V ⊢ typedAdditiveInductionBody p := by
    cl_prover [hi,induction_body_transport p]
  simpa [typedAdditiveInductionBody_val,p] using (tprovable_iff_provable (T:=U)).mp ha

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem open_successor_induction_provable {m q : V} (hq : IsSemiformula PAeq (m+1) q)
    (hs : shift PAeq q=q) :
    Provable U (targetIndBody (subst PAeq (qVec PAeq (fvarVec m)) q)) := by
  have hnq := matrixParameterCount_valid hq.isUFormula
  have hb := closedSuccessorBody_valid hnq
  have hbs := closedSuccessorBody_shift hnq hs
  have h := (provable_alls_iff_open hb hbs).mp (canonicalSuccessorAxiom_provable hq.isUFormula hs)
  rw [closedSuccessorBody_readback hnq,canonical_matrix_opening_eq hq] at h
  exact h

#print axioms canonical_matrix_opening_eq
#print axioms successor_proof_to_additive
#print axioms open_successor_induction_provable
end M6.PA.FoundationPAeqCode

