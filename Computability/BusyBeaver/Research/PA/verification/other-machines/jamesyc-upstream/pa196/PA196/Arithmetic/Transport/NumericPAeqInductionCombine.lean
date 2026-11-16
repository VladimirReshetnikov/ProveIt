module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryEmptyRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionCombine
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary RelationalSource.Numeric PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
noncomputable def combineCode (F B S A T C:V):V :=
  imp L (imp L (qqAnd F B) A) (imp L (imp L (qqAnd F S) T)
    (imp L (imp L (qqAnd A T) C) (imp L F (imp L B (imp L S C)))))
noncomputable def combineProof (F B S A T C:SF (V:=V) 0):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅
      (((F ⋏ B) 🡒 A) 🡒 (((F ⋏ S) 🡒 T) 🡒 (((A ⋏ T) 🡒 C) 🡒 (F 🡒 (B 🡒 (S 🡒 C)))))) := by
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  let Γ:ND.Seq (V:=V) := insert (∼S) (insert (∼B) (insert (∼F)
    (insert (∼((A ⋏ T) 🡒 C)) (insert (∼((F ⋏ S) 🡒 T)) (insert (∼((F ⋏ B) 🡒 A)) ∅)))))
  have hF:ND.Proof (T:=(∅:Theory L).internalize V) Γ F := ND.assumption _ (by simp [Γ])
  have hB:ND.Proof (T:=(∅:Theory L).internalize V) Γ B := ND.assumption _ (by simp [Γ])
  have hS:ND.Proof (T:=(∅:Theory L).internalize V) Γ S := ND.assumption _ (by simp [Γ])
  have hA:ND.Proof (T:=(∅:Theory L).internalize V) Γ ((F ⋏ B) 🡒 A) := ND.assumption _ (by simp [Γ])
  have hT:ND.Proof (T:=(∅:Theory L).internalize V) Γ ((F ⋏ S) 🡒 T) := ND.assumption _ (by simp [Γ])
  have hC:ND.Proof (T:=(∅:Theory L).internalize V) Γ ((A ⋏ T) 🡒 C) := ND.assumption _ (by simp [Γ])
  exact ND.mp (ND.andIntro (ND.mp (ND.andIntro hF hB) hA) (ND.mp (ND.andIntro hF hS) hT)) hC

theorem combineCode_valid {F B S A T C:V} (hF:IsFormula L F) (hB:IsFormula L B)
    (hS:IsFormula L S) (hA:IsFormula L A) (hT:IsFormula L T) (hC:IsFormula L C):
    IsFormula L (combineCode F B S A T C) := by
  unfold combineCode
  exact IsSemiformula.imp.mpr ⟨IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF,hB⟩,hA⟩,
    IsSemiformula.imp.mpr ⟨IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hF,hS⟩,hT⟩,
      IsSemiformula.imp.mpr ⟨IsSemiformula.imp.mpr ⟨IsSemiformula.and.mpr ⟨hA,hT⟩,hC⟩,
        IsSemiformula.imp.mpr ⟨hF,IsSemiformula.imp.mpr ⟨hB,IsSemiformula.imp.mpr ⟨hS,hC⟩⟩⟩⟩⟩⟩

theorem combine_requested_certificate (F B S A T C native lo z:V)
    (hF:IsFormula L F) (hB:IsFormula L B) (hS:IsFormula L S)
    (hA:IsFormula L A) (hT:IsFormula L T) (hC:IsFormula L C)
    (hc:FormulaCovered 0 native lo z (combineCode F B S A T C)):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (combineCode F B S A T C)+1 := by
  exact empty_requested_certificate _ (combineProof ⟨F,hF⟩ ⟨B,hB⟩ ⟨S,hS⟩ ⟨A,hA⟩ ⟨T,hT⟩ ⟨C,hC⟩) native lo z hc
#print axioms combineProof
#print axioms combineCode_valid
#print axioms combine_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqInductionCombine

