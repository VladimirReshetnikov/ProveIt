module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextTemplateProof
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqUniversalContextTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqFormulaQuantifierTemplates
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def uniformMatrixCode (H S D P:V):V := imp L H (imp L D (qqOr P S))
noncomputable def uniformCode (H S D P:V):V := qqAll (uniformMatrixCode H S D P)
noncomputable def contextCode (H S D P:V):V := imp L (uniformCode H S D P)
  (imp L H (qqOr (qqAll (imp L D P)) S))
theorem uniformMatrix_val (H S:SF (V:=V) 0) (D P:SF (V:=V) 1):
    (uniformMatrix H S D P).val=uniformMatrixCode H.val S.val D.val P.val := by
  simp [uniformMatrix,uniformMatrixCode,liftClosed_val]
theorem uniform_val (H S:SF (V:=V) 0) (D P:SF (V:=V) 1):
    (uniform H S D P).val=uniformCode H.val S.val D.val P.val := by
  simp [uniform,uniformCode,uniformMatrix_val]
theorem context_val (H S:SF (V:=V) 0) (D P:SF (V:=V) 1):
    (uniform H S D P 🡒 (H 🡒 ((∀¹ (D 🡒 P)) ⋎ S))).val=contextCode H.val S.val D.val P.val := by
  simp [contextCode,uniform_val]
theorem uniformMatrixCode_valid {H S D P:V} (hH:IsFormula L H) (hS:IsFormula L S)
    (hD:IsSemiformula L 1 D) (hP:IsSemiformula L 1 P):IsSemiformula L 1 (uniformMatrixCode H S D P) := by
  let h:SF (V:=V) 0 := ⟨H,by simpa using hH⟩
  let s:SF (V:=V) 0 := ⟨S,by simpa using hS⟩
  let d:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have result := (uniformMatrix h s d p).isSemiformula
  rw [uniformMatrix_val] at result
  simpa using result
theorem contextCode_valid {H S D P:V} (hH:IsFormula L H) (hS:IsFormula L S)
    (hD:IsSemiformula L 1 D) (hP:IsSemiformula L 1 P):IsFormula L (contextCode H S D P) := by
  let h:SF (V:=V) 0 := ⟨H,by simpa using hH⟩
  let s:SF (V:=V) 0 := ⟨S,by simpa using hS⟩
  let d:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have result := (uniform h s d p 🡒 (h 🡒 ((∀¹ (d 🡒 p)) ⋎ s))).isSemiformula
  rw [context_val] at result
  simpa using result
#print axioms uniformMatrix_val
#print axioms uniform_val
#print axioms context_val
#print axioms uniformMatrixCode_valid
#print axioms contextCode_valid
end PA196.Arithmetic.Transport.NumericPAeqUniversalContextTemplate

