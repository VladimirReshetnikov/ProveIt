module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqExistentialInstanceTemplateProof
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqExistentialInstanceTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqFormulaQuantifierTemplates NumericPAeqFormulaLogical
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def uniformMatrixCode (H B D Q P:V):V := imp L H (imp L (qqAnd D Q) (biCode B P))
noncomputable def uniformCode (H B D Q P:V):V := qqAll (uniformMatrixCode H B D Q P)
noncomputable def instanceCode (H B D Q P:V):V := imp L (uniformCode H B D Q P)
  (imp L (qqAnd H (qqExs (qqAnd D Q))) (imp L B (qqExs (qqAnd D P))))
theorem uniformMatrix_val (H B:SF (V:=V) 0) (D Q P:SF (V:=V) 1):
    (uniformMatrix H B D Q P).val=uniformMatrixCode H.val B.val D.val Q.val P.val := by
  simp [uniformMatrix,uniformMatrixCode,biCode,liftClosed_val]
theorem uniform_val (H B:SF (V:=V) 0) (D Q P:SF (V:=V) 1):
    (uniform H B D Q P).val=uniformCode H.val B.val D.val Q.val P.val := by
  simp [uniform,uniformCode,uniformMatrix_val]
theorem instance_val (H B:SF (V:=V) 0) (D Q P:SF (V:=V) 1):
    (uniform H B D Q P 🡒 ((H ⋏ (∃¹ (D ⋏ Q))) 🡒 (B 🡒 (∃¹ (D ⋏ P))))).val=
      instanceCode H.val B.val D.val Q.val P.val := by
  simp [instanceCode,uniform_val]
theorem uniformMatrixCode_valid {H B D Q P:V} (hH:IsFormula L H) (hB:IsFormula L B)
    (hD:IsSemiformula L 1 D) (hQ:IsSemiformula L 1 Q) (hP:IsSemiformula L 1 P):
    IsSemiformula L 1 (uniformMatrixCode H B D Q P) := by
  let h:SF (V:=V) 0 := ⟨H,by simpa using hH⟩
  let b:SF (V:=V) 0 := ⟨B,by simpa using hB⟩
  let d:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let q:SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have result := (uniformMatrix h b d q p).isSemiformula
  rw [uniformMatrix_val] at result
  simpa using result
theorem instanceCode_valid {H B D Q P:V} (hH:IsFormula L H) (hB:IsFormula L B)
    (hD:IsSemiformula L 1 D) (hQ:IsSemiformula L 1 Q) (hP:IsSemiformula L 1 P):
    IsFormula L (instanceCode H B D Q P) := by
  let h:SF (V:=V) 0 := ⟨H,by simpa using hH⟩
  let b:SF (V:=V) 0 := ⟨B,by simpa using hB⟩
  let d:SF (V:=V) 1 := ⟨D,by simpa using hD⟩
  let q:SF (V:=V) 1 := ⟨Q,by simpa using hQ⟩
  let p:SF (V:=V) 1 := ⟨P,by simpa using hP⟩
  have result := (uniform h b d q p 🡒 ((h ⋏ (∃¹ (d ⋏ q))) 🡒 (b 🡒 (∃¹ (d ⋏ p))))).isSemiformula
  rw [instance_val] at result
  simpa using result
#print axioms uniformMatrix_val
#print axioms uniform_val
#print axioms instance_val
#print axioms uniformMatrixCode_valid
#print axioms instanceCode_valid
end PA196.Arithmetic.Transport.NumericPAeqExistentialInstanceTemplate

