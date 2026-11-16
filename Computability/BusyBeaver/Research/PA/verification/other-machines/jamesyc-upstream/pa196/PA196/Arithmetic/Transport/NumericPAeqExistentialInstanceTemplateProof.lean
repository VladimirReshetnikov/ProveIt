module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplatesCode
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqExistentialInstanceTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqFormulaQuantifierTemplates
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def uniformMatrix (H B:SF (V:=V) 0) (D Q P:SF (V:=V) 1):SF (V:=V) 1 :=
  liftClosed H 🡒 ((D ⋏ Q) 🡒 ((liftClosed B 🡒 P) ⋏ (P 🡒 liftClosed B)))
noncomputable def uniform (H B:SF (V:=V) 0) (D Q P:SF (V:=V) 1):SF (V:=V) 0 :=
  ∀¹ uniformMatrix H B D Q P
@[simp] theorem uniform_shift (H B:SF (V:=V) 0) (D Q P:SF (V:=V) 1):
    (uniform H B D Q P).shift=uniform H.shift B.shift D.shift Q.shift P.shift := by
  simp [uniform,uniformMatrix]
noncomputable def instanceProof (H B:SF (V:=V) 0) (D Q P:SF (V:=V) 1):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅
      (uniform H B D Q P 🡒 ((H ⋏ (∃¹ (D ⋏ Q))) 🡒 (B 🡒 (∃¹ (D ⋏ P))))) := by
  apply ND.impIntro
  apply ND.impIntro
  apply ND.impIntro
  let Γ:ND.Seq (V:=V) := insert (∼B) (insert (∼(H ⋏ (∃¹ (D ⋏ Q)))) (insert (∼uniform H B D Q P) ∅))
  have hU : ND.Proof (T:=(∅:Theory L).internalize V) Γ (uniform H B D Q P) := ND.assumption _ (by simp [Γ])
  have hA : ND.Proof (T:=(∅:Theory L).internalize V) Γ (H ⋏ (∃¹ (D ⋏ Q))) := ND.assumption _ (by simp [Γ])
  have hB : ND.Proof (T:=(∅:Theory L).internalize V) Γ B := ND.assumption _ (by simp [Γ])
  apply ND.exsElim (p:=D ⋏ Q) (ND.andRight hA)
  let C:ND.Seq (V:=V) := insert (∼(D ⋏ Q).free) Γ.shift
  let x:ST (V:=V) 0 := Semiterm.fvar 0
  have hV : ND.Proof (T:=(∅:Theory L).internalize V) C ((D ⋏ Q).free) := ND.assumption _ (by simp [C])
  have hH' : ND.Proof (T:=(∅:Theory L).internalize V) C H.shift := ND.up (ND.shift (ND.andLeft hA)) _
  have hB' : ND.Proof (T:=(∅:Theory L).internalize V) C B.shift := ND.up (ND.shift hB) _
  have hU' : ND.Proof (T:=(∅:Theory L).internalize V) C (uniform H.shift B.shift D.shift Q.shift P.shift) := by
    simpa using ND.up (ND.shift hU) (D ⋏ Q).free
  have hAt : ND.Proof (T:=(∅:Theory L).internalize V) C
      (H.shift 🡒 ((D ⋏ Q).free 🡒 ((B.shift 🡒 P.free) ⋏ (P.free 🡒 B.shift)))) := by
    simpa [uniform,uniformMatrix,Bootstrapping.Semiformula.free,x] using ND.allElim hU' x
  have hP := ND.mp hB' (ND.andLeft (ND.mp hV (ND.mp hH' hAt)))
  have hD : ND.Proof (T:=(∅:Theory L).internalize V) C D.free := by
    simpa [Bootstrapping.Semiformula.free] using ND.andLeft (by simpa [Bootstrapping.Semiformula.free] using hV : ND.Proof (T:=(∅:Theory L).internalize V) C (D.free ⋏ Q.free))
  simp only [Bootstrapping.Semiformula.shift_exs,Bootstrapping.Semiformula.shift_and]
  apply ND.exsIntro _ x
  simpa [C,Bootstrapping.Semiformula.free,x] using ND.andIntro hD hP
#print axioms uniform_shift
#print axioms instanceProof
end PA196.Arithmetic.Transport.NumericPAeqExistentialInstanceTemplate

