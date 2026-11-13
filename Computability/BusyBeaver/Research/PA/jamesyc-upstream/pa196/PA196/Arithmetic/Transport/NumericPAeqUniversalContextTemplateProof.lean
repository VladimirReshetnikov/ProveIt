module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaQuantifierTemplatesCode
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
noncomputable def uniformMatrix (H S:SF (V:=V) 0) (D P:SF (V:=V) 1):SF (V:=V) 1 :=
  liftClosed H 🡒 (D 🡒 (P ⋎ liftClosed S))
noncomputable def uniform (H S:SF (V:=V) 0) (D P:SF (V:=V) 1):SF (V:=V) 0 :=
  ∀¹ uniformMatrix H S D P
@[simp] theorem uniform_shift (H S:SF (V:=V) 0) (D P:SF (V:=V) 1):
    (uniform H S D P).shift=uniform H.shift S.shift D.shift P.shift := by simp [uniform,uniformMatrix]
noncomputable def contextProof (H S:SF (V:=V) 0) (D P:SF (V:=V) 1):
    ND.Proof (T:=(∅:Theory L).internalize V) ∅
      (uniform H S D P 🡒 (H 🡒 ((∀¹ (D 🡒 P)) ⋎ S))) := by
  apply ND.impIntro
  apply ND.impIntro
  let Γ:ND.Seq (V:=V) := insert (∼H) (insert (∼uniform H S D P) ∅)
  apply TDerivation.or
  apply TDerivation.all
  change ND.Proof (T:=(∅:Theory L).internalize V) (insert S Γ).shift (D 🡒 P).free
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.substs_imp]
  apply ND.impIntro
  let C:ND.Seq (V:=V) := insert (∼D.free) (insert S Γ).shift
  have hH : ND.Proof (T:=(∅:Theory L).internalize V) C H.shift := ND.assumption _ (by simp [C,Γ])
  have hU : ND.Proof (T:=(∅:Theory L).internalize V) C (uniform H.shift S.shift D.shift P.shift) := by
    have hh : ND.Proof (T:=(∅:Theory L).internalize V) C (uniform H S D P).shift := ND.assumption _ (by simp [C,Γ])
    simpa using hh
  have hD : ND.Proof (T:=(∅:Theory L).internalize V) C D.free := ND.assumption _ (by simp [C])
  have hAt : ND.Proof (T:=(∅:Theory L).internalize V) C (H.shift 🡒 (D.free 🡒 (P.free ⋎ S.shift))) := by
    simpa [uniform,uniformMatrix,Bootstrapping.Semiformula.free] using ND.allElim hU (Semiterm.fvar 0)
  have hPS := ND.mp hD (ND.mp hH hAt)
  have result := TDerivation.orInv hPS
  exact result.ofEq (by ext x; simp [C,Bootstrapping.Semiformula.free]; tauto)
#print axioms uniform_shift
#print axioms contextProof
end PA196.Arithmetic.Transport.NumericPAeqUniversalContextTemplate

