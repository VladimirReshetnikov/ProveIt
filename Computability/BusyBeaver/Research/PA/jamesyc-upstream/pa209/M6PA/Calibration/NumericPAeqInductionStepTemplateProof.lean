module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqInductionStepTemplateSyntax
@[expose] public section
namespace M6.PA.NumericPAeqInductionStepTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T:InternalTheory V RelationalSource.language}
noncomputable def stepProof (F:SF (V:=V) 0) (D P R:SF (V:=V) 1) (S:SF (V:=V) 2) :
    ND.Proof (T:=T) ∅ (uniform F D P R S 🡒 ((F ⋏ sourceStep D P R) 🡒 targetStep D P S)) := by
  apply ND.impIntro
  apply ND.impIntro
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,Bootstrapping.Semiformula.substs_all]
  apply ND.allIntro
  simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_all,
    Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_and,
    Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_and,unary_shift,binary_shift,unary_subst,binary_subst]
  apply ND.impIntro
  let x:ST (V:=V) 0 := Semiterm.fvar 1
  let y:ST (V:=V) 0 := Semiterm.fvar 0
  let A := unary D.shift.shift x ⋏ (unary D.shift.shift y ⋏ (binary S.shift.shift x y ⋏ unary P.shift.shift x))
  let I := F ⋏ sourceStep D P R
  let C:ND.Seq (V:=V) := insert (∼A) ((insert (∼I) (insert (∼uniform F D P R S) ∅):ND.Seq (V:=V)).shift.shift)
  have ha:ND.Proof (T:=T) C A := ND.assumption _ (by simp [C])
  have hi:ND.Proof (T:=T) C (F.shift.shift ⋏ sourceStep D.shift.shift P.shift.shift R.shift.shift) := by
    apply ND.assumption; simp [C,I]
  have hu:ND.Proof (T:=T) C (uniform F.shift.shift D.shift.shift P.shift.shift R.shift.shift S.shift.shift) := by
    apply ND.assumption; simp [C]
  have hs:ND.Proof (T:=T) C (unary D.shift.shift x 🡒 (unary P.shift.shift x 🡒 unary R.shift.shift x)) := by
    simpa [sourceStep,unary] using ND.allElim (ND.andRight hi) x
  have hr := ND.mp (ND.andRight (ND.andRight (ND.andRight ha))) (ND.mp (ND.andLeft ha) hs)
  have hg := ND.andIntro (ND.andLeft ha) (ND.andIntro (ND.andLeft (ND.andRight ha)) (ND.andLeft (ND.andRight (ND.andRight ha))))
  have hb := ND.mp hg (ND.mp (ND.andLeft hi) (uniformAt _ _ _ _ _ x y hu))
  simpa [C,A,I,x,y,SemitermVec.q] using ND.mp hr (ND.andLeft hb)
#print axioms stepProof
end M6.PA.NumericPAeqInductionStepTemplate

