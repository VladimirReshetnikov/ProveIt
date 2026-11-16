module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateBinaryRewriting
@[expose] public section
namespace M6.PA.RelationalPredicateBinary
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : InternalTheory V L}

noncomputable def pack {Γ : ND.Seq (V:=V)} (D : SF (V:=V) 1) (R : SF (V:=V) 3)
    (P Q : SF (V:=V) 1) (x y z : ST (V:=V) 0)
    (hd : ND.Proof (T:=T) Γ (unary D z)) (hp : ND.Proof (T:=T) Γ (unary P x))
    (hq : ND.Proof (T:=T) Γ (unary Q y)) (hr : ND.Proof (T:=T) Γ (ternary R x y z)) :
    ND.Proof (T:=T) Γ (result D R P Q) := by
  have inner : ND.Proof (T:=T) Γ
      (∃¹ ∃¹ (unary P (Semiterm.bvar 1) ⋏
        (unary Q (Semiterm.bvar 0) ⋏ ternary R (Semiterm.bvar 1) (Semiterm.bvar 0) z.bShift.bShift))) := by
    apply ND.exsIntro _ x
    have last : ND.Proof (T:=T) Γ
        (∃¹ (unary P x.bShift ⋏ (unary Q (Semiterm.bvar 0) ⋏ ternary R x.bShift (Semiterm.bvar 0) z.bShift))) := by
      apply ND.exsIntro _ y
      simpa using ND.andIntro hp (ND.andIntro hq hr)
    simp only [Bootstrapping.Semiformula.substs_ex,Bootstrapping.Semiformula.substs_and,
      unary_subst,ternary_subst,Bootstrapping.Semiterm.bShift_substs_q,
      Bootstrapping.Semiterm.bShift_substs_sing,Bootstrapping.Semiterm.substs_bvar]
    simpa [SemitermVec.q] using last
  apply ND.exsIntro _ z
  simp only [result,Bootstrapping.Semiformula.substs_ex,Bootstrapping.Semiformula.substs_and,
    unary_subst,ternary_subst,Bootstrapping.Semiterm.bShift_substs_q,
    Bootstrapping.Semiterm.bShift_substs_sing,Bootstrapping.Semiterm.substs_bvar]
  simpa [SemitermVec.q] using ND.andIntro hd inner

#print axioms pack
end M6.PA.RelationalPredicateBinary

