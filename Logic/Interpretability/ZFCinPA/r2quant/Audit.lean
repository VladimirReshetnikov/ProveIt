import ZFCinPA.R2Quant

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254
open LeanProofs.ZFCinPA.ValidatorEqualityContext254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Neg
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.R2Quant.freeAvoid_even
#print axioms LeanProofs.ZFCinPA.R2Quant.freeAvoid_big
#print axioms LeanProofs.ZFCinPA.R2Quant.freeLabel_lt
#print axioms LeanProofs.ZFCinPA.R2Quant.freeLabel_odd
#print axioms LeanProofs.ZFCinPA.R2Quant.all_iff_of_eqUnder
#print axioms LeanProofs.ZFCinPA.R2Quant.iff2_trans
#print axioms LeanProofs.ZFCinPA.R2Quant.all_step
#print axioms LeanProofs.ZFCinPA.R2Quant.ex_step
#print axioms LeanProofs.ZFCinPA.R2Quant.cProv_gen_ctx
#print axioms LeanProofs.ZFCinPA.R2Quant.all_intro
#print axioms LeanProofs.ZFCinPA.R2Quant.ex_intro

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {z F : V} (hz : z % 2 = 0) (hF : OddEnv F) : FreeAvoid z F :=
  LeanProofs.ZFCinPA.R2Quant.freeAvoid_even hz hF
example {z F : V} (hz : F < z) (h1 : 1 < z) : FreeAvoid z F :=
  LeanProofs.ZFCinPA.R2Quant.freeAvoid_big hz h1
example {F j : V} : freeLabel F j < 2 * (F + 1) + 1 :=
  LeanProofs.ZFCinPA.R2Quant.freeLabel_lt
example {F j : V} (hF : OddEnv F) : freeLabel F j % 2 = 1 :=
  LeanProofs.ZFCinPA.R2Quant.freeLabel_odd hF
example {x y P Q : V} (he : EqUnder (eqContext (x ∷ 0) (y ∷ 0)) P Q)
    (vxQ : Vac x Q) (vyP : Vac y P) : Iff2 (wal x P) (wal y Q) :=
  LeanProofs.ZFCinPA.R2Quant.all_iff_of_eqUnder he vxQ vyP
example {a b c : V} (h₁ : Iff2 a b) (h₂ : Iff2 b c) : Iff2 a c :=
  LeanProofs.ZFCinPA.R2Quant.iff2_trans h₁ h₂

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

example {p F s : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0) :
    Iff2 (wal (LeanProofs.ZFCinPA.R2Quant.lx F)
      (encode F (LeanProofs.ZFCinPA.R2Quant.lx F ∷ 0) s p)) (encode F 0 s (^∀ p)) :=
  LeanProofs.ZFCinPA.R2Quant.all_step hp hF hs
example {p F s z : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0)
    (hz : z % 2 = 1) (hzx : z < LeanProofs.ZFCinPA.R2Quant.lx F) :
    CProv (wim (encode F (z ∷ 0) s p) (encode F 0 s (^∃ p))) :=
  LeanProofs.ZFCinPA.R2Quant.ex_step hp hF hs hz hzx
example {F s g : V} (hF : OddEnv F) (hs : s % 2 = 0) (L : V)
    (hL : ∀ i < len L, IsFormula ℒₛₑₜ L.[i]) :
    CProv (wim (wal (LeanProofs.ZFCinPA.R2Quant.lx F) (imps (negEnc F s L) g))
      (imps (negEnc F s L) (wal (LeanProofs.ZFCinPA.R2Quant.lx F) g))) :=
  LeanProofs.ZFCinPA.R2Quant.cProv_gen_ctx hF hs L hL
example {p F s L : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0)
    (hL : ∀ i < len L, IsFormula ℒₛₑₜ L.[i])
    (h : Der (negEnc F s L) (encode F (LeanProofs.ZFCinPA.R2Quant.lx F ∷ 0) s p)) :
    Der (negEnc F s L) (encode F 0 s (^∀ p)) :=
  LeanProofs.ZFCinPA.R2Quant.all_intro hp hF hs hL h
example {p F s z G : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0)
    (hz : z % 2 = 1) (hzx : z < LeanProofs.ZFCinPA.R2Quant.lx F)
    (h : Der G (encode F (z ∷ 0) s p)) : Der G (encode F 0 s (^∃ p)) :=
  LeanProofs.ZFCinPA.R2Quant.ex_intro hp hF hs hz hzx h

-- Both universal directions and an actual free-environment label client.
example {p F s : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (wim (wal (LeanProofs.ZFCinPA.R2Quant.lx F)
      (encode F (LeanProofs.ZFCinPA.R2Quant.lx F ∷ 0) s p)) (encode F 0 s (^∀ p))) :=
  (LeanProofs.ZFCinPA.R2Quant.all_step hp hF hs).1
example {p F s : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (wim (encode F 0 s (^∀ p)) (wal (LeanProofs.ZFCinPA.R2Quant.lx F)
      (encode F (LeanProofs.ZFCinPA.R2Quant.lx F ∷ 0) s p))) :=
  (LeanProofs.ZFCinPA.R2Quant.all_step hp hF hs).2
example {p F s j : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (wim (encode F (freeLabel F j ∷ 0) s p) (encode F 0 s (^∃ p))) :=
  LeanProofs.ZFCinPA.R2Quant.ex_step hp hF hs
    (LeanProofs.ZFCinPA.R2Quant.freeLabel_odd hF) LeanProofs.ZFCinPA.R2Quant.freeLabel_lt
