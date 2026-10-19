import ZFCinPA.R2Ax

noncomputable section

namespace LeanProofs.ZFCinPA.R2AxFreshAudit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Gic
open scoped LO.FirstOrder.Arithmetic
set_option autoImplicit false

variable {V : Type} [ORingStructure V]
  [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

#print axioms LeanProofs.ZFCinPA.R2Ax.gic_body
#print axioms LeanProofs.ZFCinPA.R2Ax.closure
#print axioms LeanProofs.ZFCinPA.R2Ax.gic_axiom

example (s m b F i : V) : V :=
  LeanProofs.ZFCinPA.R2Ax.pc s m b F i

example (K : SF (V := V) 2) {F s : V} (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (encode F 0 s (gicBody K).val) :=
  LeanProofs.ZFCinPA.R2Ax.gic_body K hF hs

example {m b s : V} (hb : IsSemiformula ℒₛₑₜ m b)
    (hbs : shift ℒₛₑₜ b = b) (hs : s % 2 = 0)
    (base : ∀ F : V, OddEnv F → CProv (encode F 0 s (subst ℒₛₑₜ (fvarVec m) b)))
    (F : V) (hF : OddEnv F) :
    CProv (encode F 0 s (qqAlls b m)) :=
  LeanProofs.ZFCinPA.R2Ax.closure hb hbs hs base F hF

example {p F s : V} (hp : GicR p) (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (encode F 0 s p) :=
  LeanProofs.ZFCinPA.R2Ax.gic_axiom hp hF hs

end LeanProofs.ZFCinPA.R2AxFreshAudit
