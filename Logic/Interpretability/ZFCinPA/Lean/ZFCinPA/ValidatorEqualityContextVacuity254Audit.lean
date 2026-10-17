import ZFCinPA.ValidatorEqualityContextVacuity254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEqualityContext254
open LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open LeanProofs.ZFCinPA.ValidatorEqualityContextVacuity254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContextVacuity254.prefixContext_vac
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContextVacuity254.eqContext_vac
#print axioms LeanProofs.ZFCinPA.ValidatorEqualityContextVacuity254.all_of_cons_avoiding_context

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (n B B' z : V) (hB : ∀ i<n, z≠B.[i]) (hB' : ∀ i<n, z≠B'.[i]) :
    Vac z (prefixContext n B B') := prefixContext_vac n B B' z hB hB'
example (B B' z : V) : Vac z (prefixContext 0 B B') :=
  prefixContext_vac 0 B B' z (by simp) (by simp)
example (B B' z : V) (hlen : len B=len B')
    (hB : Avoid z B) (hB' : Avoid z B') : Vac z (eqContext B B') :=
  eqContext_vac B B' z hlen hB hB'
example (B B' z : V) (hlen : len B=len B')
    (hB : Avoid z B) (hB' : Avoid z B') :
    CProv (wim (eqContext B B') (wal z (eqContext B B'))) :=
  eqContext_vac B B' z hlen hB hB'
example (z : V) : Vac z (eqContext (0 : V) 0) :=
  eqContext_vac 0 0 z rfl (avoid_nil z) (avoid_nil z)
example (B B' z x y : V) (hlen : len B=len B')
    (hB : Avoid z B) (hB' : Avoid z B') (hx : z≠x) (hy : z≠y) :
    Vac z (eqContext (x∷B) (y∷B')) :=
  eqContext_vac (x∷B) (y∷B') z (by simp [hlen]) (avoid_cons hB hx) (avoid_cons hB' hy)
example (B B' p q x y : V) (hlen : len B=len B')
    (hbody : CProv (wim (eqContext (x∷B) (y∷B')) (wim p q)))
    (hxB : Avoid x B) (hxB' : Avoid x B')
    (hyB : Avoid y B) (hyB' : Avoid y B')
    (vxq : Vac x q) (vyall : Vac y (wal x p)) :
    CProv (wim (eqContext B B') (wim (wal x p) (wal y q))) :=
  all_of_cons_avoiding_context B B' p q x y hlen hbody hxB hxB' hyB hyB' vxq vyall
