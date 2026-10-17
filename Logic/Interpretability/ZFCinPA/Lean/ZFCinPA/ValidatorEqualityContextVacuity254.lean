import ZFCinPA.ValidatorEqualityContext254
import ZFCinPA.ValidatorEnvironmentVacuity254

set_option autoImplicit false
noncomputable section

/-!
Vacuity of the represented equality context, from avoidance of every coordinate.
Only Sigma-one induction is needed: the bound stacks and generalized label stay
fixed while the prefix length varies. This does not rename accepted proofs.
-/
namespace LeanProofs.ZFCinPA.ValidatorEqualityContextVacuity254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorProvability254 ValidatorQuantifierCore254
open ValidatorEqualityContext254 ValidatorEnvironmentVacuity254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
private instance wal_sigma1 : 𝚺₁-Function₂[V] wal := wal_defined.to_definable₀
private instance vac_sigma1 : 𝚺₁-Relation[V] Vac := by
  unfold Vac
  definability

/-- Pointwise avoidance through the internal prefix length suffices, regardless
of the actual lengths of either stack, since vector lookup is total. -/
lemma prefixContext_vac (n B B' z : V) :
    (∀ i<n, z≠B.[i]) → (∀ i<n, z≠B'.[i]) → Vac z (prefixContext n B B') := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _ _
    simpa using vac_truth z
  case succ n ih =>
    intro hB hB'
    rw [prefixContext_succ]
    exact vac_neg (vac_imp (vac_eq _ _ z (hB n (by simp)) (hB' n (by simp)))
      (vac_neg (ih (fun i hi => hB i (lt_succ_iff_le.mpr (le_of_lt hi)))
        (fun i hi => hB' i (lt_succ_iff_le.mpr (le_of_lt hi))))))

/-- Equal-length stacks allow both prefix avoidance premises to be expressed
using the shared public `Avoid` predicate. -/
lemma eqContext_vac (B B' z : V) (hlen : len B=len B')
    (hB : Avoid z B) (hB' : Avoid z B') : Vac z (eqContext B B') :=
  prefixContext_vac (len B) B B' z hB (fun i hi => hB' i (by rwa [← hlen]))

/-- The two context-vacuity resources for the relational quantifier rule.
The two body-vacuity resources remain explicit for the caller. -/
lemma all_of_cons_avoiding_context (B B' p q x y : V) (hlen : len B=len B')
    (hbody : CProv (wim (eqContext (x∷B) (y∷B')) (wim p q)))
    (hxB : Avoid x B) (hxB' : Avoid x B')
    (hyB : Avoid y B) (hyB' : Avoid y B')
    (vxq : Vac x q) (vyall : Vac y (wal x p)) :
    CProv (wim (eqContext B B') (wim (wal x p) (wal y q))) :=
  all_of_cons B B' p q x y hbody
    (eqContext_vac B B' x hlen hxB hxB') vxq
    (eqContext_vac B B' y hlen hyB hyB') vyall

end LeanProofs.ZFCinPA.ValidatorEqualityContextVacuity254
