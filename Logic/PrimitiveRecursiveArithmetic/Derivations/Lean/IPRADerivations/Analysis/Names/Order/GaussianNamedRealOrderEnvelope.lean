import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport

/-!
# Exact named real order from a uniform one-sided sample bound

A one-sided error of K/2^p at common precision suffices for exact
independent-clock order. One explicit query removes the auxiliary
slack after the two regularity comparisons.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRealOrderEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianNameEquivalence (point_at)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def envelope (f g : PR 2) (x y K : PTm n) : Fm PTm n := .all
  (upper (fstT (ap2 f (var 0) (Syn.shift x))) (fstT (ap2 g (var 0) (Syn.shift y)))
    (Syn.shift K) (unit (var 0)))

@[simp] theorem subst_envelope {l : ℕ} (σ : Fin n → PTm l) (f g : PR 2) (x y K : PTm n) :
    (envelope f g x y K).subst σ = envelope f g (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ K) := by
  simp [envelope,Syn.subst_shift,Syn.shift_subst]

theorem envelope_at (f g : PR 2) (x y K p : PTm n) (h : Γ ⊢[PRAAx] envelope f g x y K) :
    Γ ⊢[PRAAx] upper (fstT (ap2 f p x)) (fstT (ap2 g p y)) K (unit p) := by
  simpa only [envelope,RationalValueBounds.subst_upper,subst_fstT,subst_ap2,
    GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem independent_slack (f g : PR 2) (x y K p q s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (h : Γ ⊢[PRAAx] envelope f g x y K) :
    Γ ⊢[PRAAx] upperSlack (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p+unit q) (unit p*unit q) (K+two) s := by
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hS := unit_positive (Γ := Γ) s
  have hPS := positive_product _ _ hP hS
  have hSQ := positive_product _ _ hS hQ
  have left := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hPS (point_at f x p s hf))
  have right := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hSQ (point_at g y s q hg))
  have center := envelope_at f g x y K s h
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left center) right
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hPS hS) hSQ) joined
  exact le_of_eq_add (d := zero) (by ipra_ring)

theorem order_from_envelope (f g : PR 2) (x y K : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (h : Γ ⊢[PRAAx] envelope f g x y K) :
    Γ ⊢[PRAAx] realOrder f g x y := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let a := fstT (ap2 f p (sh x))
  let b := fstT (ap2 g q (sh y))
  let s := precision a b (unit p*unit q) (sh K+two)
  have u : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hf.shift.shift
  have v : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hg.shift.shift
  have c : Δ ⊢[PRAAx] envelope f g (sh x) (sh y) (sh K) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  exact remove_upper_slack a b (unit p+unit q) (unit p*unit q) (sh K+two)
    (independent_slack f g (sh x) (sh y) (sh K) p q s u v c)

theorem actual_real_order_from_uniform_envelope_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((pointCN f (var 0) ⋏ pointCN g (var 1)) ⟶ envelope f g (var 0) (var 1) (var 2) ⟶ realOrder f g (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (order_from_envelope f g _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedRealOrderEnvelope
