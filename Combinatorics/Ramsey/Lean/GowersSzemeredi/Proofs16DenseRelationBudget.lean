import GowersSzemeredi.Proofs16DenseRelationStep
import Mathlib.Order.Iterate

/-! A common rank/frequency budget accommodates the offsets introduced by
recentering. This recurrence is independent of the ambient modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem relationRankStep_mono_witness {theta M M' : Real} (htheta : 0 < theta)
    (hM : 0 < M) (hMM' : M ≤ M') (Q d : Nat) [NeZero Q] :
    relationRankStep theta M Q d ≤ relationRankStep theta M' Q d := by
  have hM' : 0 < M' := hM.trans_le hMM'
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  apply Nat.add_le_add_left
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_left htheta.le hM hMM') (by positivity)

def denseRelationBudget (theta : Real) (R Q k d : Nat) : Nat :=
  relationRankStep theta ((2 * R + 1)^(d + 2 * k) : Nat) Q d + k

theorem denseRelationBudget_ge (theta : Real) (R Q k d : Nat) :
    d + k ≤ denseRelationBudget theta R Q k d :=
  Nat.add_le_add_right (relationRankStep_ge _ _ _ _) _

theorem denseRelationBudget_mono {theta : Real} (htheta : 0 < theta)
    (R Q k : Nat) [NeZero Q] : Monotone (denseRelationBudget theta R Q k) := by
  intro a b hab
  apply Nat.add_le_add_right
  apply (relationRankStep_mono htheta (by positivity) Q hab).trans
  apply relationRankStep_mono_witness htheta (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2 * R + 1) (Nat.add_le_add_right hab _)

/-- One common budget bounds both the new domain rank and fixed frequencies. -/
theorem relationRankStep_le_denseRelationBudget {theta : Real} (htheta : 0 < theta)
    (R Q k d g f : Nat) [NeZero Q] (hg : g ≤ d) (hf : f ≤ d) :
    relationRankStep theta ((2 * R + 1)^(f + 2 * k) : Nat) Q g ≤
      denseRelationBudget theta R Q k d := by
  apply le_trans _ (Nat.le_add_right _ k)
  apply (relationRankStep_mono htheta (by positivity) Q hg).trans
  apply relationRankStep_mono_witness htheta (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2 * R + 1) (Nat.add_le_add_right hf _)

/-- Uniform rank bounds turn the successive density denominators into one. -/
theorem dense_relation_density_compose {alpha : Real} (ha : 0 ≤ alpha)
    (Q n d e : Nat) [NeZero Q] (he : e ≤ d) :
    alpha / (Q : Real)^((n + 1) * d) ≤
      (alpha / (Q : Real)^e) / (Q : Real)^(n * d) := by
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  rw [div_div, ← pow_add]
  apply div_le_div_of_nonneg_left ha (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) (by nlinarith : e + n * d ≤ (n + 1) * d)

/-- Row geometry can always be restricted to a smaller phase radius. -/
theorem tupleRowGeometry.mono_radius {N : Nat} [NeZero N] {κ : Type*} [Fintype κ]
    {A : Finset (ZMod N × ZMod N)} {W F : Finset (ZMod N)}
    {L : κ → ZMod N → ZMod N} {a : ZMod N} {eta eta' : Real}
    (hgeom : tupleRowGeometry A W F L a eta) (h : eta' ≤ eta) :
    tupleRowGeometry A W F L a eta' := by
  intro x hx d hd hv
  exact hgeom x hx d (bohr_mono_radius F h hd)
    (bohr_mono_radius (Finset.univ.image fun j => L j x) h hv)

end LeanProofs.GowersSzemeredi
