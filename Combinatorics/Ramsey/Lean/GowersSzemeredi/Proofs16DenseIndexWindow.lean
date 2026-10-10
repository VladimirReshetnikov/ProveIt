import GowersSzemeredi.Proofs16CoherentSandersCharts

/-! Reindex a finite active window of the actual frequency-iteration output.
Indices beyond the constructed family are padded by zero maps on the full
domain. No active value changes, and all chart domains have one uniform
positive density bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def denseWindowIndex (J : Finset Nat) (i : Fin J.card) : Nat := (J.equivFin.symm i).1

def denseWindowDomain {N : Nat} [NeZero N] (J : Finset Nat) (m : Nat)
    (D : Nat → Finset (ZMod N)) (i : Fin J.card) : Finset (ZMod N) :=
  if denseWindowIndex J i < m then D (denseWindowIndex J i) else Finset.univ

def denseWindowMap {N : Nat} (J : Finset Nat) (m : Nat)
    (theta : Nat → ZMod N → ZMod N) (i : Fin J.card) : ZMod N → ZMod N :=
  if denseWindowIndex J i < m then theta (denseWindowIndex J i) else fun _ => 0

def denseWindowActive (J S : Finset Nat) : Finset (Fin J.card) :=
  Finset.univ.filter fun i => denseWindowIndex J i ∈ S

theorem dense_window_index_mem (J : Finset Nat) (i : Fin J.card) : denseWindowIndex J i ∈ J :=
  (J.equivFin.symm i).2

theorem dense_window_index_surjective (J : Finset Nat) {j : Nat} (hj : j ∈ J) :
    ∃ i : Fin J.card, denseWindowIndex J i = j := by
  refine ⟨J.equivFin ⟨j,hj⟩,?_⟩
  simp [denseWindowIndex]

theorem dense_window_freiman {N m : Nat} [NeZero N]
    (J : Finset Nat) (D : Nat → Finset (ZMod N)) (theta : Nat → ZMod N → ZMod N)
    (hF : ∀ i < m, FreimanHom 8 (D i) (theta i)) :
    ∀ i, FreimanHom 8 (denseWindowDomain J m D i) (denseWindowMap J m theta i) := by
  intro i
  by_cases hi : denseWindowIndex J i < m
  · simpa only [denseWindowDomain,denseWindowMap,if_pos hi] using hF _ hi
  · simp only [denseWindowDomain,denseWindowMap,if_neg hi]
    exact isAddFreimanHom_const (Set.mem_univ (0 : ZMod N))

theorem dense_window_domain_density {N m : Nat} [NeZero N]
    (J : Finset Nat) (D : Nat → Finset (ZMod N)) {delta p : Real}
    (hp : 0 ≤ p) (hdelta : Real.exp (-p) ≤ delta)
    (hD : ∀ i < m, delta*(N : Real) ≤ ((D i).card : Real)) :
    ∀ i, Real.exp (-p)*(N : Real) ≤ ((denseWindowDomain J m D i).card : Real) := by
  intro i
  by_cases hi : denseWindowIndex J i < m
  · simp only [denseWindowDomain,if_pos hi]
    exact (mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg _)).trans (hD _ hi)
  · simp only [denseWindowDomain,if_neg hi,Finset.card_univ,ZMod.card]
    exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp)) (Nat.cast_nonneg _)).trans_eq (one_mul _)

/-- Reindexing and zero padding keep the active original frequency image exactly. -/
theorem dense_window_active_image {N m : Nat} (J S : Finset Nat)
    (theta : Nat → ZMod N → ZMod N) (x : ZMod N)
    (hSJ : S ⊆ J) (hSm : ∀ j ∈ S, j < m) :
    (denseWindowActive J S).image (fun i => denseWindowMap J m theta i x) =
      S.image (fun j => theta j x) := by
  ext r
  constructor
  · intro hr
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
    have hmem := (Finset.mem_filter.mp hi).2
    have hlt := hSm _ hmem
    simp only [denseWindowMap,if_pos hlt]
    exact Finset.mem_image_of_mem _ hmem
  · intro hr
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i,heq⟩ := dense_window_index_surjective J (hSJ hj)
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq.symm ▸ hj⟩,?_⟩
    simp only [denseWindowMap,heq,if_pos (hSm j hj)]

/-- The retained point is in each reindexed active chart's genuine domain. -/
theorem dense_window_active_domain_mem {N m : Nat} [NeZero N]
    (J S : Finset Nat) (D : Nat → Finset (ZMod N)) {x : ZMod N}
    (hSm : ∀ j ∈ S, j < m ∧ x ∈ D j) {i : Fin J.card} (hi : i ∈ denseWindowActive J S) :
    x ∈ denseWindowDomain J m D i := by
  have h := hSm _ (Finset.mem_filter.mp hi).2
  simpa only [denseWindowDomain,if_pos h.1] using h.2

def denseChartLog (delta : Real) : Real := max 0 (Real.log (1/delta))

theorem denseChartLog_spec {delta : Real} (hd : 0 < delta) :
    0 ≤ denseChartLog delta ∧ Real.exp (-denseChartLog delta) ≤ delta := by
  refine ⟨le_max_left _ _,?_⟩
  have he : Real.exp (-(Real.log (1/delta))) = delta := by
    rw [Real.exp_neg,Real.exp_log (by positivity)]
    field_simp
  calc Real.exp (-denseChartLog delta) ≤ Real.exp (-Real.log (1/delta)) :=
      Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
    _ = delta := he

/-- The existing potential bound supplies an N-independent family-size bound. -/
theorem dense_chart_family_size_bound {N m s : Nat} [NeZero N] {delta : Real} (hd : 0 < delta)
    (hm : ⌈delta*(N : Real)^2⌉₊ * m ≤ N*N*s) : m ≤ ⌈(s : Real)/delta⌉₊ := by
  have hN2 : (0 : Real) < (N : Real)^2 := by exact_mod_cast Nat.pow_pos (NeZero.pos N)
  have hc : delta*(N : Real)^2 ≤ (⌈delta*(N : Real)^2⌉₊ : Real) := Nat.le_ceil _
  have hmR : (⌈delta*(N : Real)^2⌉₊ : Real)*m ≤ (N : Real)^2*s := by
    simpa only [Nat.cast_mul,pow_two] using
      (Nat.cast_le.mpr hm : ((⌈delta*(N : Real)^2⌉₊ * m : Nat) : Real) ≤ ((N*N*s : Nat) : Real))
  have hmul : (delta*(m : Real))*(N : Real)^2 ≤ (s : Real)*(N : Real)^2 := by
    calc (delta*(m : Real))*(N : Real)^2 = (delta*(N : Real)^2)*m := by ring
      _ ≤ (⌈delta*(N : Real)^2⌉₊ : Real)*m := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ ≤ (N : Real)^2*s := hmR
      _ = _ := by ring
  have hdm : delta*(m : Real) ≤ s := le_of_mul_le_mul_right hmul hN2
  have hdiv : (m : Real) ≤ s/delta := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hdm)
  exact_mod_cast hdiv.trans (Nat.le_ceil _)

end LeanProofs.GowersSzemeredi
