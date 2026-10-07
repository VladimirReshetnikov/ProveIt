import OAI.Combinatorics.Progressions.Estimates.AllocatedTestUniformCoarseJointComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem character_root_power_cancel_le {a C : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {n k : ℕ} (hn : 0 < n) (hk : n * (n + 2) ≤ k) :
    a ^ n * (C / a ^ (1 / (n : ℝ))) ^ k ≤ C ^ k / a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hr0 : 0 < a ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos ha0 _
  have hr1 : 1 ≤ a ^ (1 / (n : ℝ)) :=
    Real.one_le_rpow ha (by positivity)
  have hi1 : 1 / a ^ (1 / (n : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hr0).mpr
    simpa using hr1
  have hpow := pow_le_pow_of_le_one (le_of_lt (one_div_pos.mpr hr0)) hi1 hk
  calc
    _ = C ^ k * (a ^ n * (1 / a ^ (1 / (n : ℝ))) ^ k) := by
      rw [div_eq_mul_one_div, mul_pow]
      ring
    _ ≤ C ^ k * (a ^ n * (1 / a ^ (1 / (n : ℝ))) ^ (n * (n + 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (pow_nonneg ha0.le _))
        (pow_nonneg hC _)
    _ = C ^ k / a ^ 2 := by
      rw [character_root_power_cancel a 1 ha0 n hn]
      simp only [one_pow]
      ring

theorem finite_character_reciprocal_tail_of_le (B R n k : ℕ)
    (hB : 0 < B) (hn : 0 < n) (hk : n * (n + 2) ≤ k)
    (C : ℝ) (hC : 0 ≤ C) :
    (∑ a : Fin R, if B < a.val + 1 then
      ((a.val + 1 : ℕ) : ℝ) ^ n *
        (C / ((a.val + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ^ k else 0) ≤
      C ^ k / (B : ℝ) := by
  calc
    _ ≤ C ^ k * ∑ a : Fin R,
        if B < a.val + 1 then 1 / ((a.val + 1 : ℕ) : ℝ) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      split_ifs with h
      · simpa only [one_div, div_eq_mul_inv, one_mul] using
          character_root_power_cancel_le (a := ((a.val + 1 : ℕ) : ℝ))
            (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le a.val)) hC hn hk
      · simp
    _ ≤ C ^ k / (B : ℝ) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (finite_positiveOrder_reciprocal_tail B R hB)
        (pow_nonneg hC _)

theorem largeCokernel_reciprocal_probability_le_of_card_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (B R : ℕ) (hB : 0 < B) (C : ℝ) (hC : 0 ≤ C)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J)
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤
        C / (a : ℝ) ^ (1 / (Fintype.card I : ℝ))) :
    (FiniteProbabilityWeights.pi p).eventProbability (largeCokernelEvent column B R) ≤
      C ^ Fintype.card J / (B : ℝ) := by
  have h := largeCokernel_probability_le p column B R
    (fun a => C / (a : ℝ) ^ (1 / (Fintype.card I : ℝ)))
    (fun a => div_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg a) _)) hsingle
  exact h.trans (finite_character_reciprocal_tail_of_le B R (Fintype.card I) (Fintype.card J)
    hB Fintype.card_pos hJ C hC)

theorem boxCokernel_probability_le_of_card_le {I J K : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]
    (e : I → K) (he : Function.Injective e) (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (p : ∀ j, FiniteProbabilityWeights (K → Finset.Ico (lo j) (hi j)))
    (B R : ℕ) (hB : 0 < B) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J)
    (hw : ∀ j x, (p j).weight x ≤
      C * (Fintype.card (K → Finset.Ico (lo j) (hi j)) : ℝ)⁻¹)
    (hscale : ∀ j, (R : ℝ) ^ (1 / (Fintype.card I : ℝ)) ≤
      D * ((hi j - lo j : ℤ) : ℝ)) :
    (FiniteProbabilityWeights.pi p).eventProbability
        (largeCokernelEvent (fun _j x i => (x (e i) : ℤ)) B R) ≤
      (C * (1 + D)) ^ Fintype.card J / (B : ℝ) := by
  apply largeCokernel_reciprocal_probability_le_of_card_le p _ B R hB (C * (1 + D))
    (mul_nonneg hC (by positivity)) hJ
  intro a haB haR χ hχ j
  have ha : 0 < a := by omega
  have hχpos : 0 < orderOf χ := by omega
  have h := integerBox_character_probability_le e he (lo j) (hi j) (hlen j)
    (p j) C hC (hw j) χ hχpos
  rw [hχ] at h
  apply h.trans
  apply reciprocal_interval_error_absorb _ _ C D
    (Real.rpow_pos_of_pos (by exact_mod_cast ha) _) (by exact_mod_cast sub_pos.mpr (hlen j)) hC
  exact (Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast haR) (by positivity)).trans
    (hscale j)

theorem scalarCube_largeCokernel_probability_le_of_card_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (L B : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L) (hB : 0 < B)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (scalarCubeLargeCokernelEvent B) ≤
      (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^
        Fintype.card J / (B : ℝ) := by
  let R := (Fintype.card I).factorial * L ^ Fintype.card I
  have hbound := boxCokernel_probability_le_of_card_le
    (I := I) (J := J) (K := Option I) Option.some (Option.some_injective I)
    (fun _ => -(L : ℤ)) (fun _ => (L : ℤ)) (fun _ => by omega)
    (fun _ => integerScalarCubeWeights I L hL) B R hB
    (integerScalarCubeDensityCap I) ((Fintype.card I).factorial : ℝ)
    (integerScalarCubeDensityCap_pos I).le (Nat.cast_nonneg _) hJ
    (fun _ x => integerScalarCubeWeights_weight_le I L hL hsize x) (fun _ => ?_)
  · apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans hbound
    intro x hx
    apply nonzeroMinor_largeCokernelEvent _ x B L _ hx.1 hx.2
    intro i j
    have h := Finset.mem_Ico.mp (x j (some i)).property
    have ha : |(x j (some i) : ℤ)| ≤ (L : ℤ) := abs_le.mpr ⟨h.1, h.2.le⟩
    have hn : (((x j (some i) : ℤ).natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by
      simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast hn
  · have h := nat_monomial_root_le (Fintype.card I) (Fintype.card I).factorial L
      Fintype.card_pos (Nat.factorial_pos _)
    apply h.trans
    push_cast
    nlinarith [show (0 : ℝ) ≤ (Fintype.card I).factorial from Nat.cast_nonneg _]

theorem scalarKernel_explicit_probability_le_of_card_le (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J) (s : I ↪ J)
    {M D L : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hL : 0 < L)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
        (scalarKernelCutoff I J M D η) x) ≤ scalarKernelAdjustedAccuracy I J M D η := by
  let B := scalarKernelCutoff I J M D η
  let κ := scalarKernelThreshold I J M D η
  let ε := scalarKernelAdjustedAccuracy I J M D η
  obtain ⟨hB, hsize, _, hinv, hmesh, htail⟩ := scalarKernelCutoff_bounds I J hM hD hη
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hκ : 0 < κ := scalarKernelThreshold_pos I J hM hD hη
  have hε : 0 < ε := scalarKernelAdjustedAccuracy_pos I J hM hD hη
  have hsizeL : Fintype.card I + 1 ≤ L := hsize.trans hlarge
  have hsmall : 1 / (B : ℝ) ≤ κ := by
    apply (div_le_iff₀ hB').mpr
    have h := (div_le_iff₀ hκ).mp hinv
    nlinarith
  have hmeshL : coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) / L ≤ κ := by
    apply (div_le_iff₀ hL').mpr
    have hBL : (scalarKernelCutoff I J M D η : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlarge
    have h := (div_le_iff₀ hκ).mp (hmesh.trans hBL)
    nlinarith
  have htailB : scalarKernelTailConstant I J / B ≤ ε / 2 := by
    apply (div_le_iff₀ hB').mpr
    have h := (div_le_iff₀ hε).mp htail
    nlinarith
  have hJpos : 0 < Fintype.card J := by
    exact lt_of_lt_of_le (Nat.mul_pos Fintype.card_pos (by omega)) hJ
  have hN : 0 < Fintype.card (J × Option I) := by
    rw [Fintype.card_prod, Fintype.card_option]
    exact Nat.mul_pos hJpos (by omega)
  have hreal := discrete_minor_threshold_probability (Fintype.equivFin (J × Option I)) hN
    s s.injective L hL hsizeL ε hε hmeshL
  have hminor : (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => |normalizedScalarCubeMinor s x| ≤ 1 / (B : ℝ)) ≤ ε / 2 := by
    apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans hreal
    intro x hx
    exact hx.trans hsmall
  have hcoker := scalarCube_largeCokernel_probability_le_of_card_le (I := I) (J := J) L B hL hsizeL hB hJ
  apply (scalarKernel_bad_event_le _ s (1 / (B : ℝ)) B (one_div_pos.mpr hB')).trans
  exact (add_le_add hminor (hcoker.trans htailB)).trans_eq (by ring)

theorem affineKernel_explicit_probability_le_of_card_le (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J) (s : I ↪ J)
    {M D L : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hL : 0 < L)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) (K : J → ℕ)
    (hKL : ∀ j, K j ≤ L) (hDK : ∀ j, L ≤ D * K j) (c : J → ℤ)
    (m : J → Option I → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M) :
    (FiniteProbabilityWeights.pi (fun j =>
      affineScalarCubeWindowWeights I L (K j) M D (c j) hL (hKL j) (hDK j)
        (m j) (r j) (hm j) (hmM j) (scalarKernelCutoff_window_size I J hM hD hη hlarge (hDK j)))).eventProbability
      (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
        (scalarKernelCutoff I J M D η) x) ≤ η := by
  let C := scalarKernelConditioningConstant I J M D
  have hC : 0 < C := scalarKernelConditioningConstant_pos I J hM hD
  have h := scalarCubeWindow_pi_eventProbability_le I J L M D K hL hKL hDK m
    (fun j => shiftScalarCubeResidues (c j) (m j) (r j)) hm hmM
    (fun j => scalarKernelCutoff_window_size I J hM hD hη hlarge (hDK j))
    (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
      (scalarKernelCutoff I J M D η) x)
  apply h.trans
  calc
    _ ≤ C * scalarKernelAdjustedAccuracy I J M D η := mul_le_mul_of_nonneg_left
      (scalarKernel_explicit_probability_le_of_card_le I J hJ s hM hD hη hL hlarge) hC.le
    _ = η := by
      change C * (η / C) = η
      field_simp

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedTupleEnvelope_ge_input (m : ℕ) {D p e : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) :
    p ≤ allocatedTupleEnvelope m D p e := by
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  let R := (D + 1) ^ 2 + 4 * D + 3
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrest : 0 ≤ R + D + D +
      (D * ((m * 2 ^ (m + 1) : ℕ) * p + allocatedDensityEnvelope m D p) +
        R + D + allocatedDensityEnvelope m D p + 1) + (e + 2) + 1 := by positivity
  have hmp : p ≤ ((m : ℝ) + 1) * p := by
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hp]
  dsimp only [allocatedTupleEnvelope]
  dsimp only [R] at hrest
  linarith

theorem allocatedPhysicalIdealLengthEnvelope_ge_input (m : ℕ) {D p e w E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    p ≤ allocatedPhysicalIdealLengthEnvelope m D p e w E := by
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  have hi := kernelInverseEnvelope_nonneg hD hp
  have ht := allocatedTestEnvelope_nonneg m hD hp (show 0 ≤ E + 3 by positivity)
  have hf : 0 ≤ allocatedFrontEnvelope m D p
      (allocatedAccuracyEnvelope m D p (allocatedTestEnvelope m D p (E + 3))) := by
    dsimp only [allocatedFrontEnvelope, allocatedKernelEnvelope, allocatedAccuracyEnvelope]
    positivity
  have hmf : 0 ≤ (m : ℝ) * allocatedFrontEnvelope m D p
      (allocatedAccuracyEnvelope m D p (allocatedTestEnvelope m D p (E + 3))) :=
    mul_nonneg (Nat.cast_nonneg _) hf
  have htuple := allocatedTupleEnvelope_ge_input m hD hp ht
  have hg := allocatedIdealGridEnvelope_nonneg m hD hp he
  have hmesh : 0 ≤ E + D * w + allocatedIdealMeshEnvelope m D p e + 3 := by
    unfold allocatedIdealMeshEnvelope
    positivity
  dsimp only [allocatedPhysicalIdealLengthEnvelope, allocatedTestLengthEnvelope, allocatedJointLengthEnvelope]
  linarith

theorem scalarKernelCutoff_le_allocatedPrimitive
    (α G : Type*) [Fintype α] [Nonempty α] [Fintype G]
    {q E T : ℝ} (hq : 0 ≤ q) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hα : (Fintype.card α : ℝ) ≤ q) (hG : (Fintype.card G : ℝ) ≤ q)
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDq : (D : ℝ) ≤ Real.exp q) :
    (scalarKernelCutoff α G M D (Real.exp (-(E + 1))) : ℝ) ≤
      Real.exp (allocatedKernelPrimitiveBudget q E T) := by
  have hinput : 0 ≤ q + E + T + 1 := by positivity
  have hMi := hMT.trans (Real.exp_le_exp.mpr (show T ≤ q + E + T + 1 by linarith))
  have hDi := hDq.trans (Real.exp_le_exp.mpr (show q ≤ q + E + T + 1 by linarith))
  have hη : (Real.exp (-(E + 1)))⁻¹ ≤ Real.exp (q + E + T + 1) := by
    rw [Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  exact (scalarKernelCutoff_le_exp α G hM hD (Real.exp_pos _) hinput hMi hDi hη).trans
    (Real.exp_le_exp.mpr (scalarKernelLogarithmicBudget_le_allocatedPrimitive α G hq hE hT hα hG))

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedIdealScale_ge_exp {D p e w E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    Real.exp p ≤ ((allocatedIdealScale (G := G) B U basis hR hσ D p e w E).value : ℝ) :=
  (Real.exp_le_exp.mpr (allocatedPhysicalIdealLengthEnvelope_ge_input m hD hp he hw hE)).trans
    (allocatedIdealScale_lower B U basis hR hσ D p e w E)

theorem allocatedIdealScale_kernel_cutoff {dim : ℕ} [Nonempty (Fin dim)]
    {q Ebad T D p e w E : ℝ}
    (hq : 0 ≤ q) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T)
    (hD : 0 ≤ D) (he : 0 ≤ e) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hdim : (dim : ℝ) ≤ q) (hG : (Fintype.card G : ℝ) ≤ q)
    (hbudget : allocatedKernelPrimitiveBudget q Ebad T ≤ p)
    {M Dwin : ℕ} (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDq : (Dwin : ℝ) ≤ Real.exp q) :
    let cutoff := scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(Ebad + 1)))
    0 < cutoff ∧ (cutoff : ℝ) ≤ Real.exp (allocatedKernelPrimitiveBudget q Ebad T) ∧
      cutoff ≤ (allocatedIdealScale (G := G) B U basis hR hσ D p e w E).value := by
  have hp := (allocatedKernelPrimitiveBudget_bounds hq hEbad hT).1.trans hbudget
  have hcut := scalarKernelCutoff_le_allocatedPrimitive (Fin dim) G hq hEbad hT
    (by simpa only [Fintype.card_fin] using hdim) hG hM hDwin hMT hDq
  refine ⟨(scalarKernelCutoff_bounds (Fin dim) G hM hDwin (Real.exp_pos _)).1, hcut, ?_⟩
  exact_mod_cast hcut.trans ((Real.exp_le_exp.mpr hbudget).trans
    (allocatedIdealScale_ge_exp B U basis hR hσ hD hp he hw hE))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedReferenceScale_affine_kernel_control
    {dim : ℕ} [Nonempty (Fin dim)] {q E T D p e : ℝ}
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hT : 0 ≤ T) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hdim : (dim : ℝ) ≤ q) (hGp : (Fintype.card G : ℝ) ≤ q)
    (hG : dim * (dim + 2) ≤ Fintype.card G) (selection : Fin dim ↪ G)
    (hbudget : allocatedKernelPrimitiveBudget q E T ≤ p)
    {M Dwin : ℕ} (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDq : (Dwin : ℝ) ≤ Real.exp q) :
    let Psp := allocatedKernelPrimitiveBudget q E T
    let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
    let error := allocatedReferenceIdealError m D Psp (E + 1)
    let S := allocatedIdealScale (G := G) B U basis hR hσ D p e w error
    let η := Real.exp (-(E + 1))
    let cutoff := scalarKernelCutoff (Fin dim) G M Dwin η
    let Good := fun x : G → IntegerScalarCubeBox (Fin dim) S.value =>
      GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff x
    0 < cutoff ∧ (cutoff : ℝ) ≤ Real.exp Psp ∧
    ∃ hlarge : cutoff ≤ S.value,
    ∀ (K : G → ℕ) (hKL : ∀ g, K g ≤ S.value) (hDK : ∀ g, S.value ≤ Dwin * K g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    let law := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (K g) M Dwin (shift g)
        S.positive (hKL g) (hDK g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hDwin (Real.exp_pos _) hlarge (hDK g)))
    law.eventProbability (fun x => ¬Good x) ≤ η ∧
      (∃ x, law.weight x ≠ 0 ∧ Good x) ∧
      ∀ (f : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℂ) (g : ∀ x, Good x → ℂ),
        (∀ x, ‖f x‖ ≤ 1) → (∀ x (hx : Good x), ‖f x - g x hx‖ ≤ η) →
        ‖law.complexMean f - law.complexMean (fun x => if hx : Good x then g x hx else 0)‖ ≤
          Real.exp (-E) := by
  intro Psp w error S η cutoff Good
  have hPsp : 0 ≤ Psp := (allocatedKernelPrimitiveBudget_bounds hq hE hT).1
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hD hPsp (by linarith)
  obtain ⟨hcutoff, hcutoffP, hlarge⟩ := allocatedIdealScale_kernel_cutoff B U basis hR hσ
    hq hE hT hD he hw herror hdim hGp hbudget hM hDwin hMT hDq
  refine ⟨hcutoff, hcutoffP, hlarge, ?_⟩
  intro K hKL hDK shift moduli residues hmoduli hmoduliM law
  have hbad : law.eventProbability (fun x => ¬Good x) ≤ η :=
    affineKernel_explicit_probability_le_of_card_le (Fin dim) G
      (by simpa only [Fintype.card_fin] using hG) selection hM hDwin (Real.exp_pos _) S.positive
      hlarge K hKL hDK shift moduli residues hmoduli hmoduliM
  have hη : η < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine ⟨hbad, law.exists_supported_good_of_bad_lt_one Good (hbad.trans_lt hη), ?_⟩
  intro f g hf hgood
  exact law.complexMean_goodPart_exp_error Good f g hbad hf hgood

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedNormalizedInitialLog_ge_input (m : ℕ) {p Pc E T : ℝ}
    (hp : 0 ≤ p) (hPc : 0 ≤ Pc) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    p ≤ allocatedNormalizedInitialLog m p Pc E (T + 1) := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have he := allocatedCoefficientAccuracyLog_nonneg m hp (show 0 ≤ E + 3 by positivity)
  have hJ := allocatedJointLengthEnvelope_nonneg m hD hPc he
  dsimp only [allocatedCoefficientAccuracyLog] at hJ
  have hprod := mul_nonneg hp hT
  dsimp only [allocatedNormalizedInitialLog]
  nlinarith

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedPrimitiveNormalizedScale_ge_exp {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    Real.exp p ≤ ((allocatedPrimitiveNormalizedScale (G := G) B U b hR hσ p E (T + 1)).value : ℝ) :=
  (Real.exp_le_exp.mpr (allocatedNormalizedInitialLog_ge_input m hp
    (allocatedComparisonDimension_bounds m hp).1 hE hT)).trans
      (allocatedNormalizedScale_lower B U b hR hσ p (allocatedComparisonDimension m p) E (T + 1))

noncomputable def allocatedKernelScale (p E T : ℝ) : LayerSamplerScale (G := G) B U b R σ :=
  allocatedPrimitiveNormalizedScale B U b hR hσ (allocatedKernelPrimitiveBudget p E T) (E + 1) (T + 1)

theorem allocatedKernelScale_cutoff {dim : ℕ} [Nonempty (Fin dim)] {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hdim : (dim : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p) :
    (scalarKernelCutoff (Fin dim) G M D (Real.exp (-(E + 1))) : ℝ) ≤
        Real.exp (allocatedKernelPrimitiveBudget p E T) ∧
      scalarKernelCutoff (Fin dim) G M D (Real.exp (-(E + 1))) ≤
        (allocatedKernelScale (G := G) B U b hR hσ p E T).value := by
  have hinput : 0 ≤ p + E + T + 1 := by positivity
  have hMinput := hMT.trans (Real.exp_le_exp.mpr (show T ≤ p + E + T + 1 by linarith))
  have hDinput := hDp.trans (Real.exp_le_exp.mpr (show p ≤ p + E + T + 1 by linarith))
  have hηinput : (Real.exp (-(E + 1)))⁻¹ ≤ Real.exp (p + E + T + 1) := by
    rw [Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlog := scalarKernelLogarithmicBudget_le_allocatedPrimitive (Fin dim) G hp hE hT
    (by simpa only [Fintype.card_fin] using hdim) hG
  have hcut := (scalarKernelCutoff_le_exp (Fin dim) G hM hD (Real.exp_pos _) hinput
    hMinput hDinput hηinput).trans (Real.exp_le_exp.mpr hlog)
  refine ⟨hcut, ?_⟩
  exact_mod_cast hcut.trans (allocatedPrimitiveNormalizedScale_ge_exp B U b hR hσ
    (allocatedKernelPrimitiveBudget_bounds hp hE hT).1 (show 0 ≤ E + 1 by positivity) hT)

theorem allocatedKernelScale_affine_bad_probability [DecidableEq G]
    {dim : ℕ} [Nonempty (Fin dim)] {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hdim : (dim : ℝ) ≤ p) (hGp : (Fintype.card G : ℝ) ≤ p)
    (hG : dim * (dim + 2) ≤ Fintype.card G) (selection : Fin dim ↪ G)
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p) :
    let S := allocatedKernelScale (G := G) B U b hR hσ p E T
    let η := Real.exp (-(E + 1))
    let cutoff := scalarKernelCutoff (Fin dim) G M D η
    let hlarge := (allocatedKernelScale_cutoff B U b hR hσ hp hE hT hdim hGp hM hD hMT hDp).2
    ∀ (K : G → ℕ) (hKL : ∀ g, K g ≤ S.value) (hDK : ∀ g, S.value ≤ D * K g)
      (c : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    (FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (K g) M D (c g) S.positive (hKL g) (hDK g)
        (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hD (Real.exp_pos _) hlarge (hDK g)))).eventProbability
      (fun x => ¬ GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff x) ≤ η := by
  intro S η cutoff hlarge K hKL hDK c moduli residues hmoduli hmoduliM
  exact affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hG) selection hM hD (Real.exp_pos _) S.positive
    hlarge K hKL hDK c moduli residues hmoduli hmoduliM

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedCoarseKernelScale (p E T : ℝ) : LayerSamplerScale (G := G) B U b R σ :=
  allocatedPrimitiveNormalizedScale B U b hR hσ (allocatedKernelPrimitiveBudget p E T) (E+2) (T+1)

theorem allocatedCoarseKernelScale_cutoff {dim : ℕ} [Nonempty (Fin dim)] {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hdim : (dim : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p) :
    (scalarKernelCutoff (Fin dim) G M D (Real.exp (-(E+1))) : ℝ) ≤
        Real.exp (allocatedKernelPrimitiveBudget p E T) ∧
      scalarKernelCutoff (Fin dim) G M D (Real.exp (-(E+1))) ≤
        (allocatedCoarseKernelScale (G := G) B U b hR hσ p E T).value := by
  have hcut := (allocatedKernelScale_cutoff B U b hR hσ hp hE hT hdim hG hM hD hMT hDp).1
  refine ⟨hcut, ?_⟩
  exact_mod_cast hcut.trans (allocatedPrimitiveNormalizedScale_ge_exp B U b hR hσ
    (allocatedKernelPrimitiveBudget_bounds hp hE hT).1 (show 0 ≤ E+2 by positivity) hT)

theorem allocatedCoarseKernelScale_affine_bad_probability [DecidableEq G]
    {dim : ℕ} [Nonempty (Fin dim)] {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hdim : (dim : ℝ) ≤ p) (hGp : (Fintype.card G : ℝ) ≤ p)
    (hG : dim * (dim + 2) ≤ Fintype.card G) (selection : Fin dim ↪ G)
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p) :
    let S := allocatedCoarseKernelScale (G := G) B U b hR hσ p E T
    let η := Real.exp (-(E+1))
    let cutoff := scalarKernelCutoff (Fin dim) G M D η
    let hlarge := (allocatedCoarseKernelScale_cutoff B U b hR hσ hp hE hT hdim hGp hM hD hMT hDp).2
    ∀ (K : G → ℕ) (hKL : ∀ g, K g ≤ S.value) (hDK : ∀ g, S.value ≤ D*K g)
      (c : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    (FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (K g) M D (c g) S.positive (hKL g) (hDK g)
        (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hD (Real.exp_pos _) hlarge (hDK g)))).eventProbability
      (fun x => ¬GoodScalarKernelTuple selection (1/(cutoff : ℝ)) cutoff x) ≤ η := by
  intro S η cutoff hlarge K hKL hDK c moduli residues hmoduli hmoduliM
  exact affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hG) selection hM hD (Real.exp_pos _) S.positive
    hlarge K hKL hDK c moduli residues hmoduli hmoduliM

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "Z" => selectedJointDensityMass bases stride cells widths baseDensity
local notation "Kernel" => (G → IntegerScalarCubeBox (Fin dim) S.value)

variable (μ : FiniteProbabilityWeights (G → IntegerScalarCubeBox (Fin dim) S.value))
variable (selection : Fin dim ↪ G) (M : ℕ)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "Good" => GoodScalarKernelTuple (L := S.value) selection (1 / (M : ℝ)) M
local notation "source" => (fun (x : Kernel) (base : X → ℤ) =>
  allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ base cells hmass test Z poly hmem)

include hbases htotal htest

theorem allocatedOriginal_kernel_average :
    let f : Kernel → (X → ℤ) → ℂ := source
    ∀ (reference : ∀ x : Kernel, Good x → (X → ℤ) → ℂ)
      {ε : ℝ}, 0 ≤ ε →
      (∀ x (hx : Good x) base, base ∈ bases → ‖f x base - reference x hx base‖ ≤ ε) →
    ‖μ.complexMean (fun x => 𝔼 base ∈ bases, f x base) -
      μ.goodPartBaseMean bases Good reference‖ ≤
      ε + μ.eventProbability (fun x => ¬Good x) := by
  intro f reference ε hε hcomparison
  apply μ.complexMean_goodPart_base_comparison bases hbases Good f reference hε _ hcomparison
  intro x
  exact allocatedOriginalSource_base_average_bound B U b hb o hR hσ S X poly hmem N hN
    hW hτ hξ stride cells hmass bases hbases htotal x test htest

theorem allocatedOriginal_kernel_average_of_bad_bound :
    let f : Kernel → (X → ℤ) → ℂ := source
    ∀ (reference : ∀ x : Kernel, Good x → (X → ℤ) → ℂ)
      {ε η : ℝ}, 0 ≤ ε →
      (∀ x (hx : Good x) base, base ∈ bases → ‖f x base - reference x hx base‖ ≤ ε) →
      μ.eventProbability (fun x => ¬Good x) ≤ η →
    ‖μ.complexMean (fun x => 𝔼 base ∈ bases, f x base) -
      μ.goodPartBaseMean bases Good reference‖ ≤ ε + η := by
  intro f reference ε η hε hcomparison hbad
  exact (allocatedOriginal_kernel_average B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells
    hmass bases hbases htotal μ selection M test htest reference hε hcomparison).trans
    (add_le_add le_rfl hbad)

theorem allocatedOriginal_affine_kernel_average [Nonempty (Fin dim)]
    (hG : dim * (dim + 2) ≤ Fintype.card G)
    (modulusBound lengthFactor : ℕ) (hmodulusBound : 0 < modulusBound) (hlengthFactor : 0 < lengthFactor)
    {η : ℝ} (hη : 0 < η)
    (hlarge : scalarKernelCutoff (Fin dim) G modulusBound lengthFactor η ≤ S.value)
    (K : G → ℕ) (hKL : ∀ g, K g ≤ S.value) (hDK : ∀ g, S.value ≤ lengthFactor * K g)
    (c : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
    (residues : ∀ g i, ZMod (moduli g i))
    (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliBound : ∀ g i, moduli g i ≤ modulusBound) :
    let cutoff := scalarKernelCutoff (Fin dim) G modulusBound lengthFactor η
    let law := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (K g) modulusBound lengthFactor (c g)
        S.positive (hKL g) (hDK g) (moduli g) (residues g) (hmoduli g) (hmoduliBound g)
        (scalarKernelCutoff_window_size (Fin dim) G hmodulusBound hlengthFactor hη hlarge (hDK g)))
    ∀ (reference : ∀ x : Kernel, GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff x → (X → ℤ) → ℂ)
      {ε : ℝ}, 0 ≤ ε →
      (∀ x (hx : GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff x) base,
        base ∈ bases → ‖source x base - reference x hx base‖ ≤ ε) →
    ‖law.complexMean (fun x => 𝔼 base ∈ bases, source x base) -
      law.goodPartBaseMean bases (GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff)
        reference‖ ≤ ε + η := by
  intro cutoff law reference ε hε hcomparison
  have hbad := affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hG) selection hmodulusBound hlengthFactor hη S.positive
    hlarge K hKL hDK c moduli residues hmoduli hmoduliBound
  exact allocatedOriginal_kernel_average_of_bad_bound B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
    stride cells hmass bases hbases htotal law selection cutoff test htest reference hε hcomparison hbad

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedAveragedCoarseKernelStatement (m dim : ℕ) : Prop :=
    ∃ A a : ℕ, 2 ≤ A ∧ 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    [Nonempty (Fin dim)]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ v, Fintype (B v)] [∀ v, DecidableEq (B v)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {p Etarget T : ℝ} (_hp : 0 ≤ p) (_hE : 0 ≤ Etarget) (_hT : 0 ≤ T)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hn : ∀ j, (n j : ℝ) ≤ p)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (_hRup : ∀ j, R j ≤ Real.exp p) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) (_hmsp : ((m + 2 : ℕ) : ℝ) ≤ p),
    let E := Etarget + 1
    let Q := allocatedKernelPrimitiveBudget p E T
    let S := allocatedCoarseKernelScale (G := G) B U b hR hσ p E T
    let P := allocatedChosenScaleBudget m Q (E + 2) (T + 1)
    let Pc := allocatedComparisonDimension m Q
    let L₀ := allocatedNormalizedInitialScale m Q Pc (E + 2) (T + 1)
    (S.value : ℝ) ≤ Real.exp ((p + Etarget + T + a)^a) ∧
    ∀ (M D : ℕ) (hM : 0 < M) (hD : 0 < D)
      (_hMT : (M : ℝ) ≤ Real.exp T) (_hDp : (D : ℝ) ≤ Real.exp p)
      (selection : Fin dim ↪ G) (_hdim : dim ≤ m + 1)
      (_hG : dim * (dim + 2) ≤ Fintype.card G),
    let η := Real.exp (-(E + 1))
    let cutoff := scalarKernelCutoff (Fin dim) G M D η
    let hcutoff := (scalarKernelCutoff_bounds (Fin dim) G hM hD (Real.exp_pos (-(E + 1)))).1
    let Good := GoodScalarKernelTuple (L := S.value) selection (1 / (cutoff : ℝ)) cutoff
    let GoodKernel := {x : G → IntegerScalarCubeBox (Fin dim) S.value // Good x}
    ∃ hlarge : cutoff ≤ S.value,
    (cutoff : ℝ) ≤ Real.exp Q ∧
    ∃ (degree : GoodKernel → ℕ) (hdegree : ∀ x, 0 < degree x),
    (∀ x, (degree x : ℝ) ≤ Real.exp ((p + Etarget + T + a)^a)) ∧
    ∀ (K : G → ℕ) (hKL : ∀ g, K g ≤ S.value) (hDK : ∀ g, S.value ≤ D * K g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    let kernelLaw := FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (K g) M D (shift g) S.positive
        (hKL g) (hDK g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hD (Real.exp_pos _) hlarge (hDK g)))
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp p)
    {X : Type uX} [Fintype X] [DecidableEq X] (_hXp : (Fintype.card X : ℝ) ≤ p),
    let O := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
    let rows := fun j => (Subtype.val : O j → Finset (Fin dim))
    let ξ₀ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection cutoff Q (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection cutoff Q (E + 2)
    let W : ℝ := Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)
    let hW : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    let Pmass := allocatedUnifiedSamplingBudget m dim A P Q (E + 2)
    ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
      (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (c : ∀ j, U j)
      (_hc : coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U (fun s => c s.1))))
      (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t) {Rrank τ : ℝ} (hτ : 0 < τ),
    let mesh := normalizedTupleRadius X selection cutoff Q (E + 2)
      (Fintype.card (LayerSamplerVariables G I n B)) / 4
    ∀ (_hτp : 1 / τ ≤ Real.exp p) (_hstrideT : ∀ t, (stride t : ℝ) ≤ Real.exp T)
      (_hsize : ∀ t, Real.exp ((p + Etarget + T + a)^a) ≤ (N t : ℝ))
      (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
      (_hRank : Real.exp ((p + Etarget + T + a)^a) ≤ Rrank)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
      {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
      (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))),
    let centeredPoly := fun j => subtractConstant (c j).val (poly j)
    let centeredMem := fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N
    let baseDensity := jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center
    let Z := selectedJointDensityMass bases stride cells widths baseDensity
    ∃ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (hN : ∀ t, 0 < N t) (hZ : 0 < Z),
    let hwidths := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let whole := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let law := whole.prod (selectedJointFiniteLaw bases _hbases stride cells widths hwidths
      hmass baseDensity (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hmem center) hZ)
    (|Z - 1| ≤ Real.exp (-Pmass) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
    ∃ reference : GoodKernel → (X → ℤ) → (Finset (Fin dim) → (X → ℝ) → ℂ) → ℂ,
    (∀ x : GoodKernel, let : NeZero (degree x) := ⟨(hdegree x).ne'⟩
      ∀ base, allocatedRefinedSiteFunctional (τ := τ) (ξ := ξ₀) B U b hR hσ S x.val rows X
        hcutoff selection x.property stride hb o bW (degree x) N hW mesh base cells
        (physicalCubeEuclideanSample U (degree x) centeredPoly centeredMem) Z Pc (T + 1) (Real.exp (coefficientErrorVolumeLog Q + 4)) (reference x base)) ∧
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1),
    ‖kernelLaw.complexMean (fun x => law.complexMean (fun z =>
        physicalCubeSiteTest test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
          (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val))) -
      kernelLaw.goodPartBaseMean bases Good
        (fun x hx base => reference ⟨x, hx⟩ base test)‖ ≤ Real.exp (-Etarget)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedAveragedCoarseKernelComparison (m dim : ℕ) :
    allocatedAveragedCoarseKernelStatement m dim := by
  obtain ⟨A, C, hA, _, hcomparison⟩ := allocatedTestUniformCoarseJointComparison m dim
  obtain ⟨a₀, ha₀, hthreshold⟩ := exists_allocatedKernelThreshold_bound C
  let a := a₀ + 2
  unfold allocatedAveragedCoarseKernelStatement
  refine ⟨A, a, hA, by dsimp [a]; omega, ?_⟩
  intro G _ _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hEtarget hT
    hvars hI hn hJ hRup hRi hσi hmsp E Q S P Pc L₀
  have hE : 0 ≤ E := by dsimp [E]; linarith
  obtain ⟨hQ, hpQ, _, _, _⟩ := allocatedKernelPrimitiveBudget_bounds hp hE hT
  have hexp := Real.exp_le_exp.mpr hpQ
  have hwork : (p + E + T + a₀)^a₀ ≤ (p + Etarget + T + a)^a := by
    have hbase : p + E + T + a₀ ≤ p + Etarget + T + a := by
      dsimp [E, a]
      push_cast
      linarith
    have hone : 1 ≤ p + Etarget + T + a := by
      dsimp [a]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) a₀]
    exact (pow_le_pow_left₀ (by positivity) hbase a₀).trans
      (pow_le_pow_right₀ hone (by dsimp [a]; omega))
  have hcut : (Q + E + (T + 1) + C)^C ≤ (p + Etarget + T + a)^a := by
    have hstep : Q + E + (T + 1) + C ≤ Q + (E + 1) + (T + 1) + C := by linarith
    exact (pow_le_pow_left₀ (by positivity) hstep C).trans
      ((hthreshold hp hE hT).trans hwork)
  obtain ⟨S', hS', hSbound, hkernel⟩ := hcomparison B U b hR hσ hQ hE
    (show 0 ≤ T + 1 by positivity) (hvars.trans hpQ)
    (fun j => (hI j).trans hpQ) (fun j => (hn j).trans hpQ) (fun j => (hJ j).trans hpQ)
    (fun j => (hRup j).trans hexp) (fun j => (hRi j).trans hexp)
    (fun j => (hσi j).trans hexp) (hmsp.trans hpQ)
  have hS : S' = S := hS'
  subst S'
  refine ⟨hSbound.trans (Real.exp_le_exp.mpr hcut), ?_⟩
  intro M D hM hD hMT hDp selection hdim hG η cutoff hcutoff Good GoodKernel
  have hdimP : (dim : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : dim ≤ m + 2)).trans hmsp
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  obtain ⟨hcutoffQ, hlarge⟩ := allocatedCoarseKernelScale_cutoff B U b hR hσ
    hp hE hT hdimP hGp hM hD hMT hDp
  refine ⟨hlarge, hcutoffQ, ?_⟩
  have hforKernel (x : GoodKernel) := hkernel x.val hcutoff hcutoffQ selection x.property hdim
  choose degree hdegree hdegreeBound hconstruct using hforKernel
  refine ⟨degree, hdegree, fun x => (hdegreeBound x).trans (Real.exp_le_exp.mpr hcut), ?_⟩
  intro K hKL hDK shift moduli residues hmoduli hmoduliM kernelLaw
  have hbad : kernelLaw.eventProbability (fun x => ¬Good x) ≤ η :=
    allocatedCoarseKernelScale_affine_bad_probability B U b hR hσ hp hE hT hdimP hGp hG
      selection hM hD hMT hDp K hKL hDK shift moduli residues hmoduli hmoduliM
  have hηlt : η < 1 := by
    change Real.exp (-(E + 1)) < 1
    calc
      _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hexists : ∃ x : G → IntegerScalarCubeBox (Fin dim) S.value, Good x := by
    by_contra! hnone
    have hone : kernelLaw.eventProbability (fun x => ¬Good x) = 1 := by
      simp only [FiniteProbabilityWeights.eventProbability, hnone, not_false_eq_true,
        ite_true, FiniteProbabilityWeights.mean_const]
    linarith
  obtain ⟨x₀, hx₀⟩ := hexists
  let x0 : GoodKernel := ⟨x₀, hx₀⟩
  intro _ _ _ _ _ hb o Cchart Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _ hCp hVp
  let : ∀ x : GoodKernel, NeZero (degree x) := fun x => ⟨(hdegree x).ne'⟩
  have hg (x : GoodKernel) := hconstruct x hb o Cchart Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  choose g hgc hgb hgi hgm hglaw hgproj hdata using hg
  intro X _ _ hXp O rows ξ₀ hξ W hW Pmass poly hpoly hmem center c hc N stride hs Rrank τ hτ
    mesh hτp hstrideT hsize hrank hRank cells hcells bases hbases Kcov _ bW
    centeredPoly centeredMem widths baseDensity Z
  have hresults (x : GoodKernel) := hdata x
    (fun j => (hCp j).trans hexp) (fun j => (hVp j).trans hexp) (hXp.trans hpQ)
    poly hpoly hmem center c hc N stride hs hτ (hτp.trans hexp)
    (fun t => (hstrideT t).trans (Real.exp_le_exp.mpr (by linarith : T ≤ T + 1)))
    (fun t => (Real.exp_le_exp.mpr hcut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hcut).trans hRank) cells hcells bases hbases bW
  choose hmass hN hZ hnormal reference hrep herror using hresults
  let law := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).prod
    (selectedJointFiniteLaw bases hbases stride cells widths
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N (hN x0)) (hmass x0) baseDensity
      (jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hmem center) (hZ x0))
  refine ⟨hmass x0, hN x0, hZ x0, hnormal x0, reference, hrep, ?_⟩
  intro test htest
  have hunit (x : G → IntegerScalarCubeBox (Fin dim) S.value) :
      ‖law.complexMean (fun z => physicalCubeSiteTest test (physicalCubeRootDifferences
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
        (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val))‖ ≤ 1 := by
    apply (law.norm_complexMean_le_mean_norm _).trans
    exact (law.mean_mono (fun _ => physicalCubeSiteTest_norm_le test htest _)).trans_eq (law.mean_const 1)
  have havg := kernelLaw.complexMean_goodPart_comparison Good
    (fun x => law.complexMean (fun z => physicalCubeSiteTest test (physicalCubeRootDifferences
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z.1)
      (allocatedPhysicalCubeDirections B U b S x z.1) z.2.1.val z.2.2.val)))
    (fun x hx => 𝔼 base ∈ bases, reference ⟨x, hx⟩ base test)
    (Real.exp_pos (-E)).le hunit (fun x hx => (herror ⟨x, hx⟩ test htest).2)
  have hηsmall : η ≤ Real.exp (-E) := Real.exp_le_exp.mpr (by linarith : -(E + 1) ≤ -E)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum : Real.exp (-E) + η ≤ Real.exp (-Etarget) := by
    calc
      _ ≤ 2 * Real.exp (-E) := by linarith
      _ ≤ Real.exp 1 * Real.exp (-E) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-Etarget) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [E]
        ring
  exact havg.trans ((add_le_add le_rfl hbad).trans hsum)

end Erdos3.VectorPolynomial

end

end OAI
