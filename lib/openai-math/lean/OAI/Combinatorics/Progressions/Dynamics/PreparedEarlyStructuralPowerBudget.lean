import OAI.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks

namespace OAI

section

namespace Erdos3

open VectorPolynomial

def preparationCoordinateCap (s D T : ℕ) : ℕ := D * (T + 1) ^ s + D + T + 1

noncomputable def preparationModulusCap (s M R : ℕ) (p : ℝ) : ℕ :=
  R * preparationHeight p s ^ M

noncomputable def preparationOscillationCap (s n R : ℕ) (p : ℝ) : ℕ :=
  (s + 1) * (n + 1) ^ s * R * n * s * preparationHeight p s

noncomputable def preparationShrink (s n M R : ℕ) (p δ : ℝ) : ℝ :=
  4 * preparationModulusCap s M R p /
    min 1 (δ / (preparationOscillationCap s n R p + 1))

theorem preparationShrink_one_le (s n M : ℕ) {R : ℕ} {p δ : ℝ}
    (hR : 1 ≤ R) (hp : 0 ≤ p) (hδ : 0 < δ) :
    1 ≤ preparationShrink s n M R p δ := by
  have hheight := preparationHeight_pos hp s
  have hQ : 1 ≤ preparationModulusCap s M R p := by
    exact Nat.mul_pos hR (pow_pos hheight M)
  have hρ : 0 < min 1 (δ / (preparationOscillationCap s n R p + 1)) := by positivity
  apply (le_div_iff₀ hρ).mpr
  have hQreal : (1 : ℝ) ≤ preparationModulusCap s M R p := by exact_mod_cast hQ
  have hρle := min_le_left (1 : ℝ) (δ / (preparationOscillationCap s n R p + 1))
  nlinarith

theorem preparationCoordinateCap_bounds {I J : Type} {s D t T : ℕ}
    {L : RankPreparationFamily I J s} (h : L.Sized D t) (ht : t ≤ T) (i : Fin s) :
    Fintype.card (L i).Coord ≤ preparationCoordinateCap s D T ∧
      Fintype.card (L i).Column ≤ preparationCoordinateCap s D T ∧
      Fintype.card (L i).Row + 1 ≤ preparationCoordinateCap s D T := by
  obtain ⟨hc, hb, hr⟩ := h.uniform ht i
  dsimp only [preparationCoordinateCap]
  omega

theorem preparation_section_bound {I J : Type} {s M R : ℕ} {p : ℝ}
    (L : RankPreparationFamily I J s) (i : Fin s) (hp : 0 ≤ p)
    (hM : (M : ℝ) ≤ p) (hR : (R : ℝ) ≤ Real.exp p)
    (hcoords : Fintype.card (L i).Coord ≤ M)
    (hcols : Fintype.card (L i).Column ≤ M) (hrows : Fintype.card (L i).Row + 1 ≤ M) :
    let He := rankCutDirectionHeight (Fintype.card (L i).Coord)
      (Fintype.card (L i).Column) (Fintype.card (L i).Row)
      (preparationHeight p (s - 1 - i.val)) R
    He ≤ preparationHeight p ((s - 1 - i.val) + 1) ∧ He ≤ preparationHeight p s := by
  intro He
  have he : He ≤ preparationHeight p ((s - 1 - i.val) + 1) :=
    rankCutDirectionHeight_le_preparationHeight _ _ _ _ _ _ hp
      ((Nat.cast_le.mpr hcoords).trans hM) ((Nat.cast_le.mpr hcols).trans hM)
      (by exact_mod_cast (Nat.cast_le.mpr hrows).trans hM) le_rfl hR
  exact ⟨he, he.trans (preparationHeight_mono hp (by omega))⟩

theorem preparation_step_caps (s n M R h He c : ℕ) {p δ : ℝ}
    (hp : 0 ≤ p) (hδ : 0 < δ) (hh : h + 1 ≤ s)
    (he : He ≤ preparationHeight p s) (hc : c ≤ M) :
    let K := (((h + 1 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ (h + 1) * R * n * ((h + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    let ρ₀ := min 1 (δ / (preparationOscillationCap s n R p + 1))
    R * He ^ c ≤ preparationModulusCap s M R p ∧ 0 < ρ₀ ∧ ρ₀ ≤ ρ := by
  intro K ρ ρ₀
  have hheight := preparationHeight_pos hp s
  have hq : He ^ c ≤ preparationHeight p s ^ M :=
    (Nat.pow_le_pow_left he c).trans (Nat.pow_le_pow_right hheight hc)
  have hKnat : (h + 1 + 1) * (n + 1) ^ (h + 1) * R * n * (h + 1) * He ≤
      preparationOscillationCap s n R p := by
    unfold preparationOscillationCap
    gcongr
  have hK : K ≤ preparationOscillationCap s n R p := by
    dsimp only [K]
    exact_mod_cast hKnat
  refine ⟨Nat.mul_le_mul_left R hq, by dsimp [ρ₀]; positivity, ?_⟩
  apply min_le_min_left 1
  exact div_le_div_of_nonneg_left hδ.le (by dsimp [K]; positivity) (by linarith)

theorem preparation_large_side {s n M R h He c : ℕ} {p δ N : ℝ}
    (hp : 0 ≤ p) (hδ : 0 < δ) (hh : h + 1 ≤ s)
    (he : He ≤ preparationHeight p s) (hc : c ≤ M)
    (hN : preparationShrink s n M R p δ ≤ N) :
    let K := (((h + 1 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ (h + 1) * R * n * ((h + 1 : ℕ) : ℝ) * He
    4 * ((R * He ^ c : ℕ) : ℝ) ≤ min 1 (δ / (K + 1)) * N := by
  intro K
  obtain ⟨hq, hρ, hρle⟩ := preparation_step_caps s n M R h He c hp hδ hh he hc
  have hQ0 : 0 ≤ (4 : ℝ) * preparationModulusCap s M R p := by positivity
  have hN0 : 0 ≤ N := (div_nonneg hQ0 hρ.le).trans hN
  have hl := (div_le_iff₀ hρ).mp hN
  have hqr : ((R * He ^ c : ℕ) : ℝ) ≤ preparationModulusCap s M R p := Nat.cast_le.mpr hq
  have hm := mul_le_mul_of_nonneg_right hρle hN0
  nlinarith

theorem preparation_side_loss {s n M R h He c q len : ℕ} {p δ N : ℝ}
    (hp : 0 ≤ p) (hδ : 0 < δ) (hh : h + 1 ≤ s)
    (he : He ≤ preparationHeight p s) (hc : c ≤ M) (hq : q ≤ R * He ^ c)
    (hN : 0 ≤ N)
    (hlen : min 1 (δ / ((((h + 1 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ (h + 1) *
      R * n * ((h + 1 : ℕ) : ℝ) * He + 1)) * N ≤ 4 * q * len) :
    N ≤ preparationShrink s n M R p δ * len := by
  obtain ⟨hQ, hρ, hρle⟩ := preparation_step_caps s n M R h He c hp hδ hh he hc
  have hm := mul_le_mul_of_nonneg_right hρle hN
  have hqr : (q : ℝ) ≤ preparationModulusCap s M R p := Nat.cast_le.mpr (hq.trans hQ)
  have hlen0 : (0 : ℝ) ≤ len := Nat.cast_nonneg _
  have hb : min 1 (δ / (preparationOscillationCap s n R p + 1)) * N ≤
      (4 * preparationModulusCap s M R p) * len := by nlinarith
  dsimp only [preparationShrink]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hρ).mpr
  nlinarith

end Erdos3

end

section

namespace Erdos3

private theorem preparationCoordinateCap_real_bound {s m D : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hm : m ≤ s) (hD : (D : ℝ) ≤ p) :
    (preparationCoordinateCap m D (m * D) : ℝ) ≤
      p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1 := by
  have hT : (m : ℝ) * D ≤ (s : ℝ) * p :=
    mul_le_mul (Nat.cast_le.mpr hm) hD (Nat.cast_nonneg D) (Nat.cast_nonneg s)
  have hpowers : ((m : ℝ) * D + 1) ^ m ≤ ((s : ℝ) * p + 1) ^ s :=
    (pow_le_pow_left₀ (by positivity) (add_le_add hT le_rfl) m).trans
      (pow_le_pow_right₀ (by nlinarith [mul_nonneg (Nat.cast_nonneg s) hp]) hm)
  have hmul := mul_le_mul hD hpowers (by positivity : 0 ≤ ((m : ℝ) * D + 1) ^ m) hp
  simp only [preparationCoordinateCap, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
  linarith

theorem exists_preparation_input_power_budget (s e : ℕ) :
    ∃ a E : ℕ, 2 ≤ a ∧ 2 ≤ E ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ m D dim R : ℕ, m ≤ s → (D : ℝ) ≤ p → (dim : ℝ) ≤ p →
        (R : ℝ) ≤ Real.exp ((p + 2) ^ e) →
        let pPrep := (p + 2) ^ a
        let δ := Real.exp (-((p + 2) ^ e))
        let T := m * D
        let M := preparationCoordinateCap m D T
        0 ≤ pPrep ∧ (M : ℝ) ≤ pPrep ∧ (m : ℝ) ≤ pPrep ∧ (dim : ℝ) ≤ pPrep ∧
          (T : ℝ) + 1 ≤ pPrep ∧ 0 < δ ∧
          (δ / ((T : ℝ) * M + 1))⁻¹ ≤ Real.exp pPrep ∧
          (R : ℝ) ≤ Real.exp pPrep ∧
          (pPrep + 2) ^ (budgetDepthExponent 38 m + 7) ≤ (p + 2) ^ E := by
  let Mpoly : Polynomial ℕ :=
    Polynomial.X * (Polynomial.C s * Polynomial.X + 1) ^ s + Polynomial.X +
      Polynomial.C s * Polynomial.X + 1
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ e +
    (Polynomial.C s * Polynomial.X) * Mpoly + Mpoly +
      Polynomial.C s * Polynomial.X + Polynomial.X + Polynomial.C s + 2
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_fixed_power_budget Q
  let E := (a + 2) * (budgetDepthExponent 38 s + 7)
  refine ⟨a, E, ha, by dsimp [E]; nlinarith [preparationExponent_pos s], ?_⟩
  intro p hp m D dim R hm hD hdim hR
  dsimp only
  have hp0 : 0 ≤ p := by linarith
  let Mup := p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1
  let T := m * D
  let M := preparationCoordinateCap m D T
  let δ := Real.exp (-((p + 2) ^ e))
  let pPrep := (p + 2) ^ a
  have hMup : 0 ≤ Mup := by dsimp [Mup]; positivity
  have hTup : 0 ≤ (s : ℝ) * p := mul_nonneg (Nat.cast_nonneg s) hp0
  have hprod0 : 0 ≤ (s : ℝ) * p * Mup := mul_nonneg hTup hMup
  have hpow0 : 0 ≤ (p + 2) ^ e := by positivity
  have hbudget : (p + 2) ^ e + (s : ℝ) * p * Mup + Mup + (s : ℝ) * p + p + s + 2 ≤ pPrep := by
    simpa [Q, Mpoly, Mup, pPrep, Polynomial.eval₂_pow] using hbound p hp0
  have hM : (M : ℝ) ≤ Mup := preparationCoordinateCap_real_bound hp0 hm hD
  have hT : (T : ℝ) ≤ (s : ℝ) * p := by
    dsimp only [T]
    rw [Nat.cast_mul]
    exact mul_le_mul (Nat.cast_le.mpr hm) hD (Nat.cast_nonneg D) (Nat.cast_nonneg s)
  have hTM : (T : ℝ) * M ≤ (s : ℝ) * p * Mup :=
    mul_le_mul hT hM (Nat.cast_nonneg M) hTup
  have hpPrep : 0 ≤ pPrep := by dsimp [pPrep]; positivity
  have hApPrep : (p + 2) ^ e ≤ pPrep := by linarith
  have hshare : (δ / ((T : ℝ) * M + 1))⁻¹ ≤ Real.exp pPrep := by
    calc
      _ = ((T : ℝ) * M + 1) * Real.exp ((p + 2) ^ e) := by
        simp only [δ, div_eq_mul_inv, Real.exp_neg, mul_inv_rev, inv_inv]
      _ ≤ Real.exp ((T : ℝ) * M) * Real.exp ((p + 2) ^ e) :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_nonneg _)
      _ = Real.exp ((T : ℝ) * M + (p + 2) ^ e) := (Real.exp_add _ _).symm
      _ ≤ Real.exp pPrep := Real.exp_le_exp.mpr (by linarith)
  refine ⟨hpPrep, ?_, ?_, ?_, ?_, Real.exp_pos _, hshare,
    hR.trans (Real.exp_le_exp.mpr hApPrep), ?_⟩
  · exact hM.trans (by linarith)
  · have hmR : (m : ℝ) ≤ s := Nat.cast_le.mpr hm
    linarith
  · exact hdim.trans (by linarith)
  · linarith
  · have hdepth : budgetDepthExponent 38 m + 7 ≤ budgetDepthExponent 38 s + 7 :=
      Nat.add_le_add_right (preparationExponent_mono hm) 7
    exact (pow_le_pow_right₀ (by linarith : 1 ≤ pPrep + 2) hdepth).trans
      (shifted_power_budget_le hp0 a (budgetDepthExponent 38 s + 7))

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

private theorem early_preparationCoordinateCap_bound {s m D : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hm : m ≤ s) (hD : (D : ℝ) ≤ p) :
    (preparationCoordinateCap m D (m * D) : ℝ) ≤
      p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1 := by
  have hT : (m : ℝ) * D ≤ (s : ℝ) * p :=
    mul_le_mul (Nat.cast_le.mpr hm) hD (Nat.cast_nonneg D) (Nat.cast_nonneg s)
  have hpowers : ((m : ℝ) * D + 1) ^ m ≤ ((s : ℝ) * p + 1) ^ s :=
    (pow_le_pow_left₀ (by positivity) (add_le_add hT le_rfl) m).trans
      (pow_le_pow_right₀ (by nlinarith [mul_nonneg (Nat.cast_nonneg s) hp]) hm)
  have hmul := mul_le_mul hD hpowers (by positivity : 0 ≤ ((m : ℝ) * D + 1) ^ m) hp
  simp only [preparationCoordinateCap, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
  linarith

theorem exists_prepared_early_structural_power_budget (s paddingDepth : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ m D nX : ℕ, m ≤ s → (D : ℝ) ≤ p → (nX : ℝ) ≤ p →
        let M := preparationCoordinateCap m D (m * D)
        let q := max m paddingDepth
        let Jalloc := modularInitialBlockCount q (nX + q * M)
        (M : ℝ) + Jalloc + enlargedPreparedCommonSamplerDimension q M Jalloc +
          allocatedUniformChartLog (M : ℝ) ≤ (p + 2) ^ C := by
  classical
  let K := max s paddingDepth
  let A : ℕ := ∑ r : Fin (K + 1),
    (2 ^ r.val * (2 ^ (2 * r.val) * r.val.factorial + 1) + 1)
  let B : ℕ := ∑ r : Fin (K + 1), ∑ j : Fin r.val, preparedCommonBlockCount r.val j
  let Mpoly : Polynomial ℕ :=
    Polynomial.X * (Polynomial.C s * Polynomial.X + 1) ^ s + Polynomial.X +
      Polynomial.C s * Polynomial.X + 1
  let Jpoly : Polynomial ℕ :=
    Polynomial.C A * (Polynomial.X + Polynomial.C K * Mpoly + 11)
  let P : Polynomial ℕ :=
    Mpoly + Jpoly +
      (Polynomial.C ((K + 1) * (K + 3)) + Mpoly * Polynomial.C K * Polynomial.C B +
        Mpoly + Polynomial.C K + 2 +
        (Polynomial.C (K + 2) + Mpoly * Polynomial.C K * Polynomial.C K) * Jpoly) +
      20 * (Mpoly + 1) ^ 3
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp m D nX hm hD hnX
  dsimp only
  let M := preparationCoordinateCap m D (m * D)
  let q := max m paddingDepth
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let Mup := p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1
  let Jup := (A : ℝ) * (p + (K : ℝ) * Mup + 11)
  have hp0 : 0 ≤ p := by linarith
  have hMup : 0 ≤ Mup := by dsimp [Mup]; positivity
  have hJup : 0 ≤ Jup := by dsimp [Jup]; positivity
  have hq : q ≤ K := max_le_max hm le_rfl
  have hqR : (q : ℝ) ≤ K := Nat.cast_le.mpr hq
  have hA : 2 ^ q * (2 ^ (2 * q) * q.factorial + 1) + 1 ≤ A := by
    exact Finset.single_le_sum
      (f := fun r : Fin (K + 1) =>
        2 ^ r.val * (2 ^ (2 * r.val) * r.val.factorial + 1) + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨q, Nat.lt_succ_of_le hq⟩)
  have hB : (∑ j : Fin q, preparedCommonBlockCount q j) ≤ B := by
    exact Finset.single_le_sum
      (f := fun r : Fin (K + 1) => ∑ j : Fin r.val, preparedCommonBlockCount r.val j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨q, Nat.lt_succ_of_le hq⟩)
  have hM : (M : ℝ) ≤ Mup := early_preparationCoordinateCap_bound hp0 hm hD
  have hJnat : Jalloc ≤ A * (nX + q * M + 11) :=
    (modularInitialBlockCount_linear_bound q (nX + q * M)).trans
      (Nat.mul_le_mul_right _ hA)
  have hJ : (Jalloc : ℝ) ≤ Jup := by
    have hJreal : (Jalloc : ℝ) ≤ (A : ℝ) * ((nX : ℝ) + (q : ℝ) * M + 11) := by
      exact_mod_cast hJnat
    refine hJreal.trans ?_
    dsimp only [Jup]
    gcongr
  have hdim : (enlargedPreparedCommonSamplerDimension q M Jalloc : ℝ) ≤
      ((K : ℝ) + 1) * (K + 3) + Mup * K * B + Mup + K + 2 +
        (K + 2 + Mup * K * K) * Jup := by
    rw [enlargedPreparedCommonSamplerDimension_polynomial]
    simp only [preparedCommonSamplerDimension, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    have hBR : ((∑ j : Fin q, preparedCommonBlockCount q j : ℕ) : ℝ) ≤ B :=
      Nat.cast_le.mpr hB
    gcongr
  have hchart : allocatedUniformChartLog (M : ℝ) ≤ 20 * (Mup + 1) ^ 3 := by
    unfold allocatedUniformChartLog
    gcongr
  have htotal : Mup + Jup +
      (((K : ℝ) + 1) * (K + 3) + Mup * K * B + Mup + K + 2 +
        (K + 2 + Mup * K * K) * Jup) + 20 * (Mup + 1) ^ 3 ≤ (p + 2) ^ C := by
    simpa [P, Mpoly, Jpoly, Mup, Jup, Polynomial.eval₂_pow,
      Nat.cast_add, Nat.cast_mul] using hbound p hp0
  exact (add_le_add (add_le_add (add_le_add hM hJ) hdim) hchart).trans htotal

end Erdos3

end

end OAI
