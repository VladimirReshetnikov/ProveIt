import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.Combinatorics.Progressions.Lattices.PositivePartitionIntegerExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

noncomputable def productPartitionWeight (j : ∀ a, κ a) (x : ∀ a, X a) : ℝ :=
  ∏ a, ψ a (j a) (x a)

theorem productPartitionWeight_nonneg (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) : 0 ≤ productPartitionWeight ψ j x :=
  Finset.prod_nonneg (fun a _ => hψ a (j a) (x a))

theorem productPartitionWeight_pos_coordinate (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (j : ∀ a, κ a) (x : ∀ a, X a) (hx : 0 < productPartitionWeight ψ j x) (a : α) :
    0 < ψ a (j a) (x a) := by
  classical
  apply lt_of_le_of_ne (hψ a (j a) (x a))
  intro hz
  have hw : productPartitionWeight ψ j x = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ a) hz.symm
  linarith

variable [DecidableEq α] [∀ a, Fintype (κ a)]

theorem sum_productPartitionWeight (hsum : ∀ a x, ∑ j, ψ a j x = 1) (x : ∀ a, X a) :
    ∑ j, productPartitionWeight ψ j x = 1 := by
  unfold productPartitionWeight
  rw [← Fintype.prod_sum (fun a j => ψ a j (x a))]
  simp only [hsum, Finset.prod_const_one]

variable [∀ a, PseudoMetricSpace (X a)]

omit [DecidableEq α] [∀ a, Fintype (κ a)] in
theorem productPartitionWeight_diameter {rho : ℝ} (hrho : 0 ≤ rho)
    (hψ : ∀ a j x, 0 ≤ ψ a j x)
    (hdiam : ∀ a j x y, 0 < ψ a j x → 0 < ψ a j y → dist x y ≤ rho)
    (j : ∀ a, κ a) (x y : ∀ a, X a)
    (hx : 0 < productPartitionWeight ψ j x) (hy : 0 < productPartitionWeight ψ j y) :
    dist x y ≤ rho := by
  apply (dist_pi_le_iff hrho).mpr
  intro a
  exact hdiam a (j a) (x a) (y a)
    (productPartitionWeight_pos_coordinate ψ hψ j x hx a)
    (productPartitionWeight_pos_coordinate ψ hψ j y hy a)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def intervalTensorWeight {S : Type*} [Fintype S] (B r : ℝ)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : ℝ :=
  ∏ i, intervalSiteWeight B r (k i) (x i)

noncomputable def intervalTensorApprox {S : Type*} [Fintype S] [DecidableEq S]
    (B r : ℝ) (F : (S → ℝ) → ℂ) (x : S → ℝ) : ℂ :=
  ∑ k : S → Fin (intervalSiteCount B r),
    (intervalTensorWeight B r k x : ℂ) * F (fun i => intervalSiteCenter B r (k i))

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

theorem intervalTensorWeight_near {S : Type*} [Fintype S] {B r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) (hx : 0 < intervalTensorWeight B r k x) :
    dist x (fun i => intervalSiteCenter B r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hp := productPartitionWeight_pos_coordinate (fun _ : S => intervalSiteWeight B r)
    (fun _ j x => (intervalSiteWeight_range B hr j x).1) k x hx i
  exact (intervalSiteWeight_near B r (k i) (x i) hp).le

theorem intervalTensorApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖F x - intervalTensorApprox B r F x‖ ≤ 2 * K * r := by
  apply norm_sub_positive_sum_le (fun k => intervalTensorWeight B r k x)
    (fun k => F (fun i => intervalSiteCenter B r (k i))) (F x) _
    (fun k => intervalTensorWeight_nonneg B hr k x) (intervalTensorWeight_sum hB hr x hx)
  intro k hk
  have h := hF.dist_le_mul x (fun i => intervalSiteCenter B r (k i))
  rw [dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (intervalTensorWeight_near hr k x hk) K.coe_nonneg).trans_eq (by ring))

theorem intervalTensorApprox_coefficient_sum {S : Type*} [Fintype S] [DecidableEq S]
    (B r : ℝ) (F : (S → ℝ) → ℂ) {A : ℝ} (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ k : S → Fin (intervalSiteCount B r), ‖F (fun i => intervalSiteCenter B r (k i))‖) ≤
      (intervalSiteCount B r : ℝ)^Fintype.card S * A := by
  calc
    _ ≤ ∑ _k : S → Fin (intervalSiteCount B r), A := Finset.sum_le_sum (fun k _ => hF _)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_native_product_partition_approximation (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p rho : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0), LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤
                  (ell : ℝ) * (productMetricBound d : ℝ) * rho := by
  obtain ⟨C, hC, hpart⟩ := exists_native_factor_partitions s a
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p rho hp hα hD hrho hscale
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, hdiam⟩ :=
    hpart D hp hα hD hrho hscale
  refine ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hv hbound
  let F := v ∘ (productSpaceEquiv D).symm
  have hF : LipschitzWith (ell * productMetricBound d) F :=
    hv.comp (productSpaceEquiv_symm_lipschitz D)
  obtain ⟨c, hc, herr⟩ := exists_bounded_complex_partition_approximation
    (productPartitionWeight ψ) (productPartitionWeight_nonneg ψ (fun i j x => (hunit i j x).1))
    (sum_productPartitionWeight ψ hsum)
    (productPartitionWeight_diameter ψ hrho.le (fun i j x => (hunit i j x).1) hdiam)
    F 2 (fun x => hbound _) hF
  refine ⟨c, hc, fun x => ?_⟩
  have h := herr (productSpaceEquiv D x)
  simp only [F, Function.comp_apply, Equiv.symm_apply_apply, productPartitionWeight,
    productSpaceEquiv_apply, NNReal.coe_mul] at h
  push_cast at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_controlled_native_product_approximation (s a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p epsilon : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      letI := (pi D).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧ (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ (v : (pi D).Space → ℂ) (ell : ℝ≥0),
              (ell : ℝ) ≤ Real.exp ((p + 2) ^ b) → LipschitzWith ell v → (∀ x, ‖v x‖ ≤ 2) →
              ∃ c : (∀ i, Fin (n i)) → ℂ, (∀ j, ‖c j‖ ≤ 2) ∧
                ∀ x, ‖v x - ∑ j, (∏ i, (ψ i (j i) (productProjection D i x) : ℂ)) * c j‖ ≤ epsilon := by
  obtain ⟨c, _, hpart⟩ := exists_native_product_partition_approximation s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 2) ^ a + (X + 2) ^ b + (X + 4) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ _ _ _ _ d D p epsilon hp hα hD hepsilon hscale
  let q := p + (p + 2) ^ a + (p + 2) ^ b + (p + 4) ^ 4
  have hpq : p ≤ q := by
    dsimp [q]
    linarith [pow_nonneg (by linarith : 0 ≤ p + 2) a,
      pow_nonneg (by linarith : 0 ≤ p + 2) b, sq_nonneg ((p + 4) ^ 2)]
  have hq : 0 ≤ q := hp.trans hpq
  let A := (p + 2) ^ b + (p + 4) ^ 4
  let rho := epsilon / Real.exp A
  have hrho : 0 < rho := div_pos hepsilon (Real.exp_pos _)
  have hrhoscale : 1 / rho ≤ Real.exp ((q + 2) ^ 1) := by
    calc
      1 / rho = Real.exp A * (1 / epsilon) := by dsimp [rho]; field_simp
      _ ≤ Real.exp A * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
      _ = Real.exp (A + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A, q]; simp only [pow_one]; linarith)
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  obtain ⟨n, hn, hnb, hcount, K, hKb, ψ, hunit, hsum, hLip, happ⟩ :=
    hpart D hq (hα.trans hpq) (fun i => (hD i).mono (D i) hpq) hrho hrhoscale
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hexp := Real.exp_le_exp.mpr hcost
  refine ⟨n, hn, fun i => (hnb i).trans hexp, hcount.trans hexp,
    K, fun i => (hKb i).trans hexp, ψ, hunit, hsum, hLip, ?_⟩
  intro v ell hell hv hb
  obtain ⟨coeff, hcoeff, herr⟩ := happ v ell hv hb
  refine ⟨coeff, hcoeff, fun x => (herr x).trans ?_⟩
  calc
    (ell : ℝ) * (productMetricBound d : ℝ) * rho ≤
        Real.exp ((p + 2) ^ b) * Real.exp ((p + 4) ^ 4) * rho :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hell (productMetricBound_le_exp d hp hα (fun i => (hD i).1))
          (productMetricBound d).coe_nonneg (Real.exp_nonneg _)) hrho.le
    _ = epsilon := by rw [← Real.exp_add]; dsimp [rho, A]; field_simp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_bounded_variable_patch_expansion (d a : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] [DecidableEq σ]
      {s N P : ℕ} [NeZero N] [NeZero P] {p ρ : ℝ},
      Fintype.card σ ≤ d → 1 ≤ s → 0 ≤ p → (P : ℝ) ≤ Real.exp p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ f : (σ → ℤ) → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      (∀ y : σ → ℤ, (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
        ∃ F : (σ → ℤ) → ℂ,
          Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p F) ∧
          (∀ x, ‖F x‖ ≤ 1) ∧
          ∀ (x : σ → ℤ) (δ : ℝ), 0 ≤ δ →
            (∀ k, |(x k : ℝ)| ≤ (N : ℝ)) → (∀ k, (P : ℤ) ∣ x k - y k) →
            (∀ k, |(x k : ℝ) - (y k : ℝ)| ≤ (N : ℝ) * δ) →
            ‖f x - F x‖ ≤ Real.exp p * δ) →
      ∃ F : (σ → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) F) ∧
        (∀ x : σ → ZMod N, ‖F (fun k => ((x k).val : ℤ))‖ ≤ 1) ∧
        (𝔼 x : σ → ZMod N,
          ‖f (fun k => ((x k).val : ℤ)) - F (fun k => ((x k).val : ℤ))‖) ≤
            Real.exp (p + (18 * d + 2)) * (ρ + 1 / N) := by
  obtain ⟨A, _, hpartition⟩ := exists_interval_residue_partition a
  obtain ⟨B, _, hweighted⟩ := exists_positive_weighted_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := Polynomial.C d * Q + X + Polynomial.C d
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B + R)
  refine ⟨C, hC, ?_⟩
  intro σ _ _ s N P _ _ p ρ hσ hs hp hP hρ hprec f hf hlocal
  classical
  obtain ⟨n, _hn, hcard, ψ, hψ, hsum, hdiam⟩ := hpartition N P hp hP hρ hprec
  let J := σ → Fin n × ZMod P
  let v := fun (x : σ → ZMod N) (k : σ) => ((x k).val : ℤ)
  have hv (x : σ → ZMod N) (k : σ) : |(v x k : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x k).val))]
    exact Nat.cast_le.mpr (x k).val_lt.le
  let w := productPartitionWeight (fun _ : σ => ψ)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ k j x, 0 ≤ (fun _ : σ => ψ) k j x :=
    fun _ j x => ((hψ j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hchoose (j : J) : ∃ y : σ → ZMod N,
      ∀ x, (∀ k, x k ∉ E) → 0 < w j x → (∀ k, y k ∉ E) ∧ 0 < w j y := by
    by_cases h : ∃ y, (∀ k, y k ∉ E) ∧ 0 < w j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hwx => False.elim (h ⟨x, hx, hwx⟩)⟩
  choose y hy using hchoose
  choose S hS hSnorm hSlocal using fun j => hlocal (v (y j)) (hv (y j))
  have hgood (j : J) (x : σ → ZMod N)
      (hx : x ∉ coordinateExceptional E) (hwx : 0 < w j x) :
      ‖f (v x) - S j (v x)‖ ≤ Real.exp p * ρ := by
    have hx' := (not_mem_coordinateExceptional E x).mp hx
    obtain ⟨hy', hwy⟩ := hy j x hx' hwx
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j (y j) hwy
    apply hSlocal j (v x) ρ hρ.le (hv x)
    · intro k
      exact (hdiam (j k) (x k) (y j k) (hx' k) (hy' k) (hposx k) (hposy k)).2
    · intro k
      simpa only [v, Int.cast_natCast] using
        (hdiam (j k) (x k) (y j k) (hx' k) (hy' k) (hposx k) (hposy k)).1
  have herr := complex_partition_approximation_mean_error (coordinateExceptional E)
    w (fun j x => S j (v x)) (fun x => f (v x))
    (mul_nonneg (Real.exp_nonneg p) hρ.le) hw hwSum
    (fun j x => hSnorm j (v x)) (fun x => hf (v x)) hgood
  let q := (p + A) ^ A
  let r := (d : ℝ) * q + p + d
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpr : p ≤ r := by
    dsimp only [r]
    linarith only [mul_nonneg hd0 hq, hd0]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hσd : (Fintype.card σ : ℝ) ≤ d := by exact_mod_cast hσ
  have hqr : q ≤ r := by dsimp only [r]; nlinarith only [hq, hp, hd']
  have hdr : (Fintype.card σ : ℝ) ≤ r := by
    dsimp only [r]
    nlinarith only [hq, hp, hd', hσd]
  have hJ : (Fintype.card J : ℝ) ≤ Real.exp r := by
    simp only [J, Fintype.card_fun, Nat.cast_pow]
    calc
      _ ≤ (Real.exp q) ^ Fintype.card σ :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard (Fintype.card σ)
      _ = Real.exp (Fintype.card σ * q) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        dsimp only [r]
        nlinarith only [hp, hq, hσd, hd'])
  have hfamily (j : J) : ∃ g : (σ → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((r + B) ^ B) g) ∧
      ∀ x : σ → ZMod N, g (v x) = (w j x : ℂ) * S j (v x) := by
    obtain ⟨g, hg, he⟩ := hweighted ((Classical.choice (hS j)).mono hpr) hr hdr
      (fun k => ψ (j k)) (fun k => (hψ (j k)).mono hs hqr)
    refine ⟨g, hg, ?_⟩
    intro x
    simpa only [w, productPartitionWeight, Complex.ofReal_prod] using he x
  choose g hG he using hfamily
  let F := fun x => ∑ j : J, g j x
  have hcoeff : (∑ _j : J, ‖(1 : ℂ)‖) ≤ Real.exp r := by simpa using hJ
  have hcost : (r + B) ^ B + r ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hF : NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) F := by
    simpa only [F, one_mul] using
      ((NativeIntegerExpansion.weightedSum (fun j => Classical.choice (hG j))
        (fun _ => 1) hr hJ hcoeff).mono hcost)
  have heval (x : σ → ZMod N) : F (v x) = ∑ j : J, (w j x : ℂ) * S j (v x) := by
    apply Finset.sum_congr rfl
    intro j _
    exact he j x
  refine ⟨F, ⟨hF⟩, ?_, ?_⟩
  · intro x
    rw [show F (fun k => ((x k).val : ℤ)) = F (v x) from rfl, heval]
    exact norm_positive_partition_sum_le_one (fun j => w j x) (fun j => S j (v x))
      (fun j => hw j x) (hwSum x) (fun j => hSnorm j (v x))
  · have hdensity : ((coordinateExceptional (ι := σ) E).card : ℝ) /
        Fintype.card (σ → ZMod N) ≤ d * (E.card : ℝ) / N := by
      have hbase := coordinateExceptional_density_le (ι := σ) E
      simp only [ZMod.card] at hbase
      exact hbase.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hσd (Nat.cast_nonneg _)) (Nat.cast_nonneg N))
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have hexp : 1 ≤ Real.exp p := Real.one_le_exp hp
    have hρexp : ρ ≤ Real.exp p * ρ := le_mul_of_one_le_left hρ.le hexp
    have hNexp : (1 : ℝ) / N ≤ Real.exp p * (1 / N) := le_mul_of_one_le_left hN hexp
    have hconstant : (18 * (d : ℝ) + 2) ≤ Real.exp (18 * d + 2) := by
      linarith [Real.add_one_le_exp (18 * (d : ℝ) + 2)]
    have hbound : Real.exp p * ρ +
        2 * ((coordinateExceptional (ι := σ) E).card : ℝ) /
          Fintype.card (σ → ZMod N) ≤ Real.exp (p + (18 * d + 2)) * (ρ + 1 / N) := by
      calc
        _ = Real.exp p * ρ + 2 * (((coordinateExceptional (ι := σ) E).card : ℝ) /
            Fintype.card (σ → ZMod N)) := by ring
        _ ≤ Real.exp p * ρ + 2 * (d * (E.card : ℝ) / N) := by gcongr
        _ = Real.exp p * ρ + 2 * d * ((E.card : ℝ) / N) := by ring
        _ ≤ Real.exp p * ρ + 2 * d * (6 * ρ + 3 / N) := by gcongr
        _ = Real.exp p * ρ + 12 * d * ρ + 6 * d * (1 / N) := by ring
        _ ≤ Real.exp p * ρ + 12 * d * (Real.exp p * ρ) +
            6 * d * (Real.exp p * (1 / N)) := by gcongr
        _ = Real.exp p * ((12 * d + 1) * ρ + 6 * d * (1 / N)) := by ring
        _ ≤ Real.exp p * ((18 * d + 2) * (ρ + 1 / N)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg p)
          nlinarith [mul_nonneg (Nat.cast_nonneg d) hρ.le,
            mul_nonneg (Nat.cast_nonneg d) hN]
        _ = (18 * d + 2) * Real.exp p * (ρ + 1 / N) := by ring
        _ ≤ Real.exp (18 * d + 2) * Real.exp p * (ρ + 1 / N) := by gcongr
        _ = _ := by rw [← Real.exp_add, add_comm (18 * (d : ℝ) + 2) p]
    change (𝔼 x : σ → ZMod N, ‖f (v x) - F (v x)‖) ≤ _
    simpa only [heval] using herr.trans hbound

end Erdos3

end

end OAI
