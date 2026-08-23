import IntegerPoints.InverseJet

/-!
# Finite-order stability of normalized inverse jets

The normalized Faà di Bruno equations are triangular: at order `p`, the one-block term is
`u 1 * z p`, while every other term uses inverse jets of order strictly below `p`.  This module
turns that observation into a quantitative finite-order stability theorem.

The constants are intentionally finite and structural rather than optimized.  A product
perturbation lemma first controls a product when every factor is bounded and perturbed by
`O(ε)`.  Induction on the jet order then gives a single constant for all orders up to a fixed
cutoff.  Nothing in this module depends on the analytic-number-theory definition of the
Graham--Kolesnik class.
-/

open scoped BigOperators
open Finset

namespace LeanProofs.IntegerPoints

namespace InverseJet

/-! ## Finite-product perturbations -/

/-- Bound the absolute value of a finite product by the product of pointwise bounds. -/
theorem abs_prod_le_prod_of_abs_le {ι : Type*} (t : Finset ι) (x B : ι → ℝ)
    (hx : ∀ i ∈ t, |x i| ≤ B i) :
    |∏ i ∈ t, x i| ≤ ∏ i ∈ t, B i := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i hi ↦ abs_nonneg (x i)) hx

/-- A deliberately coarse but stable perturbation bound for a finite product.  Requiring
`B i ≥ 1` lets us retain the symmetric and convenient constant
`(∑ i, D i) * ∏ i, B i`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (t : Finset ι) (x y B D : ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hB : ∀ i ∈ t, 1 ≤ B i) (hD : ∀ i ∈ t, 0 ≤ D i)
    (hx : ∀ i ∈ t, |x i| ≤ B i) (hy : ∀ i ∈ t, |y i| ≤ B i)
    (hxy : ∀ i ∈ t, |x i - y i| ≤ ε * D i) :
    |(∏ i ∈ t, x i) - ∏ i ∈ t, y i| ≤
      ε * (∑ i ∈ t, D i) * ∏ i ∈ t, B i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      have hBt : ∀ i ∈ t, 1 ≤ B i := fun i hi ↦ hB i (mem_insert_of_mem hi)
      have hDt : ∀ i ∈ t, 0 ≤ D i := fun i hi ↦ hD i (mem_insert_of_mem hi)
      have hxt : ∀ i ∈ t, |x i| ≤ B i := fun i hi ↦ hx i (mem_insert_of_mem hi)
      have hyt : ∀ i ∈ t, |y i| ≤ B i := fun i hi ↦ hy i (mem_insert_of_mem hi)
      have hxyt : ∀ i ∈ t, |x i - y i| ≤ ε * D i :=
        fun i hi ↦ hxy i (mem_insert_of_mem hi)
      have hprodX : |∏ i ∈ t, x i| ≤ ∏ i ∈ t, B i :=
        abs_prod_le_prod_of_abs_le t x B hxt
      have hprodDiff : |(∏ i ∈ t, x i) - ∏ i ∈ t, y i| ≤
          ε * (∑ i ∈ t, D i) * ∏ i ∈ t, B i :=
        ih hBt hDt hxt hyt hxyt
      have hprodB : 0 ≤ ∏ i ∈ t, B i :=
        Finset.prod_nonneg fun i hi ↦ (hBt i hi).trans' zero_le_one
      have hsumD : 0 ≤ ∑ i ∈ t, D i := Finset.sum_nonneg hDt
      have hDa : 0 ≤ D a := hD a (mem_insert_self a t)
      have hBa : 1 ≤ B a := hB a (mem_insert_self a t)
      have hDa_le : D a ≤ D a * B a := by
        nlinarith [mul_nonneg hDa (sub_nonneg.mpr hBa)]
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        Finset.prod_insert ha]
      calc
        |x a * (∏ i ∈ t, x i) - y a * ∏ i ∈ t, y i| =
            |(x a - y a) * (∏ i ∈ t, x i) +
              y a * ((∏ i ∈ t, x i) - ∏ i ∈ t, y i)| := by
                congr 1
                ring
        _ ≤ |x a - y a| * |∏ i ∈ t, x i| +
              |y a| * |(∏ i ∈ t, x i) - ∏ i ∈ t, y i| := by
          simpa only [abs_mul] using
            (abs_add_le
              ((x a - y a) * (∏ i ∈ t, x i))
              (y a * ((∏ i ∈ t, x i) - ∏ i ∈ t, y i)))
        _ ≤ (ε * D a) * (∏ i ∈ t, B i) +
              B a * (ε * (∑ i ∈ t, D i) * ∏ i ∈ t, B i) := by
          exact add_le_add
            (mul_le_mul (hxy a (mem_insert_self a t)) hprodX (abs_nonneg _)
              (mul_nonneg hε hDa))
            (mul_le_mul (hy a (mem_insert_self a t)) hprodDiff (abs_nonneg _)
              (hBa.trans' zero_le_one))
        _ = ε * (D a + B a * ∑ i ∈ t, D i) * ∏ i ∈ t, B i := by ring
        _ ≤ ε * ((D a + ∑ i ∈ t, D i) * B a) * ∏ i ∈ t, B i := by
          have hmiddle : D a + B a * (∑ i ∈ t, D i) ≤
              (D a + ∑ i ∈ t, D i) * B a := by
            rw [add_mul]
            exact add_le_add hDa_le (by rw [mul_comm])
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmiddle hε) hprodB
        _ = ε * (D a + ∑ i ∈ t, D i) * (B a * ∏ i ∈ t, B i) := by ring

/-- Fintype form of `abs_prod_sub_prod_le`. -/
theorem abs_fintypeProd_sub_fintypeProd_le {ι : Type*} [Fintype ι]
    (x y B D : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hB : ∀ i, 1 ≤ B i)
    (hD : ∀ i, 0 ≤ D i) (hx : ∀ i, |x i| ≤ B i)
    (hy : ∀ i, |y i| ≤ B i) (hxy : ∀ i, |x i - y i| ≤ ε * D i) :
    |(∏ i, x i) - ∏ i, y i| ≤ ε * (∑ i, D i) * ∏ i, B i := by
  classical
  simpa using abs_prod_sub_prod_le Finset.univ x y B D hε
    (fun i _ ↦ hB i) (fun i _ ↦ hD i) (fun i _ ↦ hx i)
    (fun i _ ↦ hy i) (fun i _ ↦ hxy i)

/-! ## Constants for one triangular step -/

/-- A uniform envelope for a previously controlled inverse jet.  The extra `1` makes every
envelope at least one, as required by the finite-product perturbation lemma. -/
noncomputable def jetEnvelope (s K : ℝ) (p : ℕ) : ℝ :=
  1 + |inverseCoeff s p| + K / 2

theorem one_le_jetEnvelope {s K : ℝ} (hK : 0 ≤ K) (p : ℕ) :
    1 ≤ jetEnvelope s K p := by
  unfold jetEnvelope
  have habs := abs_nonneg (inverseCoeff s p)
  have hK2 : 0 ≤ K / 2 := by positivity
  linarith

/-- Perturbation constant for the product of lower-order inverse jets in one partition. -/
noncomputable def productPerturbationConstant (s K : ℝ) {p : ℕ}
    (c : OrderedFinpartition p) : ℝ :=
  (∑ _j : Fin c.length, K) * ∏ j, jetEnvelope s K (c.partSize j)

theorem productPerturbationConstant_nonneg {s K : ℝ} (hK : 0 ≤ K) {p : ℕ}
    (c : OrderedFinpartition p) : 0 ≤ productPerturbationConstant s K c := by
  unfold productPerturbationConstant
  apply mul_nonneg
  · exact Finset.sum_nonneg fun _ _ ↦ hK
  · exact Finset.prod_nonneg fun j _ ↦ (one_le_jetEnvelope hK _).trans' zero_le_one

/-- Perturbation constant for a complete ordered-finpartition monomial. -/
noncomputable def partitionPerturbationConstant (A : ℕ → ℝ) (s K : ℝ) {p : ℕ}
    (c : OrderedFinpartition p) : ℝ :=
  A c.length * ∏ j, jetEnvelope s K (c.partSize j) +
    |forwardCoeff s c.length| * productPerturbationConstant s K c

theorem partitionPerturbationConstant_nonneg {A : ℕ → ℝ} {s K : ℝ}
    (hA : ∀ m, 0 ≤ A m) (hK : 0 ≤ K) {p : ℕ} (c : OrderedFinpartition p) :
    0 ≤ partitionPerturbationConstant A s K c := by
  unfold partitionPerturbationConstant
  have hprod : 0 ≤ ∏ j, jetEnvelope s K (c.partSize j) :=
    Finset.prod_nonneg fun j _ ↦ (one_le_jetEnvelope hK _).trans' zero_le_one
  exact add_nonneg (mul_nonneg (hA _) hprod)
    (mul_nonneg (abs_nonneg _) (productPerturbationConstant_nonneg hK c))

/-- Sum of the monomial perturbation constants over the lower-order remainder. -/
noncomputable def remainderPerturbationConstant (A : ℕ → ℝ) (s K : ℝ) (p : ℕ) : ℝ :=
  ∑ c ∈ remainderPartitions p, partitionPerturbationConstant A s K c

theorem remainderPerturbationConstant_nonneg {A : ℕ → ℝ} {s K : ℝ}
    (hA : ∀ m, 0 ≤ A m) (hK : 0 ≤ K) (p : ℕ) :
    0 ≤ remainderPerturbationConstant A s K p := by
  unfold remainderPerturbationConstant
  exact Finset.sum_nonneg fun c _ ↦ partitionPerturbationConstant_nonneg hA hK c

/-! ## Stability of one partition and one remainder -/

/-- If all inverse jets appearing in a partition are already `Kε`-close to the model, the
whole partition monomial is controlled by `partitionPerturbationConstant`. -/
theorem abs_partitionTerm_sub_model_le {A : ℕ → ℝ} {s K ε : ℝ} {u z : ℕ → ℝ}
    {p : ℕ} (c : OrderedFinpartition p) (hA : 0 ≤ A c.length) (hK : 0 ≤ K)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hu : |u c.length - forwardCoeff s c.length| ≤ ε * A c.length)
    (hz : ∀ j : Fin c.length,
      |z (c.partSize j) - inverseCoeff s (c.partSize j)| ≤ K * ε) :
    |partitionTerm u z c - partitionTerm (forwardCoeff s) (inverseCoeff s) c| ≤
      ε * partitionPerturbationConstant A s K c := by
  have hKε : K * ε ≤ K / 2 := by
    calc
      K * ε ≤ K * (1 / 2) := mul_le_mul_of_nonneg_left hεhalf hK
      _ = K / 2 := by ring
  have hzBound (j : Fin c.length) :
      |z (c.partSize j)| ≤ jetEnvelope s K (c.partSize j) := by
    calc
      |z (c.partSize j)| =
          |(z (c.partSize j) - inverseCoeff s (c.partSize j)) +
            inverseCoeff s (c.partSize j)| := by congr 1; ring
      _ ≤ |z (c.partSize j) - inverseCoeff s (c.partSize j)| +
          |inverseCoeff s (c.partSize j)| := abs_add_le _ _
      _ ≤ K * ε + |inverseCoeff s (c.partSize j)| := by linarith [hz j]
      _ ≤ K / 2 + |inverseCoeff s (c.partSize j)| := by linarith
      _ ≤ jetEnvelope s K (c.partSize j) := by
        unfold jetEnvelope
        linarith
  have hmodelBound (j : Fin c.length) :
      |inverseCoeff s (c.partSize j)| ≤ jetEnvelope s K (c.partSize j) := by
    unfold jetEnvelope
    have := abs_nonneg (inverseCoeff s (c.partSize j))
    have hK2 : 0 ≤ K / 2 := by positivity
    linarith
  have hprodZ : |∏ j, z (c.partSize j)| ≤
      ∏ j, jetEnvelope s K (c.partSize j) := by
    apply abs_prod_le_prod_of_abs_le Finset.univ
    · intro j _
      exact hzBound j
  have hprodDiff : |(∏ j, z (c.partSize j)) -
      ∏ j, inverseCoeff s (c.partSize j)| ≤
      ε * productPerturbationConstant s K c := by
    have h := abs_fintypeProd_sub_fintypeProd_le
      (fun j : Fin c.length ↦ z (c.partSize j))
      (fun j : Fin c.length ↦ inverseCoeff s (c.partSize j))
      (fun j : Fin c.length ↦ jetEnvelope s K (c.partSize j))
      (fun _j : Fin c.length ↦ K) hε0
      (fun j ↦ one_le_jetEnvelope hK (c.partSize j)) (fun _ ↦ hK)
      hzBound hmodelBound (fun j ↦ by simpa [mul_comm] using hz j)
    simpa [productPerturbationConstant, mul_assoc] using h
  calc
    |partitionTerm u z c - partitionTerm (forwardCoeff s) (inverseCoeff s) c| =
        |(u c.length - forwardCoeff s c.length) * (∏ j, z (c.partSize j)) +
          forwardCoeff s c.length *
            ((∏ j, z (c.partSize j)) -
              ∏ j, inverseCoeff s (c.partSize j))| := by
      congr 1
      simp only [partitionTerm]
      ring
    _ ≤ |u c.length - forwardCoeff s c.length| * |∏ j, z (c.partSize j)| +
        |forwardCoeff s c.length| *
          |(∏ j, z (c.partSize j)) -
            ∏ j, inverseCoeff s (c.partSize j)| := by
      simpa only [abs_mul] using
        (abs_add_le
          ((u c.length - forwardCoeff s c.length) * (∏ j, z (c.partSize j)))
          (forwardCoeff s c.length *
            ((∏ j, z (c.partSize j)) -
              ∏ j, inverseCoeff s (c.partSize j))))
    _ ≤ (ε * A c.length) * (∏ j, jetEnvelope s K (c.partSize j)) +
        |forwardCoeff s c.length| * (ε * productPerturbationConstant s K c) := by
      gcongr
    _ = ε * partitionPerturbationConstant A s K c := by
      unfold partitionPerturbationConstant
      ring

/-! ## Uniform finite-order stability -/

/-- **Finite-order quantitative inverse-jet stability.**

Fix positive `s`, a positive lower bound `μ` for the first perturbed forward jet, a
nonnegative coordinatewise perturbation scale `A`, and a finite cutoff `P`.  There is one
constant `K = K(s, μ, A, P)` such that every normalized inverse-jet system whose forward jets
are `ε A_m`-close to the power model through order `P` has inverse jets `Kε`-close to the
inverse-power model through the same order.

The theorem only needs `0 ≤ ε ≤ 1/2`; in particular it also proves exact uniqueness when
`ε = 0`. -/
theorem exists_finite_stability_constant (A : ℕ → ℝ) {s μ : ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hA : ∀ m, 0 ≤ A m) (P : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (u z : ℕ → ℝ),
      0 ≤ ε → ε ≤ 1 / 2 → μ ≤ |u 1| →
      (∀ m : ℕ, 1 ≤ m → m ≤ P →
        |u m - forwardCoeff s m| ≤ ε * A m) →
      (∀ m : ℕ, 1 ≤ m → m ≤ P → normalizedRecurrenceAt u z m) →
      ∀ p : ℕ, 1 ≤ p → p ≤ P → |z p - inverseCoeff s p| ≤ K * ε := by
  induction P with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro ε u z hε0 hεhalf hu1 hu hrec p hp1 hp0
      omega
  | succ P ih =>
      obtain ⟨K₀, hK₀, hstable₀⟩ := ih
      let C : ℝ := remainderPerturbationConstant A s K₀ P
      let T : ℝ := (A 1 * |inverseCoeff s (P + 1)| + C) / μ
      have hC : 0 ≤ C := by
        dsimp [C]
        exact remainderPerturbationConstant_nonneg hA hK₀ P
      have hT : 0 ≤ T := by
        dsimp [T]
        exact div_nonneg
          (add_nonneg (mul_nonneg (hA 1) (abs_nonneg _)) hC) hμ.le
      refine ⟨max K₀ T, hK₀.trans (le_max_left _ _), ?_⟩
      intro ε u z hε0 hεhalf hu1 hu hrec
      have hzPrevious : ∀ p : ℕ, 1 ≤ p → p ≤ P →
          |z p - inverseCoeff s p| ≤ K₀ * ε := by
        apply hstable₀ ε u z hε0 hεhalf hu1
        · intro m hm1 hmP
          exact hu m hm1 (hmP.trans (Nat.le_succ P))
        · intro m hm1 hmP
          exact hrec m hm1 (hmP.trans (Nat.le_succ P))
      have hrem :
          |(∑ c ∈ remainderPartitions P, partitionTerm u z c) -
            ∑ c ∈ remainderPartitions P,
              partitionTerm (forwardCoeff s) (inverseCoeff s) c| ≤ ε * C := by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ c ∈ remainderPartitions P,
              (partitionTerm u z c -
                partitionTerm (forwardCoeff s) (inverseCoeff s) c)| ≤
              ∑ c ∈ remainderPartitions P,
                |partitionTerm u z c -
                  partitionTerm (forwardCoeff s) (inverseCoeff s) c| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ c ∈ remainderPartitions P,
              ε * partitionPerturbationConstant A s K₀ c := by
            apply Finset.sum_le_sum
            intro c hc
            apply abs_partitionTerm_sub_model_le c (hA _) hK₀ hε0 hεhalf
            · have hlen1 : 1 ≤ c.length := c.length_pos (Nat.succ_pos P)
              exact hu c.length hlen1 c.length_le
            · intro j
              exact hzPrevious (c.partSize j) (c.partSize_pos j)
                (Nat.lt_succ_iff.mp (partSize_lt_of_mem_remainderPartitions hc j))
          _ = ε * C := by
            rw [← Finset.mul_sum]
            rfl
      have hrecTop := hrec (P + 1) (Nat.succ_pos P) le_rfl
      have hmodelTop := model_normalizedRecurrenceAt hs (Nat.succ_pos P)
      rw [normalizedRecurrenceAt, sum_partitionTerm_eq_top_add_remainder] at hrecTop hmodelTop
      have heq :
          u 1 * z (P + 1) +
              ∑ c ∈ remainderPartitions P, partitionTerm u z c =
            forwardCoeff s 1 * inverseCoeff s (P + 1) +
              ∑ c ∈ remainderPartitions P,
                partitionTerm (forwardCoeff s) (inverseCoeff s) c :=
        hrecTop.trans hmodelTop.symm
      have halgebra :
          u 1 * (z (P + 1) - inverseCoeff s (P + 1)) =
            (forwardCoeff s 1 - u 1) * inverseCoeff s (P + 1) +
              ((∑ c ∈ remainderPartitions P,
                  partitionTerm (forwardCoeff s) (inverseCoeff s) c) -
                ∑ c ∈ remainderPartitions P, partitionTerm u z c) := by
        linear_combination heq
      have hright :
          |(forwardCoeff s 1 - u 1) * inverseCoeff s (P + 1) +
              ((∑ c ∈ remainderPartitions P,
                  partitionTerm (forwardCoeff s) (inverseCoeff s) c) -
                ∑ c ∈ remainderPartitions P, partitionTerm u z c)| ≤
            ε * (A 1 * |inverseCoeff s (P + 1)| + C) := by
        calc
          _ ≤ |forwardCoeff s 1 - u 1| * |inverseCoeff s (P + 1)| +
              |((∑ c ∈ remainderPartitions P,
                  partitionTerm (forwardCoeff s) (inverseCoeff s) c) -
                ∑ c ∈ remainderPartitions P, partitionTerm u z c)| := by
            simpa only [abs_mul] using
              (abs_add_le
                ((forwardCoeff s 1 - u 1) * inverseCoeff s (P + 1))
                ((∑ c ∈ remainderPartitions P,
                    partitionTerm (forwardCoeff s) (inverseCoeff s) c) -
                  ∑ c ∈ remainderPartitions P, partitionTerm u z c))
          _ ≤ (ε * A 1) * |inverseCoeff s (P + 1)| + ε * C := by
            gcongr
            · simpa [abs_sub_comm] using hu 1 le_rfl (Nat.succ_pos P)
            · simpa [abs_sub_comm] using hrem
          _ = ε * (A 1 * |inverseCoeff s (P + 1)| + C) := by ring
      have hmul : |u 1| * |z (P + 1) - inverseCoeff s (P + 1)| ≤
          ε * (A 1 * |inverseCoeff s (P + 1)| + C) := by
        rw [← abs_mul, halgebra]
        exact hright
      have hμmul : μ * |z (P + 1) - inverseCoeff s (P + 1)| ≤
          ε * (A 1 * |inverseCoeff s (P + 1)| + C) := by
        exact (mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)).trans hmul
      have htop : |z (P + 1) - inverseCoeff s (P + 1)| ≤ T * ε := by
        dsimp [T]
        rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
        simpa [mul_comm] using hμmul
      intro p hp1 hpTop
      rcases lt_or_eq_of_le hpTop with hp | rfl
      · have hpP : p ≤ P := Nat.lt_succ_iff.mp hp
        exact (hzPrevious p hp1 hpP).trans
          (mul_le_mul_of_nonneg_right (le_max_left K₀ T) hε0)
      · exact htop.trans (mul_le_mul_of_nonneg_right (le_max_right K₀ T) hε0)

end InverseJet

end LeanProofs.IntegerPoints
