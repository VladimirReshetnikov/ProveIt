import OAI.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
import OAI.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
import OAI.Combinatorics.Progressions.Estimates.MultidegreeIntegralModel

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

theorem exists_bounded_integral_model_with_frequency
    {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (e : Basis (Fin d) ℚ L)
    (b : ∀ a, Basis (Fin (finrank ℚ (F.layer a))) ℚ (F.layer a))
    {H : ℕ} (hb : ∀ a i j, RationalHeightLE (e.repr ((b a) i).val j) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (ξ : L →ₗ[ℚ] ℚ) (hξ : ∀ i, RationalHeightLE (ξ (e i)) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * (l * H ^ d) ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ M : D.MultidegreeStructure bound,
        M.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        (∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → M.ComplexityLE p := by
  classical
  let k := arrayDenominator (fun i => ξ (e i))
  have hk : 0 < k := arrayDenominator_pos _
  have hkH : k ≤ H ^ d := by
    simpa only [Fintype.card_fin] using arrayDenominator_le (fun i => ξ (e i)) (fun i => (hξ i).2)
  obtain ⟨B, hB, hdiv, hbound, D, M, hMF, hDe, hDB, hcoords, hcomplex⟩ :=
    F.exists_bounded_integral_model e b hb hc (l * k) (Nat.mul_pos hl hk)
  refine ⟨B, hB, (dvd_mul_right l k).trans hdiv,
    hbound.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left l hkH)),
    D, M, hMF, hDe, hDB, hcoords, ?_, hcomplex⟩
  intro z hz
  have hgrid : D.basis.equivFun z.coord ∈ scaledIntegerGrid B := by
    rw [← hcoords]
    change (⟨D.basis.equivFun.symm (D.basis.equivFun z.coord)⟩ : D.filtration.Group) ∈ D.lattice
    simpa only [LinearEquiv.symm_apply_apply] using hz
  rw [hDe] at hgrid
  apply coordinateGrid_functional_integral e ξ k B ((dvd_mul_left k l).trans hdiv)
    (fun i => ⟨clearedArray (fun j => ξ (e j)) i, (clearedArray_cast _ i).symm⟩) hgrid

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

theorem markedPolynomialValueHeight_le_exp (s n T K A : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hT : (T : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hA : (A : ℝ) ≤ Real.exp p) :
    ((A ^ s * ((n + 1) * (T * K) ^ n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hpower : ((A ^ s : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ s := pow_le_pow_left₀ (Nat.cast_nonneg _) hA _
      _ = Real.exp ((s : ℝ) * p) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hs, hp, sq_nonneg p])
  have hproduct : ((T * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hT hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hp, sq_nonneg p])
  have hsum := rational_sum_cost_le_exp n (T * K) hp 2 1 hproduct
    (by simpa only [pow_one] using hn.trans (by linarith only [hp] : p ≤ p + 2))
  rw [Nat.cast_mul]
  calc
    _ ≤ Real.exp ((p + 2) ^ 2) * Real.exp ((p + 2) ^ 4) :=
      mul_le_mul hpower hsum (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((p + 2) ^ 2 + (p + 2) ^ 4) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ 4 :=
        pow_le_pow_right₀ (by linarith only [hp]) (by decide)
      calc
        _ ≤ 2 * (p + 2) ^ 4 := by linarith only [hpow]
        _ ≤ (p + 2) * (p + 2) ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith only [hp]) (by positivity)
        _ = (p + 2) ^ 5 := by ring

theorem markedQuotientFrequencyHeight_le_exp (s n a d m u H K A : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hs : (s + 1 : ℕ) ≤ p)
    (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ p) (hu : (u : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hA : (A : ℝ) ≤ Real.exp p) :
    (markedQuotientFrequencyHeight s n a d m u H K A : ℝ) ≤
      Real.exp ((p + 2) ^ ((5082 * s + 3566) * 8)) := by
  let g := 5082 * s + 3564
  let R := (p + 2) ^ g
  let T := lieTreeHeight n H s
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let Q := rationalKernelHeight m B
  let E := (d + 1) * (B * Q) ^ d
  let V := A ^ s * ((n + 1) * (T * K) ^ n)
  have hpR : p ≤ R := le_power_budget hp (by dsimp [g]; omega)
  have hR : 0 ≤ R := hp.trans hpR
  have hE : (E : ℝ) ≤ Real.exp R := by
    have he : E ≤ markedQuotientHeight s n a d m 0 H := Nat.le_max_right _ _
    exact (Nat.cast_le.mpr he).trans
      (markedQuotientHeight_le_exp s n a d m 0 H hp hs hn ha hd hm (by simpa using hp) hH)
  let z := 6 * s + 2
  let S := (p + 2) ^ z
  have hpS : p ≤ S := le_power_budget hp (by dsimp [z]; omega)
  have hS : 0 ≤ S := hp.trans hpS
  have hsS : (s : ℝ) ≤ S := by
    have hss : (s : ℝ) ≤ (s + 1 : ℕ) := by exact_mod_cast Nat.le_succ s
    exact hss.trans (hs.trans hpS)
  have hV₀ := markedPolynomialValueHeight_le_exp s n T K A hS hsS (hn.trans hpS)
    (lieTreeHeight_le_exp n H s hp hn hH)
    (hK.trans (Real.exp_le_exp.mpr hpS)) (hA.trans (Real.exp_le_exp.mpr hpS))
  have hV : (V : ℝ) ≤ Real.exp R := by
    have hb := exponential_budget_comp hp hS z 5 le_rfl hV₀
    apply hb.trans (Real.exp_le_exp.mpr ?_)
    exact pow_le_pow_right₀ (by linarith only [hp]) (by dsimp [g, z]; omega)
  have hfreq := embedding_coordinate_height_budget u u E V hR (hu.trans hpR) (hu.trans hpR) hE hV
  have hout := exponential_budget_comp hp hR g 8 le_rfl hfreq
  exact hout

theorem markedQuotientJointHeight_le_exp (s n a d m q u H K A : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hs : (s + 1 : ℕ) ≤ p)
    (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p) (hu : (u : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hA : (A : ℝ) ≤ Real.exp p) :
    ((max (markedQuotientHeight s n a d m q H)
      (markedQuotientFrequencyHeight s n a d m u H K A) : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ ((5082 * s + 3566) * 8)) := by
  rw [Nat.cast_max]
  apply max_le
  · apply (markedQuotientHeight_le_exp s n a d m q H hp hs hn ha hd hm hq hH).trans
      (Real.exp_le_exp.mpr ?_)
    exact pow_le_pow_right₀ (by linarith only [hp]) (by omega)
  · exact markedQuotientFrequencyHeight_le_exp s n a d m u H K A hp hs hn ha hd hm hu hH hK hA

end Erdos3

end

section

namespace Erdos3

open Module

def markedQuotientJointHeight (s n a d m q u H K A : ℕ) : ℕ :=
  max (markedQuotientHeight s n a d m q H) (markedQuotientFrequencyHeight s n a d m u H K A)

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_integral_frequency_model (t : ℕ)
    (η : L →ₗ[ℚ] ℚ) {K A : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) K)
    (x : Fin t → ℚ) (hA : 1 ≤ A) (hx : ∀ i, RationalHeightLE (x i) A)
    (d₀ k₀ l₀ : ℕ)
    (hann : markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀ ⊓
      (markedShiftSecondIdeal F v w marked t).toSubmodule ≤
        (η.comp (markedShiftEval F v w marked t x)).ker)
    (l : ℕ) (hl : 0 < l) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ u : ℕ, u ≤ q ∧ ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
        B ≤ bchIntegralDenominatorBound (s + 1) *
          markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A ^ (q ^ 3) *
            (l * markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A ^ q) ∧
        ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
          ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
            ∃ ξ : MarkedShiftQuotient F v w marked t →ₗ[ℚ] ℚ,
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧ D.grid = B ∧
              bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
              (∀ i, RationalHeightLE (ξ (D.basis i))
                (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A)) ∧
              (∀ z ∈ markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀,
                ξ (lieQuotientMap (markedShiftSecondIdeal F v w marked t) z) =
                  η (markedShiftEval F v w marked t x z)) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
              ∀ p : ℝ, (q : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p →
                (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A : ℝ) ≤ Real.exp p →
                  M.ComplexityLE p := by
  classical
  obtain ⟨m, hm, q, hq, u, hu, f, hstructure, hlayers, ξ, hξ, hheight⟩ :=
    exists_markedShiftQuotient_bounded_frequency_data F b ω hF hω v w marked hw hv hH hc hgen
      t η hη x hA hx d₀ k₀ l₀ hann
  let J := markedQuotientJointHeight s (Fintype.card ι)
    (finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t))
    (finrank ℚ (markedShiftSubalgebra F v w marked t)) m q u H K A
  choose c hc' using hlayers
  have hcJ (α i j) : RationalHeightLE (f.repr ((c α) i).val j) J :=
    (hc' α i j).mono (Nat.le_max_left _ _)
  have hξJ (i) : RationalHeightLE (ξ (f i)) J := (hheight i).mono (Nat.le_max_right _ _)
  let M₀ := markedShiftMultidegree F v w marked hw hv t
  obtain ⟨B, hB, hdiv, hbound, D, M, hMF, hDf, hDB, hcoords, hintegral, hcomplex⟩ :=
    M₀.exists_bounded_integral_model_with_frequency f c hcJ
      (fun i j k => (hstructure i j k).mono (Nat.le_max_left _ _)) ξ hξJ l hl
  refine ⟨m, hm, q, hq, u, hu, B, hB, hdiv, hbound, D, M, ξ,
    hMF, hDB, hcoords, ?_, hξ, hintegral, hcomplex⟩
  simpa only [hDf] using hξJ

end Erdos3

end

section

namespace Erdos3

theorem integral_frequency_grid_allowance_le_exp (K d H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((K * H ^ (d ^ 3) * (l * H ^ d) : ℕ) : ℝ) ≤
      Real.exp (((p + 2) ^ 2 + (K + 5 : ℕ)) ^ (K + 5)) := by
  have hpQ : p ≤ (p + 2) ^ 2 := le_power_budget hp (by decide)
  have hlQ : ((l * H ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ Real.exp p * Real.exp p ^ d :=
        mul_le_mul hl (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (p + (d : ℝ) * p) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hp, hd, sq_nonneg p])
  exact integral_grid_allowance_le_exp K d H (l * H ^ d) (hp.trans hpQ) (hd.trans hpQ)
    (hH.trans (Real.exp_le_exp.mpr hpQ)) hlQ

noncomputable def markedFrequencyHeightBudget (s : ℕ) (p : ℝ) : ℝ :=
  (markedShiftInputBudget s p + 2) ^ ((5082 * s + 3566) * 8)

noncomputable def markedFrequencyModelBudget (s : ℕ) (p : ℝ) : ℝ :=
  markedFrequencyHeightBudget s p +
    ((markedFrequencyHeightBudget s p + 2) ^ 2 + (bchIntegralDenominatorBound (s + 1) + 5 : ℕ)) ^
      (bchIntegralDenominatorBound (s + 1) + 5)

theorem markedShiftInputBudget_le_frequencyHeight (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedShiftInputBudget s p ≤ markedFrequencyHeightBudget s p :=
  le_power_budget (markedShiftInputBudget_nonneg s hp) (by omega)

theorem markedFrequencyHeightBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ markedFrequencyHeightBudget s p :=
  (markedShiftInputBudget_nonneg s hp).trans (markedShiftInputBudget_le_frequencyHeight s hp)

theorem markedFrequencyHeightBudget_le_model (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedFrequencyHeightBudget s p ≤ markedFrequencyModelBudget s p := by
  have hQ := markedFrequencyHeightBudget_nonneg s hp
  exact le_add_of_nonneg_right (by positivity)

theorem exists_markedFrequencyModel_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → markedFrequencyModelBudget s p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X * Polynomial.C (s + 1) * (Polynomial.X + 1) ^ s +
    Polynomial.X + Polynomial.C (s + 1)
  let U : Polynomial ℕ := (Q + 2) ^ ((5082 * s + 3566) * 8)
  let K := bchIntegralDenominatorBound (s + 1) + 5
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget (U + ((U + 2) ^ 2 + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa only [markedFrequencyModelBudget, markedFrequencyHeightBudget, markedShiftInputBudget,
    Q, U, K, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom] using h p hp

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_frequency_model_with_budget (t : ℕ)
    (η : L →ₗ[ℚ] ℚ) {K A : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) K)
    (x : Fin t → ℚ) (hA : 1 ≤ A) (hx : ∀ i, RationalHeightLE (x i) A)
    (d₀ k₀ l₀ : ℕ)
    (hann : markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀ ⊓
      (markedShiftSecondIdeal F v w marked t).toSubmodule ≤
        (η.comp (markedShiftEval F v w marked t x)).ker)
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card ι : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p)
    (hAp : (A : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
      ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
        ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
          ∃ ξ : MarkedShiftQuotient F v w marked t →ₗ[ℚ] ℚ,
            M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
            M.ComplexityLE (markedFrequencyModelBudget s p) ∧ l ∣ D.grid ∧
            bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
            (∀ i, rationalLogHeight (ξ (D.basis i)) ≤ markedFrequencyModelBudget s p) ∧
            (∀ z ∈ markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀,
              ξ (lieQuotientMap (markedShiftSecondIdeal F v w marked t) z) =
                η (markedShiftEval F v w marked t x z)) ∧
            ∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  have ha : a ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t :=
    F.associatedDegree.polynomialShift_finrank_le b ω hF hω t
  have hd : d ≤ a := (markedShiftSubalgebra F v w marked t).toSubmodule.finrank_le
  have hi : finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ≤ d :=
    (markedShiftSecondIdeal F v w marked t).toSubmodule.finrank_le
  let R := markedShiftInputBudget s p
  let Q := markedFrequencyHeightBudget s p
  have hpR : p ≤ R := le_markedShiftInputBudget s hp
  have hR : 0 ≤ R := markedShiftInputBudget_nonneg s hp
  have hRQ : R ≤ Q := markedShiftInputBudget_le_frequencyHeight s hp
  have hQS : Q ≤ markedFrequencyModelBudget s p := markedFrequencyHeightBudget_le_model s hp
  have haR : (a : ℝ) ≤ R := (Nat.cast_le.mpr ha).trans
    (markedShift_dimension_budget s (Fintype.card ι) t hp hn ht)
  have hdR : (d : ℝ) ≤ R := (Nat.cast_le.mpr hd).trans haR
  obtain ⟨m, hm, q, hq, u, hu, B, hB, hdiv, hbound, D, M, ξ,
      hMF, hgrid, hcoords, hfreq, hpreserve, hintegral, hcomplex⟩ :=
    exists_markedShift_integral_frequency_model F b ω hF hω v w marked hw hv hH hc hgen
      t η hη x hA hx d₀ k₀ l₀ hann l hl
  have hmR : (m : ℝ) ≤ R := (Nat.cast_le.mpr (hm.trans hi)).trans hdR
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq).trans hdR
  have huR : (u : ℝ) ≤ R := (Nat.cast_le.mpr hu).trans hqR
  have hheight : (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A : ℝ) ≤ Real.exp Q :=
    markedQuotientJointHeight_le_exp s (Fintype.card ι) a d m q u H K A hR
      (step_le_markedShiftInputBudget s hp) (hn.trans hpR) haR hdR hmR hqR huR
      (hHp.trans (Real.exp_le_exp.mpr hpR)) (hKp.trans (Real.exp_le_exp.mpr hpR))
      (hAp.trans (Real.exp_le_exp.mpr hpR))
  have hgridS : (B : ℝ) ≤ Real.exp (markedFrequencyModelBudget s p) := by
    have hb := integral_frequency_grid_allowance_le_exp (bchIntegralDenominatorBound (s + 1)) q
      (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A) l
      (hR.trans hRQ) (hqR.trans hRQ) hheight
      (hlp.trans (Real.exp_le_exp.mpr (hpR.trans hRQ)))
    exact (Nat.cast_le.mpr hbound).trans (hb.trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hR.trans hRQ))))
  refine ⟨q, hq.trans (hd.trans ha), D, M, ξ, hMF,
    hcomplex _ (hqR.trans (hRQ.trans hQS)) hgridS
      (hheight.trans (Real.exp_le_exp.mpr hQS)), ?_, ?_, ?_, hpreserve, hintegral⟩
  · rw [hgrid]
    exact hdiv
  · simpa only [hgrid] using hcoords
  · exact fun i => (rationalLogHeight_le_of_height (hfreq i) hheight).trans hQS

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_marked_common_frequency_model (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M) (t : ℕ) (x : Fin t → ℚ) (l : ℕ),
      0 ≤ M → b ≤ M → (t : ℝ) ≤ M → (∀ i, rationalLogHeight (x i) ≤ M) →
      0 < l → (l : ℝ) ≤ Real.exp M →
      ∃ d : ℕ,
        ∃ E : RationalFilteredNilmanifold
          (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
          ∃ T : E.MultidegreeStructure (mixedCorrelationDegree s),
            ∃ ξ : MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] ℚ,
              T.filtration = D.markedQuotientMultidegree t ∧
              T.ComplexityLE ((M + C) ^ C) ∧ l ∣ E.grid ∧
              bchSubgroupCoordinates E.basis E.lattice = scaledIntegerGrid E.grid ∧
              (∀ i, rationalLogHeight (ξ (E.basis i)) ≤ (M + C) ^ C) ∧
              (∀ z ∈ markedShiftPolynomialSubmodule D.coefficientFreeFiltration D.coefficientFreeGenerator
                  D.coefficientWeight D.coefficientIsDependent t s 1 r,
                ξ (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
                    D.coefficientWeight D.coefficientIsDependent t) z) =
                  B.freeFrequency D (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                    D.coefficientWeight D.coefficientIsDependent t x z)) ∧
              ∀ z : E.filtration.Group, z ∈ E.lattice → ∃ n : ℤ, ξ z.coord = n := by
  obtain ⟨a, _, hsource⟩ := exists_common_marked_source_basis s hs
  obtain ⟨c, _, hmodel⟩ := exists_markedFrequencyModel_budget s
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B t x l hM hbM ht hx hl hlM
  let U := (M + a) ^ a
  let V := M + U + 1
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hMV : M ≤ V := by dsimp [V]; linarith only [hU]
  have hUV : U ≤ V := by dsimp [V]; linarith only [hM]
  have hU1V : U + 1 ≤ V := by dsimp [V]; linarith only [hM]
  have hM1V : M + 1 ≤ V := by dsimp [V]; linarith only [hU]
  have hV : 0 ≤ V := hM.trans hMV
  have hbound : markedFrequencyModelBudget s V ≤ (M + C) ^ C := by
    apply (hmodel V hV).trans
    simpa [Q, U, V, Polynomial.eval₂_pow] using hbudget M hM
  obtain ⟨e, ω, hF, hω, hdim, hstructure, hgen, hfreq⟩ := hsource D B hM hbM
  obtain ⟨d, _, E, T, ξ, hTF, hT, hdiv, hcoords, hξ, hpreserve, hintegral⟩ :=
    exists_markedShift_frequency_model_with_budget D.coefficientFreeFiltration e ω hF hω
      D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer (one_le_ceil_exp U)
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (fun z i => rationalHeightLE_ceil_exp (hgen z i)) t (B.freeFrequency D)
      (fun i => rationalHeightLE_ceil_exp (hfreq i)) x (one_le_ceil_exp M)
      (fun i => rationalHeightLE_ceil_exp (hx i)) s 1 r (B.markedShift_top_inter_le_ker D t x)
      l hl hV (by simpa only [Fintype.card_fin] using hdim.trans hUV) (ht.trans hMV)
      ((ceil_exp_le_exp_add_one hU).trans (Real.exp_le_exp.mpr hU1V))
      ((ceil_exp_le_exp_add_one hU).trans (Real.exp_le_exp.mpr hU1V))
      ((ceil_exp_le_exp_add_one hM).trans (Real.exp_le_exp.mpr hM1V))
      (hlM.trans (Real.exp_le_exp.mpr hMV))
  exact ⟨d, E, T, ξ, hTF, hT.mono T hbound, hdiv, hcoords,
    fun i => (hξ i).trans hbound, hpreserve, hintegral⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
