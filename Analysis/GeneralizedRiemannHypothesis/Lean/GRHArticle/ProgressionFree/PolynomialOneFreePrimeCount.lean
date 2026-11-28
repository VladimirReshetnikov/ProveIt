import GRHArticle.ProgressionFree.PolynomialOneFreePrimeFibers
import GRHArticle.ProgressionFree.PolynomialRoughWeightLimit

/-!
# Degree-ball counting with one free prime

The exact count is a finite sum over the cofactor and its remaining
degree budget. The Roth number bounds each exponent fiber.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The possible exponents up to a fixed remaining degree budget. -/
noncomputable def oneFreePrimeExponentPrefix (H : F[X] → Set ℕ) (g : F[X]) (t : ℕ) :
    Finset ℕ := (Finset.range (t+1)).filter (· ∈ H g)

private noncomputable def oneFreePrimeDegreeParameters
    (P : F[X]) (H : F[X] → Set ℕ) (N : ℕ) : Finset (Σ _ : ℕ, Σ _ : F[X], F × ℕ) :=
  (Finset.range (N+1)).sigma fun t ↦ (oneFreePrimeCofactorLayer P (N-t)).sigma fun g ↦
    (Finset.univ.erase 0) ×ˢ oneFreePrimeExponentPrefix H g t

private theorem mem_oneFreePrimeDegreeParameters
    {P : F[X]} {H : F[X] → Set ℕ} {N t : ℕ} {g : F[X]} {a : F} {e : ℕ} :
    (⟨t, g, a, e⟩ : Σ _ : ℕ, Σ _ : F[X], F × ℕ) ∈ oneFreePrimeDegreeParameters P H N ↔
      t ≤ N ∧ g ∈ oneFreePrimeCofactorLayer P (N-t) ∧ a ≠ 0 ∧ e ≤ t ∧ e ∈ H g := by
  simp [oneFreePrimeDegreeParameters, oneFreePrimeExponentPrefix]

/-- Exact finite count by nonzero scalar, monic cofactor, and exponent. -/
theorem card_polynomialDegreeLTFinset_oneFreePrimeFamily
    {P : F[X]} (hPm : P.Monic) (hPi : Irreducible P) (hP : P.natDegree = 1)
    (H : F[X] → Set ℕ) (N : ℕ) :
    ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ oneFreePrimeFamily P H)).card =
      (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
        ∑ g ∈ oneFreePrimeCofactorLayer P (N-t), (oneFreePrimeExponentPrefix H g t).card := by
  let D := oneFreePrimeDegreeParameters P H N
  let B := (polynomialDegreeLTFinset F (N+1)).filter (· ∈ oneFreePrimeFamily P H)
  have hD : D.card = B.card := by
    apply Finset.card_bij (fun a _ ↦ C a.2.2.1 * a.2.1 * P^a.2.2.2)
    · rintro ⟨t, g, a, e⟩ hp
      obtain ⟨ht, hg, ha, he, heH⟩ := mem_oneFreePrimeDegreeParameters.mp hp
      obtain ⟨hgd, hg⟩ := mem_oneFreePrimeCofactorLayer.mp hg
      let f := C a * g * P^e
      have hf : f ≠ 0 :=
        mul_ne_zero (mul_ne_zero (C_ne_zero.mpr ha) hg.1.ne_zero) (pow_ne_zero _ hPi.ne_zero)
      have hg' : oneFreePrimeCofactor P f = g :=
        oneFreePrimeCofactor_scalar_mul_cofactor_mul_pow hPm hPi hg.1 hg.2.1 ha e
      have he' : polynomialPrimeExponent P f = e :=
        polynomialPrimeExponent_scalar_mul_cofactor_mul_pow hPm hPi hg.1 hg.2.1 ha e
      have hfN := natDegree_eq_oneFreePrimeCofactor_add_exponent hP hf
      rw [hg', he', hgd] at hfN
      refine Finset.mem_filter.mpr ⟨mem_polynomialDegreeLTFinset.mpr ?_, ?_⟩
      · rw [degree_eq_natDegree hf, Nat.cast_lt, Nat.lt_succ_iff]
        omega
      · change f ≠ 0 ∧ OneFreePrimeAdmissibleCofactor P (oneFreePrimeCofactor P f) ∧
          polynomialPrimeExponent P f ∈ H (oneFreePrimeCofactor P f)
        rw [hg', he']
        exact ⟨hf,hg,heH⟩
    · rintro ⟨t, g, a, e⟩ hp ⟨t', g', a', e'⟩ hp' heq
      obtain ⟨ht, hg, ha, _, _⟩ := mem_oneFreePrimeDegreeParameters.mp hp
      obtain ⟨ht', hg', ha', _, _⟩ := mem_oneFreePrimeDegreeParameters.mp hp'
      obtain ⟨hgd, hg⟩ := mem_oneFreePrimeCofactorLayer.mp hg
      obtain ⟨hgd', hg'⟩ := mem_oneFreePrimeCofactorLayer.mp hg'
      have hG := congrArg (oneFreePrimeCofactor P) heq
      have hE := congrArg (polynomialPrimeExponent P) heq
      have hA := congrArg leadingCoeff heq
      simp only [oneFreePrimeCofactor_scalar_mul_cofactor_mul_pow hPm hPi hg.1 hg.2.1 ha,
        oneFreePrimeCofactor_scalar_mul_cofactor_mul_pow hPm hPi hg'.1 hg'.2.1 ha'] at hG
      simp only [polynomialPrimeExponent_scalar_mul_cofactor_mul_pow hPm hPi hg.1 hg.2.1 ha,
        polynomialPrimeExponent_scalar_mul_cofactor_mul_pow hPm hPi hg'.1 hg'.2.1 ha'] at hE
      rw [mul_assoc, mul_assoc, (hg.1.mul (hPm.pow e)).leadingCoeff_C_mul,
        (hg'.1.mul (hPm.pow e')).leadingCoeff_C_mul] at hA
      change a = a' at hA
      have hT : t = t' := by rw [hG] at hgd; omega
      subst t'
      subst g'
      subst a'
      subst e'
      rfl
    · intro f hf
      obtain ⟨hfN, hfE⟩ := Finset.mem_filter.mp hf
      obtain ⟨hf₀, hg, he⟩ := hfE
      have hdf := mem_polynomialDegreeLTFinset.mp hfN
      rw [degree_eq_natDegree hf₀, Nat.cast_lt, Nat.lt_succ_iff] at hdf
      let g := oneFreePrimeCofactor P f
      let t := N - g.natDegree
      have hd : f.natDegree = g.natDegree + polynomialPrimeExponent P f :=
        natDegree_eq_oneFreePrimeCofactor_add_exponent hP hf₀
      have hgd : g.natDegree = N-t := by dsimp [t]; omega
      refine ⟨⟨t,g,f.leadingCoeff,polynomialPrimeExponent P f⟩, ?_, ?_⟩
      · exact mem_oneFreePrimeDegreeParameters.mpr
          ⟨Nat.sub_le _ _, mem_oneFreePrimeCofactorLayer.mpr ⟨hgd,hg⟩,
            leadingCoeff_ne_zero.mpr hf₀, by dsimp [t]; omega, he⟩
      · exact polynomial_eq_scalar_mul_oneFreePrimeCofactor_mul_pow P f
  rw [← hD]
  simp [D, oneFreePrimeDegreeParameters, Finset.card_sigma, Finset.card_product, Finset.mul_sum]

/-- The uniformly optimized finite cofactor bound. -/
theorem card_polynomialDegreeLTFinset_oneFreePrimeFamily_le
    {P : F[X]} (hPm : P.Monic) (hPi : Irreducible P) (hP : P.natDegree = 1)
    {H : F[X] → Set ℕ} (hH : ∀ g, ThreeAPFree (H g)) (N : ℕ) :
    ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ oneFreePrimeFamily P H)).card ≤
      (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
        (oneFreePrimeCofactorLayer P (N-t)).card * rothNumberNat (t+1) := by
  rw [card_polynomialDegreeLTFinset_oneFreePrimeFamily hPm hPi hP]
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum
  intro t ht
  calc
    _ ≤ ∑ _g ∈ oneFreePrimeCofactorLayer P (N-t), rothNumberNat (t+1) := by
      apply Finset.sum_le_sum
      intro g _
      have hs (e : ℕ) (he : e ∈ oneFreePrimeExponentPrefix H g t) : e ∈ H g :=
        (Finset.mem_filter.mp he).2
      exact ((hH g).mono hs).le_rothNumberNat _
        (fun _ he ↦ Finset.mem_range.mp (Finset.mem_filter.mp he).1) rfl
    _ = _ := by simp

/-- The exact finite count normalized by the degree-ball volume. -/
theorem polynomialBallProportion_oneFreePrimeFamily
    {P : F[X]} (hPm : P.Monic) (hPi : Irreducible P) (hP : P.natDegree = 1)
    (H : F[X] → Set ℕ) (N : ℕ) :
    polynomialBallProportion (oneFreePrimeFamily P H) N =
      let q := (Fintype.card F : ℝ)
      (1-q⁻¹) * ∑ t ∈ Finset.range (N+1),
        (((∑ g ∈ oneFreePrimeCofactorLayer P (N-t), (oneFreePrimeExponentPrefix H g t).card : ℕ) : ℝ) /
          q^(N-t)) * q⁻¹^t := by
  let r (n : ℕ) := ∑ g ∈ oneFreePrimeCofactorLayer P n,
    (oneFreePrimeExponentPrefix H g (N-n)).card
  have hr (t : ℕ) (ht : t ∈ Finset.range (N+1)) :
      r (N-t) = ∑ g ∈ oneFreePrimeCofactorLayer P (N-t), (oneFreePrimeExponentPrefix H g t).card := by
    have h := Finset.mem_range.mp ht
    simp [r, show N-(N-t)=t by omega]
  have hb : (∑ t ∈ Finset.range (N+1), r (N-t)*(fun _ : ℕ ↦ 1) t) =
      ∑ t ∈ Finset.range (N+1), ∑ g ∈ oneFreePrimeCofactorLayer P (N-t),
        (oneFreePrimeExponentPrefix H g t).card := by
    simp only [mul_one]
    exact Finset.sum_congr rfl hr
  unfold polynomialBallProportion
  rw [card_polynomialDegreeLTFinset_oneFreePrimeFamily hPm hPi hP, ← hb,
    polynomial_weighted_convolution_scale]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [hr t ht]

end GRHArticle.ProgressionFree
