import OAI.Combinatorics.Progressions.Sampling.RationalForecastCoefficientPeriod

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

local instance characterOrderNeZero (N : ℕ) [NeZero N]
    (χ : AddChar (J → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

omit [Fintype I] [DecidableEq I] in

theorem integerLongPolynomial_characteristic_residue_representative
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) (v : I → ℤ) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly v N t j : ZMod N)) χ =
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly
        (fun i => (((v i : ZMod (orderOf χ)).val : ℕ) : ℤ)) N t j : ZMod N)) χ := by
  apply integerLongPolynomial_characteristic_inactive_congr
  intro i
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem integerLongPolynomial_characteristic_inactive_split
    {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (v : Ω → I → ℤ) (poly : J → MvPolynomial (A ⊕ I) ℤ)
    (N : ℕ) [NeZero N] (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) (z : Z) :
    inactive.complexMean (fun i => if gridPoint i = z then
      finiteImageCharacteristic p
        (fun t j => (integerLongPolynomialOutput poly (v i) N t j : ZMod N)) χ else 0) =
    ∑ r : I → ZMod (orderOf χ),
      (inactive.fiberMean (fun i j => (v i j : ZMod (orderOf χ))) r
        (fun i => if gridPoint i = z then 1 else 0) : ℂ) *
      finiteImageCharacteristic p
        (fun t j => (integerLongPolynomialOutput poly
          (fun i => ((r i).val : ℤ)) N t j : ZMod N)) χ := by
  let : NeZero (orderOf χ) := ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩
  have h := inactive.complexMean_fiber_factor
    (fun i j => (v i j : ZMod (orderOf χ)))
    (fun i => if gridPoint i = z then 1 else 0)
    (fun r => finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly
        (fun i => ((r i).val : ℤ)) N t j : ZMod N)) χ)
  rw [← h]
  congr 1
  funext i
  by_cases hi : gridPoint i = z
  · simp only [hi, ite_true, Complex.ofReal_one, one_mul]
    exact integerLongPolynomial_characteristic_residue_representative poly N p χ (v i)
  · simp only [hi, ite_false, Complex.ofReal_zero, zero_mul]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem inactiveResidueCoefficient_mass_le
    {Ω Z R : Type*} [Fintype Ω] [Fintype R]
    (p : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z) (residue : Ω → R)
    (a : R → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1) (z : Z) :
    (∑ r, ‖(p.fiberMean residue r (fun i => if gridPoint i = z then 1 else 0) : ℂ) * a r‖) ≤
      p.fiberMean gridPoint z (fun _ => 1) := by
  have hnonneg (r : R) :
      0 ≤ p.fiberMean residue r (fun i => if gridPoint i = z then 1 else 0) :=
    p.fiberMean_nonneg residue r _ (fun _ => by split_ifs <;> norm_num)
  calc
    _ ≤ ∑ r, p.fiberMean residue r (fun i => if gridPoint i = z then 1 else 0) := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnonneg r)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha r) (hnonneg r)
    _ = _ := p.sum_fiberMean residue _

theorem rationalInactiveResidueCoefficient_mass_le
    {Ω A I J Z : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z) (v : Ω → I → ℤ)
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (N q : ℕ) [NeZero N] [NeZero q]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ) (z : Z) :
    (∑ r : I → ZMod q,
      ‖(inactive.fiberMean (fun i j => (v i j : ZMod q)) r
        (fun i => if gridPoint i = z then 1 else 0) : ℂ) *
      finiteImageCharacteristic p
        (fun t j => (integerLongPolynomialOutput poly (fun i => ((r i).val : ℤ)) N t j : ZMod N)) χ‖)
      ≤ inactive.fiberMean gridPoint z (fun _ => 1) := by
  apply inactiveResidueCoefficient_mass_le
  intro r
  exact finiteImageCharacteristic_norm_le_one p _ χ

theorem rationalForecast_order_residue_term_count
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (N : ℕ) [NeZero N] (T : ℕ) :
    (∑ χ ∈ Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T),
      (orderOf χ) ^ Fintype.card I) ≤ T ^ (Fintype.card J + Fintype.card I + 1) := by
  let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
  have hcount : S.card ≤ T ^ (Fintype.card J + 1) :=
    finiteCharacter_boundedOrder_card_le (integerResidueTuple N)
      (integerResidueTuple_surjective N) T
  calc
    _ ≤ ∑ _χ ∈ S, T ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact Nat.pow_le_pow_left (Finset.mem_filter.mp hχ).2 _
    _ = S.card * T ^ Fintype.card I := by simp
    _ ≤ T ^ (Fintype.card J + 1) * T ^ Fintype.card I :=
      Nat.mul_le_mul_right _ hcount
    _ = _ := by rw [← pow_add]; congr 1; omega

end Erdos3

end

end OAI
