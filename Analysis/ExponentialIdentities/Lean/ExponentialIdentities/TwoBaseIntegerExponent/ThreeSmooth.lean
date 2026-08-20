import ExponentialIdentities.IntegerExponent

/-!
# A three-base form of the integral exponent theorem

The determinant argument for the bases `2`, `3`, and `5` only uses unique
factorization to prove that its row parameters are distinct.  This file keeps
that condition abstract, and then supplies it whenever the third base has a
prime divisor other than `2` and `3`.
-/

open scoped BigOperators Nat

namespace Nat

/-- A positive natural number has no prime factors other than `2` and `3` iff
it is the product of a power of `2` and a power of `3`. -/
theorem prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow
    {a : ℕ} (ha : 0 < a) :
    (∀ p : ℕ, p.Prime → p ∣ a → p = 2 ∨ p = 3) ↔
      ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by
  constructor
  · intro h
    let u := a.factorization 2
    let v := a.factorization 3
    refine ⟨u, v, ?_⟩
    apply Nat.eq_of_factorization_eq ha.ne'
      (mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)))
    intro p
    rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (pow_ne_zero _ (by decide)),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3)]
    by_cases hp2 : p = 2
    · subst p
      simp [u]
    by_cases hp3 : p = 3
    · subst p
      simp [v]
    have hap : a.factorization p = 0 := by
      by_contra hne
      have hmem : p ∈ a.primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hne
      have hp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
      exact (h p hp (Nat.dvd_of_mem_primeFactors hmem)).elim hp2 hp3
    simp [hap, hp2, hp3]
  · rintro ⟨u, v, rfl⟩ p hp hpdvd
    rcases hp.dvd_mul.mp hpdvd with hp2 | hp3
    · exact Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp
        (hp.dvd_of_dvd_pow hp2)).resolve_left hp.ne_one)
    · exact Or.inr (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
        (hp.dvd_of_dvd_pow hp3)).resolve_left hp.ne_one)

/-- If a nonzero base `a` has a prime divisor other than `2` and `3`, then the exponent
triple in `2^i * 3^j * a^k` is unique. -/
theorem injective_two_pow_mul_three_pow_mul_a_pow_of_prime_dvd
    {a p : ℕ} (ha : a ≠ 0) (hp : p.Prime) (hpa : p ∣ a)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have hfac := congrArg (fun n : ℕ ↦ n.factorization p) h
  rw [Nat.factorization_mul
      (mul_ne_zero (pow_ne_zero i (by decide)) (pow_ne_zero j (by decide)))
      (pow_ne_zero k ha),
    Nat.factorization_mul (pow_ne_zero i (by decide)) (pow_ne_zero j (by decide)),
    Nat.factorization_mul
      (mul_ne_zero (pow_ne_zero i' (by decide)) (pow_ne_zero j' (by decide)))
      (pow_ne_zero k' ha),
    Nat.factorization_mul (pow_ne_zero i' (by decide)) (pow_ne_zero j' (by decide))] at hfac
  have hkfac : k * a.factorization p = k' * a.factorization p := by
    simpa only [Nat.factorization_pow,
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3), hp2, hp3,
      Ne.symm hp2, Ne.symm hp3,
      Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
      Nat.cast_id, Finsupp.single_apply, if_false, zero_add] using hfac
  have hk : k = k' :=
    Nat.mul_right_cancel (hp.factorization_pos_of_dvd ha hpa) hkfac
  subst k'
  have huv : 2 ^ i * 3 ^ j = 2 ^ i' * 3 ^ j' :=
    mul_right_cancel₀ (pow_ne_zero k ha) h
  have hfac2 := congrArg (fun n : ℕ ↦ n.factorization 2) huv
  have hi : i = i' := by
    simpa [Nat.factorization_mul,
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3)] using hfac2
  have hfac3 := congrArg (fun n : ℕ ↦ n.factorization 3) huv
  have hj : j = j' := by
    simpa [Nat.factorization_mul,
      Nat.Prime.factorization_pow (by decide : Nat.Prime 2),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3)] using hfac3
  subst i'
  subst j'
  rfl

end Nat

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

private def pairFin {n : ℕ} (u v : Fin n) : Fin (n * n) := finProdFinEquiv (u, v)

private def tripleFin {n : ℕ} (u v w : Fin n) : Fin ((n * n) * n) :=
  finProdFinEquiv (pairFin u v, w)

private def genericRowCode {n : ℕ} (i : IntegerExponent.SixBox n) : ℕ × ℕ × ℕ :=
  ((pairFin (i 0) (i 1)).val,
    (pairFin (i 2) (i 3)).val,
    (pairFin (i 4) (i 5)).val)

private def genericColCode {n : ℕ} (i : IntegerExponent.SixBox n) : ℕ × ℕ :=
  ((tripleFin (i 0) (i 1) (i 2)).val,
    (tripleFin (i 3) (i 4) (i 5)).val)

private theorem genericRowCode_injective (n : ℕ) :
    Function.Injective (@genericRowCode n) := by
  intro i j h
  have h₀₁fin : pairFin (i 0) (i 1) = pairFin (j 0) (j 1) :=
    Fin.ext (congrArg (fun t : ℕ × ℕ × ℕ ↦ t.1) h)
  have h₂₃fin : pairFin (i 2) (i 3) = pairFin (j 2) (j 3) :=
    Fin.ext (congrArg (fun t : ℕ × ℕ × ℕ ↦ t.2.1) h)
  have h₄₅fin : pairFin (i 4) (i 5) = pairFin (j 4) (j 5) :=
    Fin.ext (congrArg (fun t : ℕ × ℕ × ℕ ↦ t.2.2) h)
  have h₀₁ : (i 0, i 1) = (j 0, j 1) := by
    apply finProdFinEquiv.injective
    exact h₀₁fin
  have h₂₃ : (i 2, i 3) = (j 2, j 3) := by
    apply finProdFinEquiv.injective
    exact h₂₃fin
  have h₄₅ : (i 4, i 5) = (j 4, j 5) := by
    apply finProdFinEquiv.injective
    exact h₄₅fin
  funext k
  fin_cases k <;> simp_all

private theorem genericColCode_injective (n : ℕ) :
    Function.Injective (@genericColCode n) := by
  intro i j h
  have h₀₁₂fin : tripleFin (i 0) (i 1) (i 2) = tripleFin (j 0) (j 1) (j 2) :=
    Fin.ext (congrArg Prod.fst h)
  have h₃₄₅fin : tripleFin (i 3) (i 4) (i 5) = tripleFin (j 3) (j 4) (j 5) :=
    Fin.ext (congrArg Prod.snd h)
  have h₀₁₂ : (pairFin (i 0) (i 1), i 2) = (pairFin (j 0) (j 1), j 2) := by
    apply finProdFinEquiv.injective
    exact h₀₁₂fin
  have h₃₄₅ : (pairFin (i 3) (i 4), i 5) = (pairFin (j 3) (j 4), j 5) := by
    apply finProdFinEquiv.injective
    exact h₃₄₅fin
  have h₀₁ : (i 0, i 1) = (j 0, j 1) := by
    apply finProdFinEquiv.injective
    exact congrArg Prod.fst h₀₁₂
  have h₃₄ : (i 3, i 4) = (j 3, j 4) := by
    apply finProdFinEquiv.injective
    exact congrArg Prod.fst h₃₄₅
  funext k
  fin_cases k <;> simp_all

private def genericRowNat (a : ℕ) {n : ℕ} (i : IntegerExponent.SixBox n) : ℕ :=
  2 ^ (genericRowCode i).1 * 3 ^ (genericRowCode i).2.1 * a ^ (genericRowCode i).2.2

private def genericRowArg (a : ℕ) {n : ℕ} (i : IntegerExponent.SixBox n) : ℝ :=
  Real.log (genericRowNat a i : ℝ)

private def genericColArg {n : ℕ} (x : ℝ) (i : IntegerExponent.SixBox n) : ℝ :=
  ((genericColCode i).1 : ℝ) + ((genericColCode i).2 : ℝ) * x

private theorem genericRowNat_injective {a n : ℕ}
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2)) :
    Function.Injective (@genericRowNat a n) :=
  hmono.comp (genericRowCode_injective n)

private theorem genericRowNat_pos {a n : ℕ} (ha : 0 < a)
    (i : IntegerExponent.SixBox n) : 0 < genericRowNat a i := by
  unfold genericRowNat
  positivity

private theorem genericRowArg_injective {a : ℕ} (ha : 0 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    (n : ℕ) : Function.Injective (@genericRowArg a n) := by
  intro i j h
  apply genericRowNat_injective hmono
  have hc : (genericRowNat a i : ℝ) = (genericRowNat a j : ℝ) :=
    Real.log_injOn_pos
      (show 0 < (genericRowNat a i : ℝ) by exact_mod_cast genericRowNat_pos ha i)
      (show 0 < (genericRowNat a j : ℝ) by exact_mod_cast genericRowNat_pos ha j) h
  exact Nat.cast_injective hc

private theorem genericColArg_injective {x : ℝ} (hx : Irrational x) (n : ℕ) :
    Function.Injective (@genericColArg n x) := by
  intro i j h
  apply genericColCode_injective n
  exact IntegerExponent.Irrational.injective_nat_add_mul hx h

private theorem genericProduct_rpow_integer {a : ℕ} (ha : 0 < a)
    {x : ℝ} {u₂ u₃ ua : ℕ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) :
    ∃ z : ℤ, (z : ℝ) = ((2 ^ u₂ * 3 ^ u₃ * a ^ ua : ℕ) : ℝ) ^ x := by
  obtain ⟨z₂, hz₂⟩ := h₂
  obtain ⟨z₃, hz₃⟩ := h₃
  obtain ⟨za, hza⟩ := haPow
  refine ⟨z₂ ^ u₂ * z₃ ^ u₃ * za ^ ua, ?_⟩
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x u₂,
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x u₃,
    ← Real.rpow_pow_comm (by exact_mod_cast ha.le) x ua]
  rw [← hz₂, ← hz₃, ← hza]

private theorem generic_exp_log_mul_nat_add_integer {R : ℕ} (hR : 0 < R)
    {x : ℝ} (v₀ v₁ : ℕ)
    (hRx : ∃ z : ℤ, (z : ℝ) = (R : ℝ) ^ x) :
    ∃ z : ℤ,
      (z : ℝ) = Real.exp (Real.log (R : ℝ) * ((v₀ : ℝ) + (v₁ : ℝ) * x)) := by
  obtain ⟨z, hz⟩ := hRx
  refine ⟨(R : ℤ) ^ v₀ * z ^ v₁, ?_⟩
  push_cast
  rw [← Real.rpow_def_of_pos (by exact_mod_cast hR)]
  rw [Real.rpow_add (by exact_mod_cast hR)]
  rw [Real.rpow_natCast]
  rw [show (v₁ : ℝ) * x = x * (v₁ : ℝ) by ring]
  rw [Real.rpow_mul_natCast (by exact_mod_cast hR.le)]
  rw [← hz]

private theorem genericRowArg_nonneg {a n : ℕ} (ha : 0 < a)
    (i : IntegerExponent.SixBox n) : 0 ≤ genericRowArg a i := by
  apply Real.log_nonneg
  exact_mod_cast genericRowNat_pos ha i

private theorem genericRowArg_le {a n : ℕ} (ha : 1 ≤ a)
    (i : IntegerExponent.SixBox n) :
    genericRowArg a i ≤ (n * n : ℕ) * (Real.log 2 + Real.log 3 + Real.log a) := by
  have hu₂ : ((genericRowCode i).1 : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast (pairFin (i 0) (i 1)).isLt.le
  have hu₃ : ((genericRowCode i).2.1 : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast (pairFin (i 2) (i 3)).isLt.le
  have hua : ((genericRowCode i).2.2 : ℝ) ≤ (n * n : ℕ) := by
    exact_mod_cast (pairFin (i 4) (i 5)).isLt.le
  have hlog₂ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog₃ : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have hterm₂ : ((genericRowCode i).1 : ℝ) * Real.log 2 ≤
      ((n * n : ℕ) : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hu₂ hlog₂
  have hterm₃ : ((genericRowCode i).2.1 : ℝ) * Real.log 3 ≤
      ((n * n : ℕ) : ℝ) * Real.log 3 := mul_le_mul_of_nonneg_right hu₃ hlog₃
  have hterma : ((genericRowCode i).2.2 : ℝ) * Real.log a ≤
      ((n * n : ℕ) : ℝ) * Real.log a := mul_le_mul_of_nonneg_right hua hloga
  have hexpand : genericRowArg a i =
      ((genericRowCode i).1 : ℝ) * Real.log 2 +
      ((genericRowCode i).2.1 : ℝ) * Real.log 3 +
      ((genericRowCode i).2.2 : ℝ) * Real.log a := by
    simp only [genericRowArg, genericRowNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
  rw [hexpand]
  linarith

private theorem genericColArg_nonneg {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (i : IntegerExponent.SixBox n) : 0 ≤ genericColArg x i := by
  dsimp only [genericColArg]
  positivity

private theorem genericColArg_le {n : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (i : IntegerExponent.SixBox n) :
    genericColArg x i ≤ ((n * n) * n : ℕ) * (1 + x) := by
  have hv₀ : ((genericColCode i).1 : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast (tripleFin (i 0) (i 1) (i 2)).isLt.le
  have hv₁ : ((genericColCode i).2 : ℝ) ≤ ((n * n) * n : ℕ) := by
    exact_mod_cast (tripleFin (i 3) (i 4) (i 5)).isLt.le
  have hv₁x : ((genericColCode i).2 : ℝ) * x ≤
      (((n * n) * n : ℕ) : ℝ) * x := mul_le_mul_of_nonneg_right hv₁ hx
  dsimp only [genericColArg]
  linarith

private theorem generic_abs_rowArg_mul_colArg_le {a n D : ℕ} {x : ℝ}
    (ha : 1 < a) (hx : 0 ≤ x)
    (hD : (Real.log 2 + Real.log 3 + Real.log a) * (1 + x) ≤ D)
    (i j : IntegerExponent.SixBox n) :
    |genericRowArg a i * genericColArg x j| ≤ (D * n ^ 5 : ℕ) := by
  have hapos : 0 < a := by omega
  have hrow0 := genericRowArg_nonneg hapos i
  have hcol0 := genericColArg_nonneg hx j
  have hrow := genericRowArg_le ha.le i
  have hcol := genericColArg_le hx j
  rw [abs_of_nonneg (mul_nonneg hrow0 hcol0)]
  calc
    genericRowArg a i * genericColArg x j ≤
        ((n * n : ℕ) : ℝ) * (Real.log 2 + Real.log 3 + Real.log a) *
          (((n * n) * n : ℕ) * (1 + x)) :=
      mul_le_mul hrow hcol hcol0
        (mul_nonneg (Nat.cast_nonneg _) (by positivity))
    _ = ((n ^ 5 : ℕ) : ℝ) *
        ((Real.log 2 + Real.log 3 + Real.log a) * (1 + x)) := by
      push_cast
      ring
    _ ≤ ((n ^ 5 : ℕ) : ℝ) * D :=
      mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
    _ = (D * n ^ 5 : ℕ) := by
      push_cast
      ring

private theorem generic_exp_rowArg_mul_colArg_integer {a n : ℕ} (ha : 0 < a)
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x)
    (i j : IntegerExponent.SixBox n) :
    ∃ z : ℤ,
      (z : ℝ) = Real.exp (genericRowArg a i * genericColArg x j) := by
  have hR : ∃ z : ℤ, (z : ℝ) = (genericRowNat a i : ℝ) ^ x := by
    simpa only [genericRowNat] using
      (genericProduct_rpow_integer ha (x := x)
        (u₂ := (genericRowCode i).1) (u₃ := (genericRowCode i).2.1)
        (ua := (genericRowCode i).2.2) h₂ h₃ haPow)
  simpa only [genericRowArg, genericColArg] using
    (generic_exp_log_mul_nat_add_integer (R := genericRowNat a i)
      (genericRowNat_pos ha i) (genericColCode j).1 (genericColCode j).2 hR)

/-- The abstract three-base determinant step.  Unique factorization is used only
through the stated injectivity of the monomials in `2`, `3`, and `a`. -/
private theorem not_irrational_of_two_three_a_rpow_integer_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) :
    ¬ Irrational x := by
  intro hxirr
  have hx0 : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  let K : ℝ := (Real.log 2 + Real.log 3 + Real.log a) * (1 + x)
  obtain ⟨D, hD⟩ := exists_nat_ge K
  let N : ℕ := 192 * D + 3
  let n : ℕ := 2 * N
  let m : ℕ := n ^ 6
  let r : ℕ := 32 * N ^ 6
  let C : ℕ := D * n ^ 5

  have hDN : 192 * D ≤ N := by
    dsimp only [N]
    omega
  have hNpos : 0 < N := by
    dsimp only [N]
    omega
  have hm : m = 2 * r := by
    dsimp only [m, r, n]
    ring
  have hr : 2 < r := by
    have hpow : 0 < N ^ 6 := pow_pos hNpos _
    dsimp only [r]
    omega
  have hCr : 192 * C ≤ r := by
    calc
      192 * C = (192 * D) * (32 * N ^ 5) := by
        dsimp only [C, n]
        ring
      _ ≤ N * (32 * N ^ 5) := Nat.mul_le_mul_right _ hDN
      _ = r := by
        dsimp only [r]
        ring
  have hrm : r ≤ m := by omega
  obtain ⟨hsmall, hnumeric⟩ :=
    IntegerExponent.exponential_det_numeric_bound C m r hm hr hCr

  have hcard : Fintype.card (IntegerExponent.SixBox n) = m := by
    rw [IntegerExponent.card_sixBox]
  let e : Fin m ≃ IntegerExponent.SixBox n := (Fintype.equivFinOfCardEq hcard).symm
  let row : Fin m → ℝ := fun i ↦ genericRowArg a (e i)
  let col : Fin m → ℝ := fun j ↦ genericColArg x (e j)
  let A : Matrix (Fin m) (Fin m) ℝ := fun i j ↦ Real.exp (row i * col j)

  have hrow : Function.Injective row :=
    (genericRowArg_injective (by omega) hmono n).comp e.injective
  have hcol : Function.Injective col :=
    (genericColArg_injective hxirr n).comp e.injective
  have hAne : A.det ≠ 0 := by
    exact IntegerExponent.det_exp_mul_ne_zero_of_injective row col hrow hcol
  have hAint : ∀ i j, ∃ z : ℤ, (z : ℝ) = A i j := by
    intro i j
    exact generic_exp_rowArg_mul_colArg_integer (by omega) h₂ h₃ haPow (e i) (e j)
  have hlower : 1 ≤ |A.det| :=
    IntegerExponent.one_le_abs_det_of_integer_entries A hAint hAne

  have hkernel : ∀ i j, |row i * col j| ≤ (C : ℝ) := by
    intro i j
    change |genericRowArg a (e i) * genericColArg x (e j)| ≤ (C : ℝ)
    simpa only [C] using
      (generic_abs_rowArg_mul_colArg_le ha hx0 (by simpa only [K] using hD) (e i) (e j))
  have hupper : |A.det| ≤
      (2 : ℝ) ^ m * (m.factorial : ℝ) * Real.exp (C : ℝ) ^ r *
        (Real.exp (C : ℝ) * (C : ℝ) ^ r / (r.factorial : ℝ)) ^ (m - r) := by
    change |Matrix.det (fun i j ↦ Real.exp (row i * col j))| ≤ _
    exact IntegerExponent.abs_det_exp_mul_le hrm row col (C : ℝ)
      (Nat.cast_nonneg _) hkernel hsmall
  have hdet_lt : |A.det| < 1 := hupper.trans_lt (by
    simpa only [mul_div_assoc] using hnumeric)
  exact (not_lt_of_ge hlower) hdet_lt

/-- A generic form of the six-exponentials consequence used here: if the
monomials in the three bases are distinct, integral powers at all three bases
force the exponent to be rational. -/
theorem rational_of_two_three_a_rpow_integer_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  exact not_not.mp
    (not_irrational_of_two_three_a_rpow_integer_of_monomial_injective
      ha hmono h₂ h₃ haPow)

/-- Integral powers at `2`, `3`, and a third multiplicatively independent
natural base force an integral exponent. -/
theorem integer_of_two_three_a_rpow_integer_of_monomial_injective
    {a : ℕ} (ha : 1 < a)
    (hmono : Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2))
    {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  apply IntegerExponent.integer_of_rational_of_two_rpow_integer
  · exact rational_of_two_three_a_rpow_integer_of_monomial_injective
      ha hmono h₂ h₃ haPow
  · exact h₂

/-- If `a` has a prime factor other than `2` and `3`, the monomials in `2`,
`3`, and `a` are pairwise distinct. -/
theorem monomial_injective_of_prime_dvd_ne_two_three {a p : ℕ}
    (ha : 0 < a) (hp : p.Prime) (hpa : p ∣ a) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Function.Injective
      (fun u : ℕ × ℕ × ℕ ↦ 2 ^ u.1 * 3 ^ u.2.1 * a ^ u.2.2) := by
  exact Nat.injective_two_pow_mul_three_pow_mul_a_pow_of_prime_dvd
    ha.ne' hp hpa hp2 hp3

/-- If a positive natural base has a prime factor other than `2` and `3`,
integrality at that base together with integrality at `2` and `3` forces the
exponent to be an integer. -/
theorem integer_of_two_three_a_rpow_integer_of_prime_factor
    {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hpa : p ∣ a)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x : ℝ}
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  have hpa_le : p ≤ a := Nat.le_of_dvd ha hpa
  have ha1 : 1 < a := hp.one_lt.trans_le hpa_le
  exact integer_of_two_three_a_rpow_integer_of_monomial_injective ha1
    (monomial_injective_of_prime_dvd_ne_two_three ha hp hpa hp2 hp3)
    h₂ h₃ haPow

/-- Under a hypothetical nonintegral exponent with integral powers at `2` and
`3`, every further positive natural base with an integral power is `3`-smooth. -/
theorem eq_two_pow_mul_three_pow_of_not_integer_of_rpows_integer
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {a : ℕ} (ha : 0 < a)
    (haPow : ∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) :
    ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by
  rw [← Nat.prime_dvd_eq_two_or_three_iff_eq_two_pow_mul_three_pow ha]
  intro p hp hpa
  by_contra hp23
  have hp2 : p ≠ 2 := fun h ↦ hp23 (Or.inl h)
  have hp3 : p ≠ 3 := fun h ↦ hp23 (Or.inr h)
  exact hx (integer_of_two_three_a_rpow_integer_of_prime_factor
    ha hp hpa hp2 hp3 h₂ h₃ haPow)

/-- Exact structural classification of all positive natural bases having an
integral `x`-th power under a hypothetical two-base counterexample: they are
precisely the `3`-smooth numbers. -/
theorem rpow_integer_iff_eq_two_pow_mul_three_pow_of_not_integer
    {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ))
    (h₂ : ∃ z : ℤ, (z : ℝ) = (2 : ℝ) ^ x)
    (h₃ : ∃ z : ℤ, (z : ℝ) = (3 : ℝ) ^ x)
    {a : ℕ} (ha : 0 < a) :
    (∃ z : ℤ, (z : ℝ) = (a : ℝ) ^ x) ↔
      ∃ u v : ℕ, a = 2 ^ u * 3 ^ v := by
  constructor
  · exact eq_two_pow_mul_three_pow_of_not_integer_of_rpows_integer
      hx h₂ h₃ ha
  · rintro ⟨u, v, rfl⟩
    obtain ⟨z₂, hz₂⟩ := h₂
    obtain ⟨z₃, hz₃⟩ := h₃
    refine ⟨z₂ ^ u * z₃ ^ v, ?_⟩
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) x u,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 3) x v]
    rw [← hz₂, ← hz₃]

end

end LeanProofs.TwoBaseIntegerExponent
