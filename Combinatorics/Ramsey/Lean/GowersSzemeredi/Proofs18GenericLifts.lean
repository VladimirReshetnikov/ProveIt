import GowersSzemeredi.Proofs18UniformCovers
import GowersSzemeredi.Proofs03FourFactorSymmetry
import GowersSzemeredi.Proofs05Corollary58
import GowersSzemeredi.Proofs18WidthPowerBoundsSide

/-! Closed-form lift densities and widths for the single-piece step in any
dimension (Notes L.7a, F3b).

`single_piece_inverse_step_global` at dimension `k` asks for a density
`C` and a width `W` below every lift `liftLastC^[j]`, `liftLastW^[j]`,
`1 ≤ j ≤ k`, of the base controls. Here they are closed forms:
* `genC X a b c k t = X^(−a)·t^b` on `(0, 1]`. This is below every lift once
  the base density satisfies `RecipPowerLB X c a₀ b₀` with
  `a ≥ a₀ + k(b₀ + k)` and `b ≥ b₀ + k` (`genC_le`). Outside `(0, 1]` it is
  the minimum of the lifts (`liftMinC`).
* `genW E k t L = ⌈L^ε⌉` with `ε = lwE E k t = E(t/2^(k+1))/4^k`, above the
  threshold `16^k·6^(4/ε)`, and `0` below it (`genW_le`).
* `nestC_genC`: the `r`-fold nest of `genC` is `X^(−a·S_r)·t^(b^r)`, with
  `S_r = 1 + b + … + b^(r−1)`.

`lift_width_powerLB` is the `j`-fold version of `liftLastW_powerLB`: all the
exponents in its threshold equal `E(t/2^(j+1))`, so the threshold is at most
`16^j·6^(4/ε)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### Densities -/

/-- The minimum of the first `j` lifts of a density. -/
def liftMinC (c : Real → Real) : Nat → Real → Real
  | 0 => fun _ => 1
  | j + 1 => fun t => min ((liftLastC^[j + 1] c) t) (liftMinC c j t)

theorem liftMinC_le (c : Real → Real) :
    ∀ k j, 1 ≤ j → j ≤ k → ∀ t, liftMinC c k t ≤ (liftLastC^[j] c) t := by
  intro k
  induction k with
  | zero => intro j hj hjk; omega
  | succ k ih =>
    intro j hj hjk t
    show min ((liftLastC^[k + 1] c) t) (liftMinC c k t) ≤ (liftLastC^[j] c) t
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact (min_le_right _ _).trans (ih j hj (by omega) t)
    · obtain rfl : j = k + 1 := by omega
      exact min_le_left _ _

theorem RecipPowerLB.le_monomial {X : Real} {c : Real → Real} {a b a' b' : Nat} (hX : 1 ≤ X)
    (h : RecipPowerLB X c a b) (ha : a ≤ a') (hb : b ≤ b') {t : Real} (ht : 0 < t) (ht1 : t ≤ 1) :
    (X ^ a')⁻¹ * t ^ b' ≤ c t := by
  obtain ⟨h0, -, h2⟩ := (h.mono hX ha hb) t ht ht1
  have hX0 : 0 < X ^ a' := pow_pos (by linarith) _
  have hti : t⁻¹ ^ b' = (t ^ b')⁻¹ := inv_pow t b'
  rw [hti] at h2
  have htb : 0 < t ^ b' := pow_pos ht _
  have h3 : (X ^ a' * (t ^ b')⁻¹)⁻¹ ≤ c t := by
    have := inv_anti₀ (inv_pos.mpr h0) h2
    rwa [inv_inv] at this
  rwa [mul_inv, inv_inv] at h3

theorem recipPowerLB_iterate_lift {X : Real} {c : Real → Real} {a b : Nat} (hX : 2 ≤ X)
    (h : RecipPowerLB X c a b) :
    ∀ j : Nat, RecipPowerLB X (liftLastC^[j] c) (a + j * (b + j)) (b + j) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    refine (ih.liftLastC hX).mono (by linarith) ?_ (by omega)
    have : (j + 1) * (b + (j + 1)) = j * (b + j) + (b + j) + (j + 1) := by ring
    omega

/-- **The closed-form lift density**: `X^(−a)·t^b` on `(0, 1]`. -/
def genC (X : Real) (a b : Nat) (c : Real → Real) (k : Nat) : Real → Real :=
  fun t => if 0 < t ∧ t ≤ 1 then (X ^ a)⁻¹ * t ^ b else liftMinC c k t

theorem genC_eq {X : Real} {a b : Nat} {c : Real → Real} {k : Nat} {t : Real} (ht : 0 < t)
    (ht1 : t ≤ 1) : genC X a b c k t = (X ^ a)⁻¹ * t ^ b := by
  unfold genC; rw [if_pos ⟨ht, ht1⟩]

theorem genC_pos_le {X : Real} (hX : 1 ≤ X) (a b : Nat) (c : Real → Real) (k : Nat) :
    ∀ t, 0 < t → t ≤ 1 → 0 < genC X a b c k t ∧ genC X a b c k t ≤ 1 := by
  intro t ht ht1
  rw [genC_eq ht ht1]
  have hXa : 1 ≤ X ^ a := one_le_pow₀ hX
  refine ⟨mul_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hXa)) (pow_pos ht _), ?_⟩
  calc (X ^ a)⁻¹ * t ^ b ≤ 1 * 1 :=
        mul_le_mul (inv_le_one_of_one_le₀ hXa) (pow_le_one₀ ht.le ht1) (pow_nonneg ht.le _)
          zero_le_one
    _ = 1 := one_mul 1

/-- `genC` is below every lift `liftLastC^[j] c`, `1 ≤ j ≤ k`. -/
theorem genC_le {X : Real} (hX : 2 ≤ X) {c : Real → Real} {a0 b0 a b k : Nat}
    (hc : RecipPowerLB X c a0 b0) (ha : a0 + k * (b0 + k) ≤ a) (hb : b0 + k ≤ b) :
    ∀ j, 1 ≤ j → j ≤ k → ∀ t, genC X a b c k t ≤ (liftLastC^[j] c) t := by
  intro j hj hjk t
  unfold genC
  split_ifs with h
  · obtain ⟨ht, ht1⟩ := h
    refine (recipPowerLB_iterate_lift hX hc j).le_monomial (by linarith) ?_ (by omega) ht ht1
    have : j * (b0 + j) ≤ k * (b0 + k) := Nat.mul_le_mul hjk (by omega)
    omega
  · exact liftMinC_le c k j hj hjk t

/-- The geometric sum `1 + b + … + b^(r−1)`. -/
def geomSum (b : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => 1 + b * geomSum b r

/-- **The nest of the closed-form density.** -/
theorem nestC_genC {X : Real} (hX : 1 ≤ X) (a b : Nat) (c : Real → Real) (k : Nat) :
    ∀ r t, 0 < t → t ≤ 1 →
      nestC (fun _ => genC X a b c k) r t = (X ^ (a * geomSum b r))⁻¹ * t ^ (b ^ r) := by
  intro r
  induction r with
  | zero => intro t _ _; simp [nestC, geomSum]
  | succ r ih =>
    intro t ht ht1
    obtain ⟨h0, h1⟩ := nestC_pos_le (c := fun _ => genC X a b c k)
      (fun _ => genC_pos_le hX a b c k) r t ht ht1
    show genC X a b c k (nestC (fun _ => genC X a b c k) r t) = _
    rw [genC_eq h0 h1, ih t ht ht1, mul_pow, ← pow_mul, inv_pow, ← pow_mul]
    simp only [geomSum]
    rw [show a * (1 + b * geomSum b r) = a + a * geomSum b r * b by ring, pow_add, mul_inv,
      show b ^ (r + 1) = b ^ r * b by ring]
    ring

/-! ### Widths -/

/-- The exponent of `j` lifts of `coverWidth E` at `t`. -/
def lwE (E : Real → Real) (j : Nat) (t : Real) : Real := E (t / 2 ^ (j + 1)) / 4 ^ j

/-- The threshold of `j` lifts of `coverWidth E` at `t`. -/
def lwT (E : Real → Real) : Nat → Real → Real
  | 0 => fun _ => 0
  | j + 1 => fun t => max (8 * lwT E j (t / 2) + 8) ((6 : Real) ^ (4 / lwE E j (t / 2)))

theorem lwE_succ (E : Real → Real) (j : Nat) (t : Real) :
    lwE E j (t / 2) / 4 = lwE E (j + 1) t := by
  unfold lwE
  have h1 : t / 2 / 2 ^ (j + 1) = t / 2 ^ (j + 1 + 1) := by rw [div_div]; congr 1; ring
  rw [h1, div_div, ← pow_succ]

theorem lwE_pos_le {E : Real → Real} (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1) (j : Nat)
    {t : Real} (ht : 0 < t) (ht1 : t ≤ 1) : 0 < lwE E j t ∧ lwE E j t ≤ 1 := by
  have hs : 0 < t / 2 ^ (j + 1) := by positivity
  have hs1 : t / 2 ^ (j + 1) ≤ 1 :=
    (div_le_self ht.le (one_le_pow₀ (by norm_num))).trans ht1
  obtain ⟨h0, h1⟩ := hE _ hs hs1
  unfold lwE
  refine ⟨by positivity, ?_⟩
  exact (div_le_self h0.le (one_le_pow₀ (by norm_num))).trans h1

theorem lwT_nonneg (E : Real → Real) : ∀ j t, 0 ≤ lwT E j t := by
  intro j
  induction j with
  | zero => intro t; exact le_rfl
  | succ j ih =>
    intro t
    show 0 ≤ max (8 * lwT E j (t / 2) + 8) ((6 : Real) ^ (4 / lwE E j (t / 2)))
    exact le_max_of_le_left (by linarith [ih (t / 2)])

/-- **`j` lifts of a cover width are a power above `lwT`.** -/
theorem lift_width_powerLB {E : Real → Real} (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1) :
    ∀ j t, 0 < t → t ≤ 1 →
      WidthPowerLB ((liftLastW^[j] (coverWidth E)) t) (lwE E j t) (lwT E j t) := by
  intro j
  induction j with
  | zero =>
    intro t ht ht1
    have h0 := (hE (t / 2) (by positivity) (by linarith)).1
    have h := coverWidth_powerLB E t h0.le
    simpa [lwE, lwT] using h
  | succ j ih =>
    intro t ht ht1
    have ht2 : 0 < t / 2 := by positivity
    have ht21 : t / 2 ≤ 1 := by linarith
    obtain ⟨he0, he1⟩ := lwE_pos_le hE j ht2 ht21
    have h := liftLastW_powerLB he0 he1 (lwT_nonneg E j (t / 2)) (ih (t / 2) ht2 ht21)
    rw [Function.iterate_succ_apply']
    rw [lwE_succ] at h
    exact h

theorem lwT_le {E : Real → Real} (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1) :
    ∀ j t, 0 < t → t ≤ 1 → lwT E j t ≤ 16 ^ j * (6 : Real) ^ (4 / lwE E j t) := by
  intro j
  induction j with
  | zero => intro t _ _; simp [lwT]; positivity
  | succ j ih =>
    intro t ht ht1
    have ht2 : 0 < t / 2 := by positivity
    have ht21 : t / 2 ≤ 1 := by linarith
    obtain ⟨he0, -⟩ := lwE_pos_le hE (j + 1) ht ht1
    have hIH := ih (t / 2) ht2 ht21
    have heq : lwE E j (t / 2) = 4 * lwE E (j + 1) t := by
      rw [← lwE_succ]; ring
    set ε := lwE E (j + 1) t with hε
    have h41 : 4 / lwE E j (t / 2) = 1 / ε := by
      rw [heq]; field_simp
    rw [h41] at hIH
    have hy1 : (1 : Real) ≤ (6 : Real) ^ (1 / ε) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hyy : (6 : Real) ^ (1 / ε) ≤ (6 : Real) ^ (4 / ε) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (div_le_div_of_nonneg_right (by norm_num) he0.le)
    have h16 : (1 : Real) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
    show max (8 * lwT E j (t / 2) + 8) ((6 : Real) ^ (4 / lwE E j (t / 2))) ≤ _
    rw [h41]
    set y := (6 : Real) ^ (4 / ε)
    have hy : 1 ≤ y := hy1.trans hyy
    have hpow : (16 : Real) ^ (j + 1) = 16 ^ j * 16 := pow_succ _ _
    rw [hpow]
    refine max_le ?_ ?_
    · have h1 : 8 * lwT E j (t / 2) ≤ 8 * (16 ^ j * y) := by
        have := hIH.trans (mul_le_mul_of_nonneg_left hyy (by positivity))
        linarith
      have h2 : (8 : Real) ≤ 8 * (16 ^ j * y) := by
        have : (1 : Real) ≤ 16 ^ j * y := one_le_mul_of_one_le_of_one_le h16 hy
        linarith
      nlinarith
    · have : (1 : Real) ≤ 16 ^ j * 16 := by nlinarith
      nlinarith

/-- **The closed-form lift width**: `⌈L^ε⌉` above `16^k·6^(4/ε)`, with
`ε = lwE E k t`. -/
def genW (E : Real → Real) (k : Nat) : Real → Nat → Nat :=
  fun t L => if 0 < t ∧ t ≤ 1 ∧ (16 : Real) ^ k * (6 : Real) ^ (4 / lwE E k t) ≤ L then
    ⌈(L : Real) ^ lwE E k t⌉₊ else 0

/-- The threshold of `genW`. -/
def genWThr (E : Real → Real) (k : Nat) (t : Real) : Real :=
  (16 : Real) ^ k * (6 : Real) ^ (4 / lwE E k t)

theorem one_le_genWThr {E : Real → Real} (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1) (k : Nat)
    {t : Real} (ht : 0 < t) (ht1 : t ≤ 1) : 1 ≤ genWThr E k t := by
  obtain ⟨he0, -⟩ := lwE_pos_le hE k ht ht1
  unfold genWThr
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (Real.one_le_rpow (by norm_num) (by positivity))

theorem genW_powerLB (E : Real → Real) (k : Nat) {t : Real} (ht : 0 < t) (ht1 : t ≤ 1) :
    WidthPowerLB (genW E k t) (lwE E k t) (genWThr E k t) := by
  intro L hL
  unfold genW
  rw [if_pos ⟨ht, ht1, hL⟩]
  exact Nat.le_ceil _

theorem genW_mono {E : Real → Real} (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1) (k : Nat) :
    ∀ t, Monotone (genW E k t) := by
  intro t L L' hLL'
  unfold genW
  split_ifs with h h'
  · obtain ⟨ht, ht1, -⟩ := h
    have he0 := (lwE_pos_le hE k ht ht1).1
    exact Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hLL') he0.le)
  · exfalso
    obtain ⟨ht, ht1, hL⟩ := h
    exact h' ⟨ht, ht1, hL.trans (by exact_mod_cast hLL')⟩
  · exact Nat.zero_le _
  · exact le_rfl

/-- `genW` is below every lift `liftLastW^[j] (coverWidth E)`, `1 ≤ j ≤ k`, when
`E` is monotone. -/
theorem genW_le {E : Real → Real} (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s ∧ E s ≤ 1)
    (hmono : ∀ s s', 0 < s → s ≤ s' → s' ≤ 1 → E s ≤ E s') {k : Nat} :
    ∀ j, j ≤ k → ∀ t L, genW E k t L ≤ (liftLastW^[j] (coverWidth E)) t L := by
  intro j hjk t L
  unfold genW
  split_ifs with h
  · obtain ⟨ht, ht1, hL⟩ := h
    obtain ⟨hk0, -⟩ := lwE_pos_le hE k ht ht1
    obtain ⟨hj0, -⟩ := lwE_pos_le hE j ht ht1
    -- the exponents
    have hs : 0 < t / 2 ^ (k + 1) := by positivity
    have hss : t / 2 ^ (k + 1) ≤ t / 2 ^ (j + 1) :=
      div_le_div_of_nonneg_left ht.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega))
    have hs1 : t / 2 ^ (j + 1) ≤ 1 := (div_le_self ht.le (one_le_pow₀ (by norm_num))).trans ht1
    have hEk := hmono _ _ hs hss hs1
    have hEk0 := (hE _ hs (hss.trans hs1)).1
    have hexp : lwE E k t ≤ lwE E j t := by
      unfold lwE
      calc E (t / 2 ^ (k + 1)) / 4 ^ k ≤ E (t / 2 ^ (j + 1)) / 4 ^ k :=
            div_le_div_of_nonneg_right hEk (by positivity)
        _ ≤ E (t / 2 ^ (j + 1)) / 4 ^ j :=
            div_le_div_of_nonneg_left (hEk0.le.trans hEk) (by positivity)
              (pow_le_pow_right₀ (by norm_num) hjk)
    -- the thresholds
    have hthr : lwT E j t ≤ genWThr E k t := by
      refine (lwT_le hE j t ht ht1).trans ?_
      unfold genWThr
      have h4 : 4 / lwE E j t ≤ 4 / lwE E k t := div_le_div_of_nonneg_left (by norm_num) hk0 hexp
      exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hjk)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) h4) (by positivity) (by positivity)
    have hL1 : (1 : Real) ≤ L := (one_le_genWThr hE k ht ht1).trans hL
    have hw := lift_width_powerLB hE j t ht ht1 L (hthr.trans hL)
    exact Nat.ceil_le.mpr ((Real.rpow_le_rpow_of_exponent_le hL1 hexp).trans hw)
  · exact Nat.zero_le _

end LeanProofs.GowersSzemeredi
