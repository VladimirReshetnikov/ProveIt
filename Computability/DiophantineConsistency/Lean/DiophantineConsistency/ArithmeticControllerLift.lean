import DiophantineConsistency.ArithmeticPow
import DiophantineConsistency.ArithmeticModularCancellation
import Mathlib.Tactic.Ring

/-! **K5a — p-adic lifting for the controller** (construction spec §7 K3 and
§8.2), generic in the odd modulus `p`, in every model of IΣ1.

Let `p = 2h+1`, `c > 0`, `C0 = c·p`, and `g = 1 + C0·v` with `v` a unit modulo
`p` (`v·vinv ≡ 1`). All exponents and moduli below are internal, so powers are
the represented `ArithmeticPow.power`.

* `expand` — the fixed-degree binomial expansion
  `(1+x)^n = 1 + n·x + b·x² + x³·E` with `2b + n = n²`, by Σ1 induction on `n`.
* `lte` (lifting the exponent) — `g^(p^k) = 1 + C0·p^k·w` with `w ≡ v (mod p)`.
* `coordinates_surj` (Hensel induction, replacing the pigeonhole principle) —
  every `z < p^k` has `j < p^k` and `Q` with `g^j = C0·p^k·Q + 1 + C0·z`.
* `coordinates_inj` — `j ↦ g^j mod C0·p^k` is injective on `[0, p^k)`.

Both coordinate statements are proved by internal induction on `k`; no coded
permutation, finite-set counting or `emultiplicity` is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticControllerLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Residue arithmetic -/

theorem mod_mod' (a : V) {m : V} (hm : 0 < m) : a % m % m = a % m :=
  mod_eq_self_of_lt (mod_lt a hm)

theorem mod_add_mod_left (a b : V) {m : V} (hm : 0 < m) : (a % m + b) % m = (a + b) % m := by
  rw [mod_add hm, mod_mod' a hm, ← mod_add hm]

theorem mod_add_mod_right (a b : V) {m : V} (hm : 0 < m) : (a + b % m) % m = (a + b) % m := by
  rw [mod_add hm, mod_mod' b hm, ← mod_add hm]

theorem mod_mul_mod_left (a b : V) {m : V} (hm : 0 < m) : (a % m * b) % m = (a * b) % m := by
  rw [mod_mul hm, mod_mod' a hm, ← mod_mul hm]

theorem mod_mul_mod_right (a b : V) {m : V} (hm : 0 < m) : (a * (b % m)) % m = (a * b) % m := by
  rw [mod_mul hm, mod_mod' b hm, ← mod_mul hm]

theorem mul_mod_mul {k a b : V} (hk : 0 < k) (hb : 0 < b) : (k * a) % (k * b) = k * (a % b) :=
  ArithmeticModularCancellation.mul_mod_mul hk hb

theorem mod_of_mul_mod (a : V) {M q : V} (hM : 0 < M) : (a % (M * q)) % M = a % M :=
  ArithmeticModularCancellation.mod_mod_of_dvd hM (dvd_mul_right M q) a

theorem add_cancel_mod {M a x y : V} (hM : 0 < M) (h : (a + x) % M = (a + y) % M) :
    x % M = y % M := by
  exact ArithmeticModularCancellation.add_cancel (a := x) (b := y) (c := a) hM
    (by simpa only [add_comm] using h)

theorem mul_cancel_left {k a b : V} (hk : 0 < k) (h : k * a = k * b) : a = b :=
  le_antisymm (le_of_mul_le_mul_left h.le hk) (le_of_mul_le_mul_left h.ge hk)

/-! ## Fixed-degree binomial expansion -/

theorem expand (x n : V) :
    ∃ b E, 2 * b + n = n * n ∧ power (1 + x) n = 1 + n * x + b * (x * x) + x * x * x * E := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, 0, by simp, by simp⟩
  case succ n ih =>
    obtain ⟨b, E, hb, hp⟩ := ih
    refine ⟨b + n, E + b + x * E, ?_, ?_⟩
    · calc 2 * (b + n) + (n + 1) = (2 * b + n) + (2 * n + 1) := by ring
        _ = (n + 1) * (n + 1) := by rw [hb]; ring
    · rw [power_succ, hp]; ring

theorem power_one_add (x n : V) : ∃ E, power (1 + x) n = 1 + n * x + x * x * E := by
  obtain ⟨b, E, _, hp⟩ := expand x n
  exact ⟨b + x * E, by rw [hp]; ring⟩

theorem power_one_add_mul (x n : V) : ∃ t, power (1 + x) n = 1 + x * t := by
  obtain ⟨E, hE⟩ := power_one_add x n
  exact ⟨n + x * E, by rw [hE]; ring⟩

/-! ## Lifting the exponent -/

section lift
variable {p c v vinv h : V}

/-- **LTE.** `(1 + c p v)^(p^k) = 1 + c·p·p^k·w` with `w ≡ v (mod p)`. -/
theorem lte (hp : p = 2 * h + 1) :
    ∀ k, ∃ w, w % p = v % p ∧ power (1 + c * p * v) (power p k) = 1 + c * p * power p k * w := by
  have hp0 : 0 < p := by rw [hp]; exact lt_of_lt_of_le _root_.zero_lt_one (le_add_self)
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨v, rfl, by simp⟩
  case succ k ih =>
    obtain ⟨w, hw, hG⟩ := ih
    rw [power_succ p k, mul_comm p (power p k), ← power_iterate, hG]
    obtain ⟨b, E, hb, hx⟩ := expand (c * p * power p k * w) p
    have h1 : 2 * b + p = 2 * (p * h) + p := by
      rw [hb]
      calc p * p = p * (2 * h + 1) := by rw [← hp]
        _ = 2 * (p * h) + p := by ring
    have hbh : b = p * h := mul_cancel_left (by norm_num) (add_right_cancel h1)
    refine ⟨w + p * (h * c * power p k * w * w + c * c * power p k * power p k * w * w * w * E),
      ?_, ?_⟩
    · rw [mod_add_mul' _ _ hp0]; exact hw
    · rw [hx, hbh]; ring

/-- Every power of `g = 1 + c p v` is `1 + c p ·(…)`. -/
theorem power_g (j : V) : ∃ t, power (1 + c * p * v) j = 1 + c * p * t := by
  obtain ⟨t, ht⟩ := power_one_add_mul (c * p * v) j
  exact ⟨v * t, by rw [ht]; ring⟩

/-- One lift step at level `P = p^k`: `g^(P l + j0) = g^j0 + C0 P (l w) + C0 (p P) T`. -/
theorem decomp (k j0 l w : V)
    (hG : power (1 + c * p * v) (power p k) = 1 + c * p * power p k * w) :
    ∃ T, power (1 + c * p * v) (power p k * l + j0) =
      power (1 + c * p * v) j0 + c * p * power p k * (l * w) + c * p * (p * power p k) * T := by
  obtain ⟨t0, ht0⟩ := power_g (c := c) (p := p) (v := v) j0
  obtain ⟨E, hE⟩ := power_one_add (c * p * power p k * w) l
  refine ⟨c * w * l * t0 + c * power p k * w * w * E * (1 + c * p * t0), ?_⟩
  rw [power_add, ← power_iterate, hG, hE, ht0]
  ring

/-- **Discrete-log surjectivity by Hensel induction.** -/
theorem coordinates_surj (hp : p = 2 * h + 1) (hinv : (v * vinv) % p = 1) :
    ∀ k, ∀ z < power p k, ∃ j < power p k, ∃ Q,
      power (1 + c * p * v) j = c * p * power p k * Q + 1 + c * p * z := by
  have hp0 : 0 < p := by rw [hp]; exact lt_of_lt_of_le _root_.zero_lt_one (le_add_self)
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro z hz
    have hz0 : z = 0 := by simpa using hz
    exact ⟨0, by simp, 0, by simp [hz0]⟩
  case succ k ih =>
    intro z hz
    set P := power p k with hPdef
    have hP : 0 < P := power_pos p k hp0
    rw [power_succ p k] at hz ⊢
    rw [← hPdef] at hz ⊢
    have hz0 : z % P < P := mod_lt z hP
    have hzh : z / P < p := div_lt_of_lt_mul hz
    obtain ⟨j0, hj0, Q, hQ⟩ := ih (z % P) hz0
    obtain ⟨w, hw, hG⟩ := lte (c := c) (v := v) hp k
    obtain ⟨T, hT⟩ := decomp (c := c) (v := v) k j0
      (((z / P + (p - Q % p)) * vinv) % p) w hG
    set l := ((z / P + (p - Q % p)) * vinv) % p with hldef
    have hl : l < p := mod_lt _ hp0
    have hy : Q % p ≤ p := (mod_lt Q hp0).le
    -- the residue of the new digit
    have hres : (Q + l * w) % p = z / P := by
      have hlw : (l * w) % p = (z / P + (p - Q % p)) % p := by
        rw [← mod_mul_mod_right l w hp0, hw, mod_mul_mod_right l v hp0, hldef,
          mod_mul_mod_left _ v hp0, mul_assoc, ← mod_mul_mod_right _ (vinv * v) hp0,
          mul_comm vinv v, hinv, mul_one]
      rw [← mod_add_mod_right Q (l * w) hp0, hlw, mod_add_mod_right Q _ hp0,
        ← mod_add_mod_left Q _ hp0,
        show Q % p + (z / P + (p - Q % p)) = z / P + p * 1 by
          rw [mul_one, add_comm (z / P), ← add_assoc, add_tsub_cancel_of_le hy, add_comm],
        mod_add_mul' _ _ hp0, mod_eq_self_of_lt hzh]
    have hγ : p * ((Q + l * w) / p) + z / P = Q + l * w := by
      have := div_add_mod (Q + l * w) p
      rwa [hres] at this
    refine ⟨P * l + j0, ?_, (Q + l * w) / p + T, ?_⟩
    · calc P * l + j0 < P * l + P := (add_lt_add_iff_left (P * l)).mpr hj0
        _ = P * (l + 1) := by ring
        _ ≤ P * p := mul_le_mul_of_nonneg_left (lt_iff_succ_le.mp hl) (Arithmetic.zero_le _)
        _ = p * P := mul_comm _ _
    · have hzd : P * (z / P) + z % P = z := div_add_mod z P
      rw [hT, hQ]
      calc c * p * P * Q + 1 + c * p * (z % P) + c * p * P * (l * w) + c * p * (p * P) * T
          = 1 + c * p * (z % P) + c * p * P * (Q + l * w) + c * p * (p * P) * T := by ring
        _ = 1 + c * p * (z % P) + c * p * P * (p * ((Q + l * w) / p) + z / P) +
            c * p * (p * P) * T := by rw [hγ]
        _ = c * p * (p * P) * ((Q + l * w) / p + T) + 1 + c * p * (P * (z / P) + z % P) := by
            ring
        _ = _ := by rw [hzd]

/-- **Injectivity of the coordinates** on `[0, p^k)`. -/
theorem coordinates_inj (hp : p = 2 * h + 1) (hc : 0 < c) (hinv : (v * vinv) % p = 1) :
    ∀ k, ∀ j < power p k, ∀ j' < power p k,
      power (1 + c * p * v) j % (c * p * power p k) =
        power (1 + c * p * v) j' % (c * p * power p k) → j = j' := by
  have hp0 : 0 < p := by rw [hp]; exact lt_of_lt_of_le _root_.zero_lt_one (le_add_self)
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro j hj j' hj' _
    have h1 : j = 0 := by simpa using hj
    have h2 : j' = 0 := by simpa using hj'
    rw [h1, h2]
  case succ k ih =>
    intro j hj j' hj' heq
    set P := power p k with hPdef
    have hP : 0 < P := power_pos p k hp0
    have hM : 0 < c * p * P := mul_pos (mul_pos hc hp0) hP
    rw [power_succ p k] at hj hj' heq
    rw [← hPdef] at hj hj' heq
    have hjd : P * (j / P) + j % P = j := div_add_mod j P
    have hjd' : P * (j' / P) + j' % P = j' := div_add_mod j' P
    have hl : j / P < p := div_lt_of_lt_mul hj
    have hl' : j' / P < p := div_lt_of_lt_mul hj'
    obtain ⟨w, hw, hG⟩ := lte (c := c) (v := v) hp k
    obtain ⟨T, hT⟩ := decomp (c := c) (v := v) k (j % P) (j / P) w hG
    obtain ⟨T', hT'⟩ := decomp (c := c) (v := v) k (j' % P) (j' / P) w hG
    rw [← hPdef] at hT hT'
    rw [← hjd, hT] at heq
    rw [← hjd', hT'] at heq
    have hM' : 0 < c * p * P * p := mul_pos hM hp0
    rw [show c * p * (p * P) = c * p * P * p by ring] at heq
    have drop : ∀ a T0 : V, (a + c * p * P * p * T0) % (c * p * P * p) = a % (c * p * P * p) :=
      fun a T0 => mod_add_mul' _ _ hM'
    have low : ∀ (G L T0 : V),
        (G + c * p * P * L + c * p * P * p * T0) % (c * p * P) = G % (c * p * P) := by
      intro G L T0
      rw [show G + c * p * P * L + c * p * P * p * T0 = G + c * p * P * (L + p * T0) by ring]
      exact mod_add_mul' _ _ hM
    -- the low digits agree
    have hlow := congrArg (· % (c * p * P)) heq
    simp only [mod_of_mul_mod _ hM, low] at hlow
    have h0 : j % P = j' % P := ih (j % P) (mod_lt j hP) (j' % P) (mod_lt j' hP) hlow
    rw [← h0] at heq
    rw [drop, drop] at heq
    have h1 := add_cancel_mod hM' heq
    rw [mul_mod_mul hM hp0, mul_mod_mul hM hp0] at h1
    have h2 : (j / P * w) % p = (j' / P * w) % p := mul_cancel_left hM h1
    have hwinv : (w * vinv) % p = 1 := by
      rw [← mod_mul_mod_left w vinv hp0, hw, mod_mul_mod_left v vinv hp0, hinv]
    have recover : ∀ x, x < p → ((x * w) % p * vinv) % p = x := by
      intro x hx
      rw [mod_mul_mod_left _ _ hp0, mul_assoc, ← mod_mul_mod_right x _ hp0, hwinv, mul_one,
        mod_eq_self_of_lt hx]
    have h3 : j / P = j' / P := by rw [← recover _ hl, h2, recover _ hl']
    rw [← hjd, ← hjd', h0, h3]

end lift

end DiophantineConsistency.ArithmeticControllerLift
