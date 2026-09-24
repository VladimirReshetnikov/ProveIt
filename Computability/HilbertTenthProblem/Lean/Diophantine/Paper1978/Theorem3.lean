import Diophantine.Paper1978.Lemma35
import Diophantine.Paper1978.Lemma27
import Diophantine.Paper1978.Lemma28
import Diophantine.Paper1978.Lemma210

/-!
# Jones 1978, Theorem 3: the universal system (1.3)

> **Theorem 3.** For any positive integers `x` and `n`, in order that `x ∈ Wₙ`, it is
> necessary and sufficient that the system (1.3) of 36 equations have a solution in
> nonnegative integers (67 unknowns).

The 36 equations are the fields `e01`–`e36` of `Sys13`, written over `ℤ` with every unknown
a natural number (the article's convention "all variables are nonnegative integers", with
the equations read as integer identities; see the note on Q4 in `Lemma210.lean` for why the
integer reading matters).  The unknowns keep the article's letters, Greek letters spelled
out (`alpha … omega`, `pi'` for `π`, `phi1`/`phi2` for `φ`/`ϕ`, `lam` for `λ`, `eps` for `ε`).

Proof.  (⟸) (1.3) gives U1–U6 and the divisibility form of U8 directly ((07)–(09) with
`T ≡ t`, `P ≡ p (mod q)`); (10)–(25) are B1–B8, (26)–(33) are T1–T9 in the variant form,
(34)–(36) are Q2–Q4; Lemma 2.10 gives T0, the variant of Lemma 2.8 gives B0, Lemma 2.7
gives U0, and Lemma 3.5 gives `x ∈ Wₙ`.  (⟹) Lemma 3.5 gives U0–U8 with `(Z!)² ∣ r + 1` and
`r ≤ g`; Lemma 2.7, the variant of Lemma 2.8 and Lemma 2.10 supply the remaining unknowns.
-/

namespace Jones1978

open Finset Diophantine

/-! ### The polynomials `A`, `B` with `T`, `P` as free arguments -/

/-- `A(y)` with `T`, `P` free. -/
def Ap (R β y g s w : ℕ) (T P : ℤ) : ℤ :=
  (3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s - 2 * y) ^ 2 +
    (Mz β y ^ 2 * (1 + ((R : ℤ) - T - P) ^ 2) * ((β : ℤ) - T ^ 2 - P ^ 2) -
      ((R : ℤ) - T - P) ^ 2 - ((g : ℤ) + 1) * Mz β y ^ 2) ^ 2

/-- `B(y)` with `T`, `P` free. -/
def Bp (R β y g s w : ℕ) (T P : ℤ) : ℤ :=
  (3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s + 2 - 2 * y) ^ 2 +
    (Mz β y ^ 2 * (1 + ((R : ℤ) - T * P) ^ 2) * ((β : ℤ) - T ^ 2 - P ^ 2) -
      ((R : ℤ) - T * P) ^ 2 - ((g : ℤ) + 1) * Mz β y ^ 2) ^ 2

theorem Apoly_eq_Ap (R β y b e g s w : ℕ) :
    Apoly R β y b e g s w = Ap R β y g s w (Tz R β e s) (Tz R β b w) := rfl

theorem Bpoly_eq_Bp (R β y b e g s w : ℕ) :
    Bpoly R β y b e g s w = Bp R β y g s w (Tz R β e s) (Tz R β b w) := rfl

theorem Ap_nonneg (R β y g s w : ℕ) (T P : ℤ) : 0 ≤ Ap R β y g s w T P := by
  unfold Ap; positivity

theorem Bp_nonneg (R β y g s w : ℕ) (T P : ℤ) : 0 ≤ Bp R β y g s w T P := by
  unfold Bp; positivity

theorem Ap_modEq {R β y g s w : ℕ} {T P T' P' q : ℤ} (hT : T ≡ T' [ZMOD q]) (hP : P ≡ P' [ZMOD q]) :
    Ap R β y g s w T P ≡ Ap R β y g s w T' P' [ZMOD q] := by
  unfold Ap; gcongr

theorem Bp_modEq {R β y g s w : ℕ} {T P T' P' q : ℤ} (hT : T ≡ T' [ZMOD q]) (hP : P ≡ P' [ZMOD q]) :
    Bp R β y g s w T P ≡ Bp R β y g s w T' P' [ZMOD q] := by
  unfold Bp; gcongr

/-- The left side of (1.3.09), as printed. -/
def lhs09 (n r g s w alpha beta : ℕ) (t p : ℕ) : ℤ :=
  ((3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s - 2 * r) ^ 2 +
      ((1 + (beta : ℤ) + r * beta) ^ 2 * (1 + ((alpha : ℤ) - t - p) ^ 2) *
          ((beta : ℤ) - t ^ 2 - p ^ 2) -
        ((alpha : ℤ) - t - p) ^ 2 - ((g : ℤ) + 1) * (1 + (beta : ℤ) + r * beta) ^ 2) ^ 2) *
    ((3 * ((s : ℤ) + w) ^ 2 + 9 * w + 3 * s + 2 - 2 * r) ^ 2 +
      ((1 + (beta : ℤ) + r * beta) ^ 2 * (1 + ((alpha : ℤ) - t * p) ^ 2) *
          ((beta : ℤ) - t ^ 2 - p ^ 2) -
        ((alpha : ℤ) - t * p) ^ 2 - ((g : ℤ) + 1) * (1 + (beta : ℤ) + r * beta) ^ 2) ^ 2) *
    (3 * (g : ℤ) + 2 - r) * (3 * (n : ℤ) + g - r)

theorem lhs09_eq (n r g s w alpha beta t p : ℕ) :
    lhs09 n r g s w alpha beta t p =
      Ap alpha beta r g s w t p * Bp alpha beta r g s w t p * Cpoly g r * (3 * (n : ℤ) + g - r) := by
  unfold lhs09 Ap Bp Cpoly
  rw [show Mz beta r = 1 + (beta : ℤ) + r * beta by unfold Mz; ring]

/-! ### The system (1.3) -/

/-- The 36 equations of (1.3), over `ℤ`, in the 67 unknowns (all natural numbers). -/
structure Sys13 (n x : ℕ)
    (a b c d e f g h i j k l m p q r s t u v w y z : ℕ)
    (alpha beta gamma delta eps zeta eta theta iota kappa lam mu nu xi pi' rho sigma tau
      ups phi1 phi2 chi psi omega : ℕ)
    (a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' : ℕ) : Prop where
  e01 : (2 * n : ℤ) = ((u : ℤ) + v) ^ 2 + 3 * v + u
  e02 : (alpha : ℤ) = theta * beta + theta
  e03 : (h : ℤ) + h * beta + h * beta * v = x + rho + rho * beta + rho * beta * u
  e04 : ((h : ℤ) + h * beta + h * beta * v - alpha) ^ 2 + x ^ 2 + gamma + 1 = beta
  e05 : (z : ℤ) = 3 * n + alpha ^ 3
  e06 : (z : ℤ) ^ 18 * (z ^ 6 + 2) * (r + 1) ^ 2 + 1 = psi ^ 2
  e07 : (t : ℤ) + e + e * beta + e * beta * s = alpha + q * phi1
  e08 : (p : ℤ) + b + b * beta + b * beta * w = alpha + q * phi2
  e09 : lhs09 n r g s w alpha beta t p = q * pi'
  e10 : (omega : ℤ) = r + q + b + e + g + s + w + f' + g' + h' + i' + j'
  e11 : (omega : ℤ) ^ 3 * (omega + 2) * (sigma + 1) ^ 2 + 1 = delta ^ 2
  e12 : (eta : ℤ) = sigma * r + sigma
  e13 : (eta : ℤ) = b + (q' + sigma) * a'
  e14 : (eta : ℤ) = e + (r' + sigma) * b'
  e15 : (eta : ℤ) = g + (s' + sigma) * c'
  e16 : (eta : ℤ) = s + (t' + sigma) * d'
  e17 : (eta : ℤ) = w + (u' + sigma) * e'
  e18 : (eta : ℤ) ^ 3 * (eta + 2) * (zeta + 1) ^ 2 + 1 = eps ^ 2
  e19 : (chi : ℤ) = zeta * (eta - r) * (q' + sigma) * (r' + sigma) * (s' + sigma) *
    (t' + sigma) * (u' + sigma)
  e20 : (y : ℤ) = q + (1 + xi) * (eta - r)
  e21 : (y : ℤ) = q * f' + (q' + sigma) * k'
  e22 : (y : ℤ) = q * g' + (r' + sigma) * l'
  e23 : (y : ℤ) = q * h' + (s' + sigma) * m'
  e24 : (y : ℤ) = q * i' + (t' + sigma) * n'
  e25 : (y : ℤ) = q * j' + (u' + sigma) * p'
  e26 : ((mu : ℤ) ^ 2 - 1) * kappa ^ 2 + 1 = nu ^ 2
  e27 : ((mu : ℤ) ^ 2 * chi ^ 2 - 1) * lam ^ 2 + 1 = ups ^ 2
  e28 : 5 * ((c : ℤ) - kappa * lam * y) ^ 2 + iota = kappa ^ 2 * lam ^ 2
  e29 : (mu : ℤ) = 9 * eta * chi * y
  e30 : (kappa : ℤ) = eta - z + 1 + k * (mu - 1)
  e31 : (lam : ℤ) = z + 1 + l * (mu * chi - 1)
  e32 : (a : ℤ) = mu * chi + mu
  e33 : (c : ℤ) = m + eta + 1
  e34 : (d : ℤ) ^ 2 = (a ^ 2 - 1) * c ^ 2 + 1
  e35 : (f : ℤ) ^ 2 = 4 * (a ^ 2 - 1) * i ^ 2 * c ^ 4 + 1
  e36 : ((d : ℤ) + tau * f) ^ 2 = ((a + f ^ 2 * (f ^ 2 - a)) ^ 2 - 1) * (eta + 1 + 2 * j * c) ^ 2 + 1

/-! ### Auxiliary facts -/

/-- `z! + 6 < z⁶ − 1 + (z⁶)^(z⁶−2)` for `z ≥ 3`. -/
theorem factorial_add_six_lt {z : ℕ} (hz : 3 ≤ z) :
    z.factorial + 6 < z ^ 6 - 1 + (z ^ 6) ^ (z ^ 6 - 2) := by
  have h1 : z.factorial ≤ z ^ z := Nat.factorial_le_pow z
  have hz6 : 2 ≤ z ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hz 6)
  have h2 : (z ^ 6) ^ (z ^ 6 - 2) = z ^ (6 * (z ^ 6 - 2)) := by rw [← pow_mul]
  have h3 : z + 1 ≤ 6 * (z ^ 6 - 2) := by
    have : z ≤ z ^ 6 := Nat.le_self_pow (by norm_num) z
    omega
  have h4 : z ^ (z + 1) ≤ z ^ (6 * (z ^ 6 - 2)) := Nat.pow_le_pow_right (by omega) h3
  have h5 : 3 * z ^ z ≤ z ^ (z + 1) := by
    rw [pow_succ, mul_comm 3]; exact Nat.mul_le_mul_left _ hz
  have h6 : 3 ≤ z ^ z := le_trans hz (Nat.le_self_pow (by omega) z)
  omega

/-- `r ≥ Z! + 6` from U6 through Lemma 2.4. -/
theorem r_large {Z r : ℕ} (hZ : 3 ≤ Z)
    (U6 : IsSquare ((Z ^ 6) ^ 3 * (Z ^ 6 + 2) * (r + 1) ^ 2 + 1)) : Z.factorial + 6 < r := by
  obtain ⟨sq, hsq⟩ := U6
  have hJ2 : 2 ≤ Z ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hZ 6)
  have := JSWW1976.lemma_2_3 hJ2 hsq
  have := factorial_add_six_lt hZ
  omega

/-- `hM(v) ≥ x` under U3 and U4 (so that U3 can be written with a nonnegative quotient). -/
theorem hM_ge_x {x u v h R β : ℕ}
    (hU3 : (Mg β u : ℤ) ∣ h * Mg β v - x) (hU4 : (h * (Mg β v : ℤ) - R) ^ 2 + x ^ 2 < β) :
    (x : ℤ) ≤ h * Mg β v := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · -- `M(u) ∣ x` with `x < β < M(u)` forces `x = 0`
    simp only [Nat.cast_zero, zero_mul, zero_sub] at hU3 ⊢
    have hdvd : (Mg β u : ℤ) ∣ x := (dvd_neg).1 hU3
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · exfalso
      have hMx : (Mg β u : ℤ) ≤ x := Int.le_of_dvd (by exact_mod_cast hx) hdvd
      have := Mg_ge β u
      have hx1 : (1 : ℤ) ≤ x := by exact_mod_cast hx
      have : (x : ℤ) ≤ x ^ 2 := by nlinarith
      have := sq_nonneg ((0 : ℤ) * Mg β v - R)
      nlinarith
  · have hM := Mg_ge β v
    have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast hh
    have h1 : (1 + β : ℤ) ≤ h * Mg β v := by nlinarith
    have hxβ : (x : ℤ) ^ 2 < β := by have := sq_nonneg ((h : ℤ) * Mg β v - R); linarith
    have hx2 : (x : ℤ) ≤ x ^ 2 := by nlinarith
    linarith

/-! ### (1.3) ⟹ `x ∈ Wₙ` -/

set_option maxHeartbeats 1000000 in
/-- (01)–(09): U1–U4, U6 and the divisibility form of U8. -/
theorem sys13_U {n x : ℕ} (hx : 0 < x)
    {b e g h p q r s t u v w z alpha beta gamma theta pi' rho phi1 phi2 psi : ℕ}
    (e01 : (2 * n : ℤ) = ((u : ℤ) + v) ^ 2 + 3 * v + u)
    (e02 : (alpha : ℤ) = theta * beta + theta)
    (e03 : (h : ℤ) + h * beta + h * beta * v = x + rho + rho * beta + rho * beta * u)
    (e04 : ((h : ℤ) + h * beta + h * beta * v - alpha) ^ 2 + x ^ 2 + gamma + 1 = beta)
    (e05 : (z : ℤ) = 3 * n + alpha ^ 3)
    (e06 : (z : ℤ) ^ 18 * (z ^ 6 + 2) * (r + 1) ^ 2 + 1 = psi ^ 2)
    (e07 : (t : ℤ) + e + e * beta + e * beta * s = alpha + q * phi1)
    (e08 : (p : ℤ) + b + b * beta + b * beta * w = alpha + q * phi2)
    (e09 : lhs09 n r g s w alpha beta t p = q * pi') :
    J u v = n ∧ U234 x u v h alpha beta theta ∧ z = 3 * n + alpha ^ 3 ∧ 3 ≤ z ∧
      IsSquare ((z ^ 6) ^ 3 * (z ^ 6 + 2) * (r + 1) ^ 2 + 1) ∧
      (q : ℤ) ∣ Apoly alpha beta r b e g s w * Bpoly alpha beta r b e g s w * Cpoly g r *
        ((3 * n : ℤ) + g - r) := by
  have hJ : J u v = n := (pairing_eq_iff u v n).1 (by exact_mod_cast e01.symm)
  have hU2 : alpha = theta * (1 + beta) := by
    have : alpha = theta * beta + theta := by exact_mod_cast e02
    rw [this]; ring
  have hU3 : (Mg beta u : ℤ) ∣ h * Mg beta v - x :=
    ⟨rho, by rw [Mg_cast, Mg_cast]; linear_combination e03⟩
  have hU4 : (h * (Mg beta v : ℤ) - alpha) ^ 2 + x ^ 2 < beta := by
    rw [Mg_cast]
    have hg0 : (0 : ℤ) ≤ gamma := by positivity
    have : (h : ℤ) * (1 + (1 + v) * beta) = h + h * beta + h * beta * v := by ring
    rw [this]; linarith
  have hU : U234 x u v h alpha beta theta := ⟨hU2, hU3, hU4⟩
  obtain ⟨hβ2, hβR⟩ := sizes_of_U234 hx hU
  have hZ : z = 3 * n + alpha ^ 3 := by exact_mod_cast e05
  have hZ3 : 3 ≤ z := by
    have : 27 ≤ alpha ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ alpha ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hU6 : IsSquare ((z ^ 6) ^ 3 * (z ^ 6 + 2) * (r + 1) ^ 2 + 1) := by
    refine ⟨psi, ?_⟩
    have h6 : ((z : ℤ) ^ 6) ^ 3 * (z ^ 6 + 2) * (r + 1) ^ 2 + 1 = psi * psi := by
      rw [← pow_mul, show 6 * 3 = 18 by norm_num, e06]; ring
    exact_mod_cast h6
  have hT : Tz alpha beta e s = t - q * phi1 := by
    unfold Tz; rw [Mz_eq, Mg_cast]; linear_combination -e07
  have hP : Tz alpha beta b w = p - q * phi2 := by
    unfold Tz; rw [Mz_eq, Mg_cast]; linear_combination -e08
  have hU8 : (q : ℤ) ∣ Apoly alpha beta r b e g s w * Bpoly alpha beta r b e g s w * Cpoly g r *
      ((3 * n : ℤ) + g - r) := by
    rw [Apoly_eq_Ap, Bpoly_eq_Bp, hT, hP]
    have hTc : (t : ℤ) - q * phi1 ≡ t [ZMOD q] := Int.modEq_iff_dvd.2 ⟨phi1, by ring⟩
    have hPc : (p : ℤ) - q * phi2 ≡ p [ZMOD q] := Int.modEq_iff_dvd.2 ⟨phi2, by ring⟩
    have hc : Ap alpha beta r g s w (t - q * phi1) (p - q * phi2) *
        Bp alpha beta r g s w (t - q * phi1) (p - q * phi2) * Cpoly g r * ((3 * n : ℤ) + g - r) ≡
        Ap alpha beta r g s w t p * Bp alpha beta r g s w t p * Cpoly g r * ((3 * n : ℤ) + g - r)
        [ZMOD q] :=
      (((Ap_modEq hTc hPc).mul (Bp_modEq hTc hPc)).mul (Int.ModEq.refl _)).mul (Int.ModEq.refl _)
    have h0 : (q : ℤ) ∣ Ap alpha beta r g s w t p * Bp alpha beta r g s w t p * Cpoly g r *
        ((3 * n : ℤ) + g - r) := ⟨pi', by rw [← lhs09_eq]; exact e09⟩
    exact (Int.modEq_zero_iff_dvd).1 (hc.trans ((Int.modEq_zero_iff_dvd).2 h0))
  exact ⟨hJ, hU, hZ, hZ3, hU6, hU8⟩

set_option maxHeartbeats 2000000 in
/-- (10)–(25): B1–B8 (without B0) and the size facts. -/
theorem sys13_B {z r q b e g s w : ℕ}
    {omega sigma eta zeta chi y xi delta eps : ℕ}
    {a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' : ℕ}
    (hr : z.factorial + 6 < r)
    (e10 : (omega : ℤ) = r + q + b + e + g + s + w + f' + g' + h' + i' + j')
    (e11 : (omega : ℤ) ^ 3 * (omega + 2) * (sigma + 1) ^ 2 + 1 = delta ^ 2)
    (e12 : (eta : ℤ) = sigma * r + sigma)
    (e13 : (eta : ℤ) = b + (q' + sigma) * a')
    (e14 : (eta : ℤ) = e + (r' + sigma) * b')
    (e15 : (eta : ℤ) = g + (s' + sigma) * c')
    (e16 : (eta : ℤ) = s + (t' + sigma) * d')
    (e17 : (eta : ℤ) = w + (u' + sigma) * e')
    (e18 : (eta : ℤ) ^ 3 * (eta + 2) * (zeta + 1) ^ 2 + 1 = eps ^ 2)
    (e19 : (chi : ℤ) = zeta * (eta - r) * (q' + sigma) * (r' + sigma) * (s' + sigma) *
      (t' + sigma) * (u' + sigma))
    (e20 : (y : ℤ) = q + (1 + xi) * (eta - r))
    (e21 : (y : ℤ) = q * f' + (q' + sigma) * k')
    (e22 : (y : ℤ) = q * g' + (r' + sigma) * l')
    (e23 : (y : ℤ) = q * h' + (s' + sigma) * m')
    (e24 : (y : ℤ) = q * i' + (t' + sigma) * n')
    (e25 : (y : ℤ) = q * j' + (u' + sigma) * p') :
    (omega = r + q + ∑ i, ![b, e, g, s, w] i + ∑ i, ![f', g', h', i', j'] i) ∧
      IsSquare (omega ^ 3 * (omega + 2) * (sigma + 1) ^ 2 + 1) ∧
      eta = sigma * (r + 1) ∧
      (∀ i, eta ≡ ![b, e, g, s, w] i [MOD sigma + ![q', r', s', t', u'] i]) ∧
      IsSquare (eta ^ 3 * (eta + 2) * (zeta + 1) ^ 2 + 1) ∧
      chi = zeta * (eta - r) * ∏ i, (sigma + ![q', r', s', t', u'] i) ∧
      y = q + (xi + 1) * (eta - r) ∧
      (∀ i, y = q * ![f', g', h', i', j'] i + ![k', l', m', n', p'] i *
        (sigma + ![q', r', s', t', u'] i)) ∧
      z < eta ∧ 1 < y ∧ 8 * eta ^ z < chi := by
  have hB1 : omega = r + q + ∑ i, ![b, e, g, s, w] i + ∑ i, ![f', g', h', i', j'] i := by
    simp [Fin.sum_univ_five]
    have : omega = r + q + b + e + g + s + w + f' + g' + h' + i' + j' := by exact_mod_cast e10
    omega
  have hB2 : IsSquare (omega ^ 3 * (omega + 2) * (sigma + 1) ^ 2 + 1) := by
    refine ⟨delta, ?_⟩
    have : ((omega : ℤ) ^ 3 * (omega + 2) * (sigma + 1) ^ 2 + 1) = delta * delta := by
      rw [e11]; ring
    exact_mod_cast this
  have hB3 : eta = sigma * (r + 1) := by
    have : eta = sigma * r + sigma := by exact_mod_cast e12
    rw [this]; ring
  have hB5 : IsSquare (eta ^ 3 * (eta + 2) * (zeta + 1) ^ 2 + 1) := by
    refine ⟨eps, ?_⟩
    have : ((eta : ℤ) ^ 3 * (eta + 2) * (zeta + 1) ^ 2 + 1) = eps * eps := by
      rw [e18]; ring
    exact_mod_cast this
  -- `r < σ < η`
  have hrW : r ≤ omega := by
    have : omega = r + q + b + e + g + s + w + f' + g' + h' + i' + j' := by exact_mod_cast e10
    omega
  obtain ⟨xx, hxx⟩ := hB2
  have hσ : omega - 1 + omega ^ (omega - 2) ≤ sigma := JSWW1976.lemma_2_3 (by omega) hxx
  obtain ⟨xx', hxx'⟩ := hB5
  have hWpow : omega ≤ omega ^ (omega - 2) := Nat.le_self_pow (by omega) omega
  have hσ7 : 7 ≤ sigma := by omega
  have hζ : eta - 1 + eta ^ (eta - 2) ≤ zeta :=
    JSWW1976.lemma_2_3 (by rw [hB3]; nlinarith) hxx'
  have bd := bounds hr hrW hσ hB3 hζ
  have hrη : r ≤ eta := by have := bd.rσ; have := bd.σN; omega
  have hB6 : chi = zeta * (eta - r) * ∏ i, (sigma + ![q', r', s', t', u'] i) := by
    have : (chi : ℤ) = zeta * ((eta - r : ℕ) : ℤ) *
        (((sigma + q') * (sigma + r') * (sigma + s') * (sigma + t') * (sigma + u') : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hrη]; rw [e19]; ring
    simp [Fin.prod_univ_five]
    exact_mod_cast this
  have hB7 : y = q + (xi + 1) * (eta - r) := by
    have : (y : ℤ) = q + (xi + 1) * ((eta - r : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hrη]; rw [e20]; ring
    exact_mod_cast this
  obtain ⟨hzN, hY1, h8X, hrσ, hσN⟩ := sizes_of_B (zs := ![b, e, g, s, w])
    (b := ![f', g', h', i', j']) (d := ![q', r', s', t', u']) hr hB1 ⟨xx, hxx⟩ hB3 ⟨xx', hxx'⟩ hB6 hB7
  have hW' : omega = r + q + b + e + g + s + w + f' + g' + h' + i' + j' := by exact_mod_cast e10
  have hWσ : omega ≤ sigma := by omega
  have hB4 : ∀ i, eta ≡ ![b, e, g, s, w] i [MOD sigma + ![q', r', s', t', u'] i] := by
    intro i
    fin_cases i <;> simp
    · exact ((Nat.modEq_iff_dvd' (by omega)).2 ⟨a', by
        have : eta = b + (q' + sigma) * a' := by exact_mod_cast e13
        rw [this, Nat.add_sub_cancel_left]; ring⟩).symm
    · exact ((Nat.modEq_iff_dvd' (by omega)).2 ⟨b', by
        have : eta = e + (r' + sigma) * b' := by exact_mod_cast e14
        rw [this, Nat.add_sub_cancel_left]; ring⟩).symm
    · exact ((Nat.modEq_iff_dvd' (by omega)).2 ⟨c', by
        have : eta = g + (s' + sigma) * c' := by exact_mod_cast e15
        rw [this, Nat.add_sub_cancel_left]; ring⟩).symm
    · exact ((Nat.modEq_iff_dvd' (by omega)).2 ⟨d', by
        have : eta = s + (t' + sigma) * d' := by exact_mod_cast e16
        rw [this, Nat.add_sub_cancel_left]; ring⟩).symm
    · exact ((Nat.modEq_iff_dvd' (by omega)).2 ⟨e', by
        have : eta = w + (u' + sigma) * e' := by exact_mod_cast e17
        rw [this, Nat.add_sub_cancel_left]; ring⟩).symm
  have hB8 : ∀ i, y = q * ![f', g', h', i', j'] i +
      ![k', l', m', n', p'] i * (sigma + ![q', r', s', t', u'] i) := by
    intro i
    fin_cases i <;> simp
    · exact_mod_cast (show (y : ℤ) = q * f' + k' * (sigma + q') by rw [e21]; ring)
    · exact_mod_cast (show (y : ℤ) = q * g' + l' * (sigma + r') by rw [e22]; ring)
    · exact_mod_cast (show (y : ℤ) = q * h' + m' * (sigma + s') by rw [e23]; ring)
    · exact_mod_cast (show (y : ℤ) = q * i' + n' * (sigma + t') by rw [e24]; ring)
    · exact_mod_cast (show (y : ℤ) = q * j' + p' * (sigma + u') by rw [e25]; ring)
  exact ⟨hB1, ⟨xx, hxx⟩, hB3, hB4, ⟨xx', hxx'⟩, hB6, hB7, hB8, hzN, hY1, h8X⟩

set_option maxHeartbeats 1000000 in
/-- (26)–(36): T0–T9 in the variant form, with T0 from Lemma 2.10. -/
theorem sys13_T {a c d f i j k l m z eta chi y kappa lam mu nu ups iota tau : ℕ}
    (hzN : z < eta) (hy1 : 1 ≤ y) (hχ1 : 1 ≤ chi)
    (e26 : ((mu : ℤ) ^ 2 - 1) * kappa ^ 2 + 1 = nu ^ 2)
    (e27 : ((mu : ℤ) ^ 2 * chi ^ 2 - 1) * lam ^ 2 + 1 = ups ^ 2)
    (e28 : 5 * ((c : ℤ) - kappa * lam * y) ^ 2 + iota = kappa ^ 2 * lam ^ 2)
    (e29 : (mu : ℤ) = 9 * eta * chi * y)
    (e30 : (kappa : ℤ) = eta - z + 1 + k * (mu - 1))
    (e31 : (lam : ℤ) = z + 1 + l * (mu * chi - 1))
    (e32 : (a : ℤ) = mu * chi + mu)
    (e33 : (c : ℤ) = m + eta + 1)
    (e34 : (d : ℤ) ^ 2 = (a ^ 2 - 1) * c ^ 2 + 1)
    (e35 : (f : ℤ) ^ 2 = 4 * (a ^ 2 - 1) * i ^ 2 * c ^ 4 + 1)
    (e36 : ((d : ℤ) + tau * f) ^ 2 =
      ((a + f ^ 2 * (f ^ 2 - a)) ^ 2 - 1) * (eta + 1 + 2 * j * c) ^ 2 + 1) :
    TConds' eta z chi y k l m a (eta + 1) c kappa lam mu := by
  have hη1 : 1 ≤ eta := by omega
  have hμ : mu = 9 * eta * chi * y := by exact_mod_cast e29
  have hμ1 : 1 ≤ mu := by
    rw [hμ]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hη1) hχ1) hy1
  have hμχ1 : 1 ≤ mu * chi := Nat.mul_pos hμ1 hχ1
  have hA : a = mu * (chi + 1) := by
    have : a = mu * chi + mu := by exact_mod_cast e32
    rw [this]; ring
  have hA1 : 1 < a := by rw [hA]; nlinarith
  have hT1 : IsSquare ((mu * mu - 1) * kappa ^ 2 + 1) := by
    refine ⟨nu, ?_⟩
    have h1 : 1 ≤ mu * mu := Nat.mul_pos hμ1 hμ1
    have : (((mu * mu - 1 : ℕ) : ℤ)) * kappa ^ 2 + 1 = nu * nu := by
      push_cast [Nat.cast_sub h1]
      rw [show ((mu : ℤ) * mu - 1) * kappa ^ 2 + 1 = (mu ^ 2 - 1) * kappa ^ 2 + 1 by ring, e26]
      ring
    exact_mod_cast this
  have hT2 : IsSquare ((mu * chi * (mu * chi) - 1) * lam ^ 2 + 1) := by
    refine ⟨ups, ?_⟩
    have h1 : 1 ≤ mu * chi * (mu * chi) := Nat.mul_pos hμχ1 hμχ1
    have : (((mu * chi * (mu * chi) - 1 : ℕ) : ℤ)) * lam ^ 2 + 1 = ups * ups := by
      push_cast [Nat.cast_sub h1]
      rw [show ((mu : ℤ) * chi * (mu * chi) - 1) * lam ^ 2 + 1 =
        (mu ^ 2 * chi ^ 2 - 1) * lam ^ 2 + 1 by ring, e27]
      ring
    exact_mod_cast this
  have hT3 : 5 * ((c : ℤ) - kappa * lam * y) ^ 2 ≤ (kappa : ℤ) ^ 2 * lam ^ 2 := by
    have : (0 : ℤ) ≤ iota := by positivity
    linarith
  have hT5 : kappa = eta - z + 1 + k * (mu - 1) := by
    have : (kappa : ℤ) = ((eta - z : ℕ) : ℤ) + 1 + k * ((mu - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hzN.le, Nat.cast_sub hμ1]; rw [e30]
    exact_mod_cast this
  have hT6 : lam = z + 1 + l * (mu * chi - 1) := by
    have : (lam : ℤ) = z + 1 + l * ((mu * chi - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hμχ1]; rw [e31]
    exact_mod_cast this
  have hT9 : c = m + (eta + 1) := by
    have : c = m + eta + 1 := by exact_mod_cast e33
    omega
  have hA2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hQ : QConds a (eta + 1) c d f i j tau := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have : (d : ℤ) ^ 2 = ((a ^ 2 - 1 : ℕ) : ℤ) * c ^ 2 + 1 := by
        push_cast [Nat.cast_sub hA2]; exact e34
      exact_mod_cast this
    · have : (f : ℤ) ^ 2 = 4 * ((a ^ 2 - 1 : ℕ) : ℤ) * i ^ 2 * c ^ 4 + 1 := by
        push_cast [Nat.cast_sub hA2]; exact e35
      exact_mod_cast this
    · push_cast; exact e36
  have hT0 : ∀ hA' : 1 < a, c = ψ hA' (eta + 1) := fun hA' => psi_of_QConds hA' (by omega) hQ
  exact ⟨hT0, hT1, hT2, hT3, hμ, hT5, hT6, hA, rfl, hT9⟩

theorem mem_of_sys13 {n x : ℕ} (hn : 0 < n) (hx : 0 < x)
    {a b c d e f g h i j k l m p q r s t u v w y z : ℕ}
    {alpha beta gamma delta eps zeta eta theta iota kappa lam mu nu xi pi' rho sigma tau
      ups phi1 phi2 chi psi omega : ℕ}
    {a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' : ℕ}
    (S : Sys13 n x a b c d e f g h i j k l m p q r s t u v w y z alpha beta gamma delta eps zeta
      eta theta iota kappa lam mu nu xi pi' rho sigma tau ups phi1 phi2 chi psi omega
      a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u') : x ∈ W n := by
  obtain ⟨hJ, hU, hZ, hZ3, hU6, hU8⟩ :=
    sys13_U hx S.e01 S.e02 S.e03 S.e04 S.e05 S.e06 S.e07 S.e08 S.e09
  have hr := r_large hZ3 hU6
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hzN, hY1, h8X⟩ :=
    sys13_B hr S.e10 S.e11 S.e12 S.e13 S.e14 S.e15 S.e16 S.e17 S.e18 S.e19 S.e20 S.e21 S.e22
      S.e23 S.e24 S.e25
  have hTC := sys13_T hzN (by omega) (by omega) S.e26 S.e27 S.e28 S.e29 S.e30 S.e31 S.e32 S.e33
    S.e34 S.e35 S.e36
  have hzpos : 0 < z := by omega
  have hB0 : y = (chi + 1) ^ eta / chi ^ z := floor_of_TConds' hY1 h8X hzpos hzN hTC
  have hBC : BConds z r q ![b, e, g, s, w] omega sigma eta zeta chi y xi ![f', g', h', i', j']
      ![k', l', m', n', p'] ![q', r', s', t', u'] :=
    ⟨hB0, hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩
  obtain ⟨⟨hq, hqz⟩, -, -, -⟩ := lemma_2_7_of_B hr hBC
  have hq0 := hqz 0
  have hq1 := hqz 1
  have hq2 := hqz 2
  have hq3 := hqz 3
  have hq4 := hqz 4
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four] at hq0 hq1 hq2 hq3 hq4
  rw [hZ] at hq hq0 hq1 hq2 hq3 hq4 hU6
  exact mem_of_cond35' hn hx ⟨⟨hq, hq0, hq1, hq2, hq3, hq4⟩, hJ, hU, hU6, hU8⟩

/-! ### `x ∈ Wₙ` ⟹ (1.3) -/

/-- The nonnegative shift `t = T + qφ` of an integer `T`. -/
theorem exists_shift {q : ℕ} (hq : 1 ≤ q) (T : ℤ) : ∃ t phi : ℕ, (t : ℤ) = T + q * phi := by
  refine ⟨(T + q * T.natAbs).toNat, T.natAbs, ?_⟩
  have hq' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have h1 : -T ≤ (T.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs _
  have h2 : (T.natAbs : ℤ) ≤ q * T.natAbs := le_mul_of_one_le_left (by positivity) hq'
  rw [Int.toNat_of_nonneg (by linarith)]

set_option maxHeartbeats 4000000 in
theorem sys13_of_mem {n x : ℕ} (hn : 0 < n) (hx : 0 < x) (hW : x ∈ W n) :
    ∃ (a b c d e f g h i j k l m p q r s t u v w y z : ℕ)
      (alpha beta gamma delta eps zeta eta theta iota kappa lam mu nu xi pi' rho sigma tau
        ups phi1 phi2 chi psi omega : ℕ)
      (a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' : ℕ),
      Sys13 n x a b c d e f g h i j k l m p q r s t u v w y z alpha beta gamma delta eps zeta
        eta theta iota kappa lam mu nu xi pi' rho sigma tau ups phi1 phi2 chi psi omega
        a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' := by
  classical
  obtain ⟨b, e, g, h, q, r, s, u, v, w, β, π, θ, R, hc, hdvd2, hrg⟩ := cond35_of_mem' hn hx hW
  obtain ⟨hβ2, hβR⟩ := sizes_of_U234 hx hc.U234
  have hR3 : 3 ≤ R := by omega
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 3 * n + R ^ 3 := ⟨_, rfl⟩
  rw [← hZ] at hdvd2
  have hZ3 : 3 ≤ Z := by
    have : 27 ≤ R ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ R ^ 3 := Nat.pow_le_pow_left hR3 3
    omega
  have hU6 := hc.U6
  rw [← hZ] at hU6
  have hr := r_large hZ3 hU6
  have hdvd : Z.factorial ∣ r + 1 := (dvd_pow_self _ two_ne_zero).trans hdvd2
  have hU0 := hc.U0
  rw [← hZ] at hU0
  obtain ⟨hq, hqb, hqe, hqg, hqs, hqw⟩ := hU0
  have hU0' : U0 Z r q ![b, e, g, s, w] := by
    refine ⟨hq, fun i => ?_⟩
    fin_cases i <;> simp <;> assumption
  obtain ⟨W, σ, N, ζ, X, Y, ξ, bs, cs, ds, hBC⟩ := exists_B_of_U0 hr hdvd hU0'
  obtain ⟨-, hzN, hY1, h8X⟩ := lemma_2_7_of_B hr hBC
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, B8⟩ := hBC
  obtain ⟨-, -, -, hrσ, hσN⟩ := sizes_of_B hr B1 B2 B3 B5 B6 B7
  have hZpos : 0 < Z := by omega
  have hrN : r ≤ N := by omega
  have hrW : r ≤ W := by rw [B1]; omega
  have hWσ : W ≤ σ := by
    obtain ⟨xx, hxx⟩ := B2
    have := JSWW1976.lemma_2_3 (by omega) hxx
    have : W ≤ W ^ (W - 2) := Nat.le_self_pow (by omega) W
    omega
  obtain ⟨k, l, m, A, B, C, K, L, M, hTC⟩ := exists_TConds'_of_floor hY1 h8X hZpos hzN B0
  obtain ⟨T0, T1, T2, T3, T4, T5, T6, T7, T8, T9⟩ := hTC
  have hN1 : 1 ≤ N := by omega
  have hX1 : 1 ≤ X := by omega
  have hY1' : 1 ≤ Y := by omega
  have hM1 : 1 ≤ M := by
    rw [T4]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hN1) hX1) hY1'
  have hMX1 : 1 ≤ M * X := Nat.mul_pos hM1 hX1
  have hA1 : 1 < A := by rw [T7]; nlinarith
  have hC : C = ψ hA1 (N + 1) := by rw [T0 hA1, T8]
  obtain ⟨D, F, i, j, τ, hQ⟩ := exists_QConds_of_psi hA1 (show 0 < N + 1 by omega)
  rw [← hC] at hQ
  obtain ⟨Q1, Q2, Q3, Q4⟩ := hQ
  -- the auxiliary unknowns
  obtain ⟨hU2, hU3, hU4⟩ := hc.U234
  have hxle := hM_ge_x hU3 hU4
  obtain ⟨rho, hrho⟩ : ∃ rho : ℕ, (h : ℤ) * Mg β v - x = rho * Mg β u := by
    obtain ⟨ρ, hρ⟩ := hU3
    have hM : (0 : ℤ) < Mg β u := by exact_mod_cast Mg_pos β u
    have hρ0 : 0 ≤ ρ := by
      by_contra hneg
      push Not at hneg
      have : (Mg β u : ℤ) * ρ < 0 := mul_neg_of_pos_of_neg hM hneg
      linarith
    exact ⟨ρ.toNat, by rw [Int.toNat_of_nonneg hρ0, hρ]; ring⟩
  obtain ⟨gamma, hgamma⟩ : ∃ gamma : ℕ, (h * (Mg β v : ℤ) - R) ^ 2 + x ^ 2 + gamma + 1 = β := by
    have : (0 : ℤ) ≤ β - ((h * Mg β v - R) ^ 2 + x ^ 2) - 1 := by linarith
    exact ⟨((β : ℤ) - ((h * Mg β v - R) ^ 2 + x ^ 2) - 1).toNat, by
      rw [Int.toNat_of_nonneg this]; ring⟩
  obtain ⟨psi, hpsi⟩ := hU6
  obtain ⟨delta, hdelta⟩ := B2
  obtain ⟨eps, heps⟩ := B5
  obtain ⟨nu, hnu⟩ := T1
  obtain ⟨ups, hups⟩ := T2
  obtain ⟨iota, hiota⟩ : ∃ iota : ℕ, 5 * ((C : ℤ) - K * L * Y) ^ 2 + iota = K ^ 2 * L ^ 2 := by
    have : (0 : ℤ) ≤ K ^ 2 * L ^ 2 - 5 * ((C : ℤ) - K * L * Y) ^ 2 := by linarith
    exact ⟨((K : ℤ) ^ 2 * L ^ 2 - 5 * ((C : ℤ) - K * L * Y) ^ 2).toNat, by
      rw [Int.toNat_of_nonneg this]; ring⟩
  have hZr : Z ≤ r := by have := Nat.self_le_factorial Z; omega
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.choose_pos hZr
  obtain ⟨t, phi1, ht⟩ := exists_shift hq1 (Tz R β e s)
  obtain ⟨p, phi2, hp⟩ := exists_shift hq1 (Tz R β b w)
  -- π' from U8
  have hU8 := hc.U8
  rw [Apoly_eq_Ap, Bpoly_eq_Bp] at hU8
  obtain ⟨pi', hpi⟩ : ∃ pi' : ℕ, lhs09 n r g s w R β t p = q * pi' := by
    rw [lhs09_eq]
    have hTc : (t : ℤ) ≡ Tz R β e s [ZMOD q] := by
      rw [ht]; exact Int.modEq_iff_dvd.2 ⟨-phi1, by ring⟩
    have hPc : (p : ℤ) ≡ Tz R β b w [ZMOD q] := by
      rw [hp]; exact Int.modEq_iff_dvd.2 ⟨-phi2, by ring⟩
    have hcong : Ap R β r g s w t p * Bp R β r g s w t p * Cpoly g r * (3 * (n : ℤ) + g - r) ≡
        Ap R β r g s w (Tz R β e s) (Tz R β b w) * Bp R β r g s w (Tz R β e s) (Tz R β b w) *
          Cpoly g r * (3 * (n : ℤ) + g - r) [ZMOD q] :=
      (((Ap_modEq hTc hPc).mul (Bp_modEq hTc hPc)).mul (Int.ModEq.refl _)).mul (Int.ModEq.refl _)
    have hdiv : (q : ℤ) ∣ Ap R β r g s w t p * Bp R β r g s w t p * Cpoly g r *
        (3 * (n : ℤ) + g - r) :=
      (Int.modEq_zero_iff_dvd).1 (hcong.trans ((Int.modEq_zero_iff_dvd).2 ⟨π, hU8⟩))
    have hnn : 0 ≤ Ap R β r g s w t p * Bp R β r g s w t p * Cpoly g r * (3 * (n : ℤ) + g - r) := by
      have hrg' : (r : ℤ) ≤ g := by exact_mod_cast hrg
      have hC0 : 0 ≤ Cpoly g r := by unfold Cpoly; linarith
      have hD0 : 0 ≤ 3 * (n : ℤ) + g - r := by linarith
      have := Ap_nonneg R β r g s w t p
      have := Bp_nonneg R β r g s w t p
      positivity
    obtain ⟨π', hπ'⟩ := hdiv
    have hq1Z : (1 : ℤ) ≤ q := by exact_mod_cast hq1
    have hπ0 : 0 ≤ π' := by
      by_contra hneg
      push Not at hneg
      have : (q : ℤ) * π' < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
      linarith
    exact ⟨π'.toNat, by rw [Int.toNat_of_nonneg hπ0]; exact hπ'⟩
  -- the quotients `a'…e'` from B4
  have hziN : ∀ i, ![b, e, g, s, w] i ≤ N := by
    intro i
    have h1 : ![b, e, g, s, w] i ≤ ∑ i, ![b, e, g, s, w] i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have haa : ∀ i, ∃ ai, N = ![b, e, g, s, w] i + (σ + ds i) * ai := by
    intro i
    have := hziN i
    obtain ⟨ai, hai⟩ := (Nat.modEq_iff_dvd' (hziN i)).1 (B4 i).symm
    exact ⟨ai, by omega⟩
  choose aa haa using haa
  have haa0 : N = b + (σ + ds 0) * aa 0 := by have h' := haa 0; simpa using h'
  have haa1 : N = e + (σ + ds 1) * aa 1 := by have h' := haa 1; simpa using h'
  have haa2 : N = g + (σ + ds 2) * aa 2 := by have h' := haa 2; simpa using h'
  have haa3 : N = s + (σ + ds 3) * aa 3 := by have h' := haa 3; simpa using h'
  have haa4 : N = w + (σ + ds 4) * aa 4 := by have h' := haa 4; simpa using h'
  have hB8' := fun i => B8 i
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
  -- assemble
  refine ⟨A, b, C, D, e, F, g, h, i, j, k, l, m, p, q, r, s, t, u, v, w, Y, Z,
    R, β, gamma, delta, eps, ζ, N, θ, iota, K, L, M, nu, ξ, pi', rho, σ, τ, ups, phi1, phi2, X,
    psi, W, aa 0, aa 1, aa 2, aa 3, aa 4, bs 0, bs 1, bs 2, bs 3, bs 4,
    cs 0, cs 1, cs 2, cs 3, cs 4, ds 0, ds 1, ds 2, ds 3, ds 4, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (pairing_eq_iff u v n).2 hc.U1
    exact_mod_cast this.symm
  · rw [hU2]; push_cast; ring
  · rw [Mg_cast, Mg_cast] at hrho; linear_combination hrho
  · rw [Mg_cast] at hgamma; linear_combination hgamma
  · rw [hZ]; push_cast; ring
  · have h' : (((Z ^ 6) ^ 3 * (Z ^ 6 + 2) * (r + 1) ^ 2 + 1 : ℕ) : ℤ) = ((psi * psi : ℕ) : ℤ) := by
      rw [hpsi]
    push_cast at h'
    rw [← pow_mul] at h'
    norm_num at h'
    linear_combination h'
  · rw [ht]; unfold Tz; rw [Mz_eq, Mg_cast]; ring
  · rw [hp]; unfold Tz; rw [Mz_eq, Mg_cast]; ring
  · exact hpi
  · rw [B1]
    simp [Fin.sum_univ_five]
    ring
  · have h' := congrArg (Nat.cast : ℕ → ℤ) hdelta
    push_cast at h'
    linear_combination h'
  · rw [B3]; push_cast; ring
  · rw [haa0]; push_cast; ring
  · rw [haa1]; push_cast; ring
  · rw [haa2]; push_cast; ring
  · rw [haa3]; push_cast; ring
  · rw [haa4]; push_cast; ring
  · have h' := congrArg (Nat.cast : ℕ → ℤ) heps
    push_cast at h'
    linear_combination h'
  · rw [B6, Fin.prod_univ_five]
    push_cast [Nat.cast_sub hrN]; ring
  · rw [B7]; push_cast [Nat.cast_sub hrN]; ring
  · rw [hB8' 0]; push_cast; ring
  · rw [hB8' 1]; push_cast; ring
  · rw [hB8' 2]; push_cast; ring
  · rw [hB8' 3]; push_cast; ring
  · rw [hB8' 4]; push_cast; ring
  · have h' := congrArg (Nat.cast : ℕ → ℤ) hnu
    push_cast [Nat.cast_sub (Nat.mul_pos hM1 hM1 : 1 ≤ M * M)] at h'
    linear_combination h'
  · have h' := congrArg (Nat.cast : ℕ → ℤ) hups
    push_cast [Nat.cast_sub (Nat.mul_pos hMX1 hMX1 : 1 ≤ M * X * (M * X))] at h'
    linear_combination h'
  · exact hiota
  · rw [T4]; push_cast; ring
  · rw [T5]; push_cast [Nat.cast_sub hzN.le, Nat.cast_sub hM1]; ring
  · rw [T6]; push_cast [Nat.cast_sub hMX1]; ring
  · rw [T7]; push_cast; ring
  · rw [T9, T8]; push_cast; ring
  · have h' := congrArg (Nat.cast : ℕ → ℤ) Q2
    push_cast [Nat.cast_sub hA2] at h'
    linear_combination h'
  · have h' := congrArg (Nat.cast : ℕ → ℤ) Q3
    push_cast [Nat.cast_sub hA2] at h'
    linear_combination h'
  · have h' := Q4
    push_cast at h'
    linear_combination h'

/-- **Theorem 3.** For positive integers `x`, `n`: `x ∈ Wₙ` iff the system (1.3) has a
solution in nonnegative integers. -/
theorem theorem_3 {n x : ℕ} (hn : 0 < n) (hx : 0 < x) :
    x ∈ W n ↔ ∃ (a b c d e f g h i j k l m p q r s t u v w y z : ℕ)
      (alpha beta gamma delta eps zeta eta theta iota kappa lam mu nu xi pi' rho sigma tau
        ups phi1 phi2 chi psi omega : ℕ)
      (a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' : ℕ),
      Sys13 n x a b c d e f g h i j k l m p q r s t u v w y z alpha beta gamma delta eps zeta
        eta theta iota kappa lam mu nu xi pi' rho sigma tau ups phi1 phi2 chi psi omega
        a' b' c' d' e' f' g' h' i' j' k' l' m' n' p' q' r' s' t' u' := by
  constructor
  · exact sys13_of_mem hn hx
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, p, q, r, s, t, u, v, w, y, z, alpha, beta,
      gamma, delta, eps, zeta, eta, theta, iota, kappa, lam, mu, nu, xi, pi', rho, sigma, tau,
      ups, phi1, phi2, chi, psi, omega, a', b', c', d', e', f', g', h', i', j', k', l', m', n',
      p', q', r', s', t', u', S⟩
    exact mem_of_sys13 hn hx S

end Jones1978
