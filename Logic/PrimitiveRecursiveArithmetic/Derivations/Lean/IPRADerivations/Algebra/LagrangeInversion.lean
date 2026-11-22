import IPRADerivations.Algebra.TruncatedSeries
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# The Lagrange–Bürmann formulas for truncated series in iPRA

Packet: `algebra/lagrange_inversion_ipra`, `paper/lagrange_inversion_ipra.tex`, Section `sec:main`: for the
unique zero-constant solution of `G = Z Φ(G) (mod Z^{N+1})` (`Algebra/TruncatedSeries.fixed`, `unique`) and
`1 ≤ n ≤ N`,

* `cor:basic` (`eq:power`, cleared): `n [Zⁿ] G^k = k [W^{n−k}] Φⁿ` for `1 ≤ k ≤ n` (`power_formula_ring`), in
  particular `n [Zⁿ] G = [W^{n−1}] Φⁿ` (`eq:basic`);
* `thm:lb-der` (`eq:lb-der-cleared`): `n [Zⁿ] H(G) = [W^{n−1}] H'(W) Φ(W)ⁿ` (`lb_der`);
* `thm:lb-alt` (`eq:lb-alt`, multiplied by `n`): `n [Zⁿ] H(G) = n [Wⁿ] H Φ^{n−1} (Φ − W Φ')` (`lb_alt`), from
  the Leibniz identity `alt_identity`.

The proof is the "quantifier-free induction route" of the paper (Section "The induction proof encoded by the
finite construction"), with no residues: by strong induction on `n`, simultaneously in `k`,
`[Zⁿ] G^k = [Z^{n−k}] Φ^k(G)` by the fixed-point equation; for `m = n − k ≥ 1` the induction hypothesis turns
`m [Z^m] P(G)` into `[W^m] W P'(W) Φ^m` for every `P` (`comp_coeff_step`, by linearity in `P`), and
`[W^{m−1}] (Φⁿ)' = m [W^m] Φⁿ` closes the step after cancelling `m`. The cancellation is done over a
characteristic-zero domain; a generic `Φ` with indeterminate coefficients over `ℤ` (`genericPoly`) and evaluation
(`evalAt`) transport the identity to every commutative ring, in particular to the ring of iPRA integer terms of a
context. The iPRA statements (`ipra_power`, `ipra_basic`, `ipra_lb_der`, `ipra_lb_alt`) are equations between
coefficient terms of `ZPoly` expressions, for every fixed point `G` and every truncation order.
-/

namespace LeanProofs.IPRA.Algebra.LagrangeInversion

open Polynomial

/-! ## Polynomial algebra over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- The iterates `G^{(0)} = 0`, `G^{(r+1)} = X Φ(G^{(r)})`. -/
noncomputable def iterP (Φ : R[X]) : ℕ → R[X]
  | 0 => 0
  | r + 1 => X * Φ.comp (iterP Φ r)

theorem comp_sub_dvd (p a b : R[X]) : a - b ∣ p.comp a - p.comp b := by
  simpa [Polynomial.comp, eval₂_eq_eval_map] using sub_dvd_eval_sub a b (p.map C)

theorem improve_dvd {m : ℕ} (p a b : R[X]) (h : (X : R[X]) ^ m ∣ a - b) :
    (X : R[X]) ^ (m + 1) ∣ X * p.comp a - X * p.comp b := by
  rw [← _root_.mul_sub, _root_.pow_succ']
  exact mul_dvd_mul_left X (h.trans (comp_sub_dvd p a b))

theorem iterP_step (Φ : R[X]) (r : ℕ) : (X : R[X]) ^ r ∣ iterP Φ r - iterP Φ (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih => exact improve_dvd Φ _ _ ih

theorem iterP_fixed (Φ : R[X]) (N : ℕ) :
    (X : R[X]) ^ (N + 1) ∣ iterP Φ (N + 1) - X * Φ.comp (iterP Φ (N + 1)) :=
  iterP_step Φ (N + 1)

theorem iterP_map {S : Type*} [CommRing S] (f : R →+* S) (Φ : R[X]) (r : ℕ) :
    (iterP Φ r).map f = iterP (Φ.map f) r := by
  induction r with
  | zero => simp [iterP]
  | succ r ih => simp only [iterP, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_comp, ih]

theorem unique_dvd (p g g' : R[X]) (N : ℕ)
    (hg : (X : R[X]) ^ (N + 1) ∣ g - X * p.comp g) (hg' : (X : R[X]) ^ (N + 1) ∣ g' - X * p.comp g') :
    ∀ m ≤ N + 1, (X : R[X]) ^ m ∣ g - g' := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 : (X : R[X]) ^ (m + 1) ∣ g - X * p.comp g := (pow_dvd_pow X hm).trans hg
    have h2 : (X : R[X]) ^ (m + 1) ∣ g' - X * p.comp g' := (pow_dvd_pow X hm).trans hg'
    have h3 := improve_dvd p g g' (ih (by omega))
    have e : g - g' = (g - X * p.comp g) - (g' - X * p.comp g') + (X * p.comp g - X * p.comp g') := by ring
    rw [e]
    exact dvd_add (dvd_sub h1 h2) h3

theorem coeff_eq_of_dvd {N : ℕ} {a b : R[X]} (h : (X : R[X]) ^ (N + 1) ∣ a - b) {i : ℕ} (hi : i ≤ N) :
    a.coeff i = b.coeff i := by
  have := (X_pow_dvd_iff.mp h) i (by omega)
  rwa [coeff_sub, sub_eq_zero] at this

theorem coeff_zero_of_fixed {Φ G : R[X]} {N : ℕ} (hfix : (X : R[X]) ^ (N + 1) ∣ G - X * Φ.comp G) :
    G.coeff 0 = 0 := by
  rw [coeff_eq_of_dvd hfix (Nat.zero_le N), coeff_X_mul_zero]

theorem coeff_pow_of_lt {G : R[X]} (hG0 : G.coeff 0 = 0) {j m : ℕ} (h : m < j) : (G ^ j).coeff m = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hG0) j) m h

theorem X_mul_monomial (j : ℕ) (b : R) (hj : 1 ≤ j) : (X : R[X]) * monomial (j - 1) b = C b * X ^ j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← C_mul_X_pow_eq_monomial, _root_.pow_succ]
  ring

end Ring

/-! ## The power formula over a characteristic-zero domain -/

section Domain

variable {S : Type*} [CommRing S] [IsDomain S] [CharZero S]

/-- With the power formula at `m ≥ 1`, `m [X^m] P(G) = [X^m] X P' Φ^m` for every `P`. -/
theorem comp_coeff_step (Φ G : S[X]) (hG0 : G.coeff 0 = 0) {m : ℕ} (hm : 1 ≤ m)
    (ih : ∀ j, 1 ≤ j → j ≤ m → (m : S) * (G ^ j).coeff m = j * (Φ ^ m).coeff (m - j)) (P : S[X]) :
    (m : S) * (P.comp G).coeff m = (X * derivative P * Φ ^ m).coeff m := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, coeff_add, _root_.mul_add, hp, hq, derivative_add, _root_.mul_add, _root_.add_mul, coeff_add]
  | monomial j a =>
    rw [monomial_comp, coeff_C_mul, derivative_monomial]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have : m ≠ 0 := by omega
      simp [coeff_one, this]
    · rw [← _root_.mul_assoc, X_mul_monomial j _ hj,
        show C (a * (j : S)) * X ^ j * Φ ^ m = C (a * (j : S)) * (X ^ j * Φ ^ m) by ring,
        coeff_C_mul, coeff_X_pow_mul']
      by_cases hjm : j ≤ m
      · rw [if_pos hjm]
        have e := ih j hj hjm
        linear_combination a * e
      · rw [if_neg hjm, coeff_pow_of_lt hG0 (by omega)]
        ring

/-- `eq:power`, cleared: `n [Xⁿ] G^k = k [X^{n−k}] Φⁿ` for `1 ≤ k ≤ n ≤ N`. -/
theorem power_formula (Φ G : S[X]) (N : ℕ) (hfix : (X : S[X]) ^ (N + 1) ∣ G - X * Φ.comp G) :
    ∀ n ≤ N, ∀ k, 1 ≤ k → k ≤ n → (n : S) * (G ^ k).coeff n = k * (Φ ^ n).coeff (n - k) := by
  have hG0 := coeff_zero_of_fixed hfix
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro hn k hk hkn
  have hpow : (X : S[X]) ^ (N + 1) ∣ G ^ k - (X * Φ.comp G) ^ k :=
    hfix.trans ((Commute.all _ _).sub_dvd_pow_sub_pow k)
  have e1 : (G ^ k).coeff n = ((Φ ^ k).comp G).coeff (n - k) := by
    rw [coeff_eq_of_dvd hpow hn, _root_.mul_pow, ← pow_comp, coeff_X_pow_mul', if_pos hkn]
  rw [e1]
  rcases Nat.eq_zero_or_pos (n - k) with hm0 | hm
  · have hkn' : k = n := by omega
    rw [hm0, coeff_zero_eq_eval_zero, eval_comp, ← coeff_zero_eq_eval_zero G, hG0,
      ← coeff_zero_eq_eval_zero, hkn']
  · set m := n - k with hm_def
    have ih : ∀ j, 1 ≤ j → j ≤ m → (m : S) * (G ^ j).coeff m = j * (Φ ^ m).coeff (m - j) :=
      fun j hj hjm => IH m (by omega) (by omega) j hj hjm
    have step := comp_coeff_step Φ G hG0 hm ih (Φ ^ k)
    obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have hpk : Φ ^ (k - 1) * Φ ^ m = Φ ^ (n - 1) := by rw [← pow_add]; congr 1; omega
    have e2 : (X * derivative (Φ ^ k) * Φ ^ m).coeff m = (k : S) * (Φ ^ (n - 1) * derivative Φ).coeff i := by
      rw [derivative_pow]
      have : X * (C (k : S) * Φ ^ (k - 1) * derivative Φ) * Φ ^ m =
          C (k : S) * (X * (Φ ^ (n - 1) * derivative Φ)) := by
        rw [← hpk]; ring
      rw [this, coeff_C_mul, hi, coeff_X_mul]
    have e3 : (n : S) * (Φ ^ (n - 1) * derivative Φ).coeff i = m * (Φ ^ n).coeff m := by
      have d := coeff_derivative (Φ ^ n) i
      rw [derivative_pow, _root_.mul_assoc, coeff_C_mul] at d
      rw [d, hi]; push_cast; ring
    have hm0 : (m : S) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    apply mul_left_cancel₀ hm0
    calc (m : S) * (n * ((Φ ^ k).comp G).coeff m) = n * ((m : S) * ((Φ ^ k).comp G).coeff m) := by ring
      _ = n * (k * (Φ ^ (n - 1) * derivative Φ).coeff i) := by rw [step, e2]
      _ = k * (n * (Φ ^ (n - 1) * derivative Φ).coeff i) := by ring
      _ = k * (m * (Φ ^ n).coeff m) := by rw [e3]
      _ = m * (k * (Φ ^ n).coeff m) := by ring

end Domain

/-! ## Transport to an arbitrary commutative ring -/

section Transport

variable {R : Type*} [CommRing R]

/-- The generic polynomial `∑_{i<L} xᵢ Wⁱ` over `ℤ[x₀, …, x_{L−1}]`. -/
noncomputable def genericPoly (L : ℕ) : (MvPolynomial (Fin L) ℤ)[X] :=
  ∑ i : Fin L, C (MvPolynomial.X i) * X ^ (i : ℕ)

/-- Evaluation of the indeterminate coefficients at the coefficients of `Φ`. -/
noncomputable def evalAt (Φ : R[X]) (L : ℕ) : MvPolynomial (Fin L) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) fun i => Φ.coeff i

theorem map_generic (Φ : R[X]) : (genericPoly (Φ.natDegree + 1)).map (evalAt Φ _) = Φ := by
  simp only [genericPoly, evalAt, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (Φ.coeff i) * X ^ i) (Φ.natDegree + 1)]
  exact (as_sum_range_C_mul_X_pow Φ).symm

/-- `eq:power`, cleared, over every commutative ring and for every fixed point `G`. -/
theorem power_formula_ring (Φ G : R[X]) (N : ℕ) (hfix : (X : R[X]) ^ (N + 1) ∣ G - X * Φ.comp G) :
    ∀ n ≤ N, ∀ k, 1 ≤ k → k ≤ n → (n : R) * (G ^ k).coeff n = k * (Φ ^ n).coeff (n - k) := by
  intro n hn k hk hkn
  set L := Φ.natDegree + 1
  set ev := evalAt Φ L
  have hS := power_formula (genericPoly L) (iterP (genericPoly L) (N + 1)) N (iterP_fixed _ N) n hn k hk hkn
  have hmap : (iterP (genericPoly L) (N + 1)).map ev = iterP Φ (N + 1) := by
    rw [iterP_map, map_generic]
  have hG : (X : R[X]) ^ (N + 1) ∣ G - iterP Φ (N + 1) :=
    unique_dvd Φ _ _ N hfix (iterP_fixed Φ N) (N + 1) le_rfl
  have hGk : (X : R[X]) ^ (N + 1) ∣ G ^ k - iterP Φ (N + 1) ^ k :=
    hG.trans ((Commute.all _ _).sub_dvd_pow_sub_pow k)
  rw [coeff_eq_of_dvd hGk hn, ← hmap, ← Polynomial.map_pow, coeff_map, ← map_generic Φ,
    ← Polynomial.map_pow, coeff_map]
  have := congrArg ev hS
  simpa only [map_mul, map_natCast] using this

/-- `eq:basic`, cleared: `n [Xⁿ] G = [X^{n−1}] Φⁿ`. -/
theorem basic_ring (Φ G : R[X]) (N : ℕ) (hfix : (X : R[X]) ^ (N + 1) ∣ G - X * Φ.comp G) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : n ≤ N) : (n : R) * G.coeff n = (Φ ^ n).coeff (n - 1) := by
  have := power_formula_ring Φ G N hfix n hn 1 le_rfl hn1
  simpa using this

/-- `thm:lb-der`, `eq:lb-der-cleared`: `n [Xⁿ] H(G) = [X^{n−1}] H' Φⁿ`. -/
theorem lb_der (Φ G H : R[X]) (N : ℕ) (hfix : (X : R[X]) ^ (N + 1) ∣ G - X * Φ.comp G) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : n ≤ N) : (n : R) * (H.comp G).coeff n = (derivative H * Φ ^ n).coeff (n - 1) := by
  have hG0 := coeff_zero_of_fixed hfix
  induction H using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, coeff_add, _root_.mul_add, hp, hq, derivative_add, _root_.add_mul, coeff_add]
  | monomial j a =>
    rw [monomial_comp, coeff_C_mul, derivative_monomial]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have : n ≠ 0 := by omega
      simp [coeff_one, this]
    · rw [← C_mul_X_pow_eq_monomial, _root_.mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      by_cases hjn : j ≤ n
      · rw [if_pos (by omega), show n - 1 - (j - 1) = n - j by omega]
        have e := power_formula_ring Φ G N hfix n hn j hj hjn
        push_cast
        linear_combination a * e
      · rw [if_neg (by omega), coeff_pow_of_lt hG0 (by omega)]
        ring

/-- The Leibniz identity `[X^{n−1}] H' Φⁿ = n [Xⁿ] H Φ^{n−1} (Φ − X Φ')`. -/
theorem alt_identity (Φ H : R[X]) {n : ℕ} (hn1 : 1 ≤ n) :
    (derivative H * Φ ^ n).coeff (n - 1) = n * (H * Φ ^ (n - 1) * (Φ - X * derivative Φ)).coeff n := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have d := coeff_derivative (H * Φ ^ (i + 1)) i
  rw [derivative_mul, derivative_pow, coeff_add] at d
  have e : H * Φ ^ (i + 1 - 1) * (Φ - X * derivative Φ) =
      H * Φ ^ (i + 1) - X * (H * Φ ^ (i + 1 - 1) * derivative Φ) := by
    rw [Nat.add_sub_cancel, _root_.pow_succ]; ring
  have e' : H * (C ((i + 1 : ℕ) : R) * Φ ^ (i + 1 - 1) * derivative Φ) =
      C ((i + 1 : ℕ) : R) * (H * Φ ^ (i + 1 - 1) * derivative Φ) := by ring
  rw [e', coeff_C_mul] at d
  rw [e, coeff_sub, coeff_X_mul]
  simp only [Nat.add_sub_cancel] at d ⊢
  push_cast at d ⊢
  linear_combination d

/-- `thm:lb-alt`, multiplied by `n`: `n [Xⁿ] H(G) = n [Xⁿ] H Φ^{n−1} (Φ − X Φ')`. -/
theorem lb_alt (Φ G H : R[X]) (N : ℕ) (hfix : (X : R[X]) ^ (N + 1) ∣ G - X * Φ.comp G) {n : ℕ}
    (hn1 : 1 ≤ n) (hn : n ≤ N) :
    (n : R) * (H.comp G).coeff n = n * (H * Φ ^ (n - 1) * (Φ - X * derivative Φ)).coeff n := by
  rw [lb_der Φ G H N hfix hn1 hn, alt_identity Φ H hn1]

end Transport

/-! ## The iPRA statements -/

section IPRA

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.TruncatedSeries
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `p^k` on coefficient lists. -/
def pw (p : ZPoly n) : ℕ → ZPoly n
  | 0 => [ZT.natLit 1]
  | k + 1 => mul p (pw p k)

/-- The derivative on coefficient lists: `(c + X q)' = q + X q'`. -/
def deriv : ZPoly n → ZPoly n
  | [] => []
  | _ :: q => add q (shiftX (deriv q))

theorem toP_pw (p : ZPoly n) (k : ℕ) : toP Γ (pw p k) = toP Γ p ^ k := by
  induction k with
  | zero => simp [pw, toP, ZT.toZ_natLit]
  | succ k ih => rw [pw, toP_mul, ih, _root_.pow_succ']

theorem toP_deriv (p : ZPoly n) : toP Γ (deriv p) = derivative (toP Γ p) := by
  induction p with
  | nil => simp [deriv, toP]
  | cons c q ih =>
    rw [deriv, toP_add, toP_shiftX, ih, toP, derivative_add, derivative_C, derivative_mul, derivative_X]
    ring

theorem toP_fixed {Φ G : ZPoly n} {N : ℕ} (h : Γ ⊢[PRAAx] cong (N + 1) G (shiftX (comp Φ G))) :
    (X : (Groth (Q Γ))[X]) ^ (N + 1) ∣ toP Γ G - X * (toP Γ Φ).comp (toP Γ G) := by
  have d := dvd_of_cong h
  rwa [toP_shiftX, toP_comp] at d

/-- `eq:power`, cleared, as an iPRA equation: `n [Zⁿ] G^k = k [W^{n−k}] Φⁿ`. -/
theorem ipra_power {Φ G : ZPoly n} {N : ℕ} (h : Γ ⊢[PRAAx] cong (N + 1) G (shiftX (comp Φ G)))
    {m k : ℕ} (hm : m ≤ N) (hk : 1 ≤ k) (hkm : k ≤ m) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit m * coef (pw G k) m) (ZT.natLit k * coef (pw Φ m) (m - k)) := by
  apply ZT.derive
  rw [ZT.toZ_mul, ZT.toZ_mul, ZT.toZ_natLit, ZT.toZ_natLit, ← coeff_toP, ← coeff_toP, toP_pw, toP_pw]
  exact power_formula_ring _ _ N (toP_fixed h) m hm k hk hkm

/-- `eq:basic`, cleared, as an iPRA equation: `n [Zⁿ] G = [W^{n−1}] Φⁿ`. -/
theorem ipra_basic {Φ G : ZPoly n} {N : ℕ} (h : Γ ⊢[PRAAx] cong (N + 1) G (shiftX (comp Φ G)))
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ N) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit m * coef G m) (coef (pw Φ m) (m - 1)) := by
  apply ZT.derive
  rw [ZT.toZ_mul, ZT.toZ_natLit, ← coeff_toP, ← coeff_toP, toP_pw]
  exact basic_ring _ _ N (toP_fixed h) hm1 hm

/-- `thm:lb-der` as an iPRA equation: `n [Zⁿ] H(G) = [W^{n−1}] H' Φⁿ`. -/
theorem ipra_lb_der {Φ G : ZPoly n} (H : ZPoly n) {N : ℕ}
    (h : Γ ⊢[PRAAx] cong (N + 1) G (shiftX (comp Φ G))) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ N) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit m * coef (comp H G) m) (coef (mul (deriv H) (pw Φ m)) (m - 1)) := by
  apply ZT.derive
  rw [ZT.toZ_mul, ZT.toZ_natLit, ← coeff_toP, ← coeff_toP, toP_comp, toP_mul, toP_deriv, toP_pw]
  exact lb_der _ _ _ N (toP_fixed h) hm1 hm

/-- `thm:lb-alt`, multiplied by `n`, as an iPRA equation: `n [Zⁿ] H(G) = n [Wⁿ] H Φ^{n−1} (Φ − W Φ')`. -/
theorem ipra_lb_alt {Φ G : ZPoly n} (H : ZPoly n) {N : ℕ}
    (h : Γ ⊢[PRAAx] cong (N + 1) G (shiftX (comp Φ G))) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ N) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit m * coef (comp H G) m)
      (ZT.natLit m * coef (mul (mul H (pw Φ (m - 1)))
        (add Φ (smul (ZT.natLit 0 - ZT.natLit 1) (shiftX (deriv Φ))))) m) := by
  apply ZT.derive
  rw [ZT.toZ_mul, ZT.toZ_mul, ZT.toZ_natLit, ← coeff_toP, ← coeff_toP, toP_comp, toP_mul, toP_mul, toP_add,
    toP_smul, toP_shiftX, toP_deriv, toP_pw]
  have e := lb_alt _ _ (toP Γ H) N (toP_fixed h) hm1 hm
  rw [e]
  congr 2
  simp only [ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_zero, Nat.cast_one, zero_sub, map_neg, map_one]
  ring

end IPRA

end LeanProofs.IPRA.Algebra.LagrangeInversion
