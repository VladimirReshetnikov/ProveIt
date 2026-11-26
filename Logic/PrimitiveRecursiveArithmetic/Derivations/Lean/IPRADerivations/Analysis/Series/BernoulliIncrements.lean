import IPRADerivations.Analysis.Series.BernoulliBounds
import IPRADerivations.Analysis.RationalArithmetic.PowerIncrement

/-!
# Increment bounds for integer polynomials on `[0, 1]`, and the Bernoulli bounds on `ΔP_j`

Packet: `analysis/calculus_ipra`, `report.tex`, `eq:Pfinitebounds`: for `j ≤ r` and `0 ≤ t ≤ t + h ≤ 1`,
`|ΔP_j| ≤ D₁ h` and `|ΔP_j − h P_{j−1}(t)| ≤ D₂ h²` with `D₁ = r 2^r`, `D₂ = r² 2^r`, from `eq:coefbound` and the
monomial remainder `eq:monomialremainder`.

For integer coefficients `a_0, …, a_d`, a point `t = p/q` and a step `h = u/q` with `p + u ≤ q` (all cleared by
powers of `q`):

* `fv a p u q = Σ_i a_i ((p + u)^i − p^i) q^{d−i}` (`q^d ΔP`), and `first_upper`, `first_lower`:
  `|fv| ≤ S₁ u q^{d−1}` whenever `Σ_i |a_i| i ≤ S₁`, from `power_diff` and `gd_le`;
* `tv a p u q = Σ_i a_i ((p + u)^i − p^i − i u p^{i−1}) q^{d−i}` (`q^d (ΔP − h P′(t))`), and `second_upper`,
  `second_lower`: `|2q · tv| ≤ S₂ u² q^{d−1}` whenever `Σ_i |a_i| (i − 1) i ≤ S₂`, from `power_inc_lower` and
  `power_inc_upper`;
* `bernoulli_step`, `bernoulli_second`: the instances at the cleared Bernoulli coefficients `bint j`, with
  `S₁ = D_j 2^r r`, `S₂ = D_j 2^r r²`, i.e. `|ΔP_j| ≤ r 2^r h` and `|ΔP_j − h P_j′(t)| ≤ (r² 2^r/2) h²`;
* `bint_deriv`: `(k + 1) · bint (j+1) (k+1) = D_{j+1} · bc j k`, i.e. `P_{j+1}′ = P_j` coefficientwise, so the
  derivative term of `tv` is `h P_{j−1}(t)` (cleared by `D_j`).

Each bound is an integer certificate (`Core/IntCertificates.zle_of_comb`): a sum over the coefficients of natural
slacks, chosen by the sign of the coefficient (`zf`, `zs`), plus the unused part of the budget `S`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BernoulliIncrements

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BernoulliCoefficients (bc bc_deriv)
open LeanProofs.IPRA.Analysis.BernoulliBounds (zint toZ_zint qsplit natAbs_cast_of_nonneg natAbs_cast_of_neg
  bden bint bint_eq bint_abs_sum)
open LeanProofs.IPRA.Algebra.PowerDifference (gd power_diff gd_le)
open LeanProofs.IPRA.Analysis.PowerIncrement (power_inc_lower power_inc_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Assembling a certificate from its terms -/

theorem cert_sub {R ι : Type*} [CommRing R] (s : Finset ι) (Z T N : ι → R) (W K Sg : R)
    (h : ∀ i ∈ s, N i * W - K * T i = Z i) :
    Sg * W - K * ∑ i ∈ s, T i = ∑ i ∈ s, Z i + (Sg - ∑ i ∈ s, N i) * W := by
  rw [← Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]; ring

theorem cert_add {R ι : Type*} [CommRing R] (s : Finset ι) (Z T N : ι → R) (W K Sg : R)
    (h : ∀ i ∈ s, K * T i + N i * W = Z i) :
    K * ∑ i ∈ s, T i + Sg * W = ∑ i ∈ s, Z i + (Sg - ∑ i ∈ s, N i) * W := by
  rw [← Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]; ring

section Inc

variable {d : ℕ} (a : Fin (d + 1) → ℤ)

/-- `q^d ΔP = Σ_i a_i ((p + u)^i − p^i) q^{d−i}`. -/
def fv (p u q : PTm n) : ZT n :=
  ZT.sumFin fun i => zint (a i) *
    ((ZT.ofNat (pw (p + u) (num i)) - ZT.ofNat (pw p (num i))) * ZT.ofNat (pw q (num (d - i))))

/-- `q^d (ΔP − h P′(t)) = Σ_i a_i ((p + u)^i − p^i − i u p^{i−1}) q^{d−i}`. -/
def tv (p u q : PTm n) : ZT n :=
  ZT.sumFin fun i => zint (a i) *
    ((ZT.ofNat (pw (p + u) (num i)) - ZT.ofNat (pw p (num i)) - ZT.ofNat (num i * pw p (num (i - 1)) * u)) *
      ZT.ofNat (pw q (num (d - i))))

/-- `q^{d−1} = q^k q^{d−(k+1)}` for `k + 1 ≤ d`. -/
theorem qsplit1 (k : ℕ) (hk : k + 1 ≤ d) (q : PTm n) :
    Groth.ι (Q.mk Γ (pw q (num (d - 1)))) =
      Groth.ι (Q.mk Γ (pw q (num k))) * Groth.ι (Q.mk Γ (pw q (num (d - (k + 1))))) := by
  have e := natEq (qsplit (Γ := Γ) (d - 1) k (by omega) q)
  simp only [Q.mk_mul, map_mul] at e
  rw [e, show d - 1 - k = d - (k + 1) by omega]

/-! ### The first-order increment -/

/-- `gd_le` in the `num (k + 1)` form. -/
theorem gd_le' {p u q : PTm n} (k : ℕ) (hR : Γ ⊢[PRAAx] le (p + u) q) (hp : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (gd (p + u) p (num (k + 1))) (num (k + 1) * pw q (num k)) :=
  gd_le (num k) hR hp

/-- The per-coefficient certificate of `first_upper`. -/
noncomputable def zf {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) (hp : Γ ⊢[PRAAx] le p q) :
    ℕ → ℤ → Groth (Q Γ)
  | 0, _ => 0
  | k + 1, c =>
    if 0 ≤ c then (c.natAbs : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw q (num (d - (k + 1))))) * Groth.ι (Q.mk Γ u) *
        sl (gd_le' k hR hp)
    else (c.natAbs : Groth (Q Γ)) * (((k + 1 : ℕ) : Groth (Q Γ)) * Groth.ι (Q.mk Γ u) *
        Groth.ι (Q.mk Γ (pw q (num (d - 1)))) + Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (gd (p + u) p (num (k + 1)))) *
        Groth.ι (Q.mk Γ (pw q (num (d - (k + 1))))))

theorem zf_nn {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) (hp : Γ ⊢[PRAAx] le p q) (j : ℕ) (c : ℤ) :
    Nonneg Γ (zf (d := d) hR hp j c) := by
  cases j with
  | zero => exact nn_zero
  | succ k =>
    simp only [zf]
    split_ifs
    · exact nn_mul (nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_term _)) (nn_sl _)
    · exact nn_mul (nn_natCast _) (nn_add (nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_term _))
        (nn_mul (nn_mul (nn_term _) (nn_term _)) (nn_term _)))

theorem zf_eq {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) (hp : Γ ⊢[PRAAx] le p q) (i : ℕ) (hi : i < d + 1)
    (c : ℤ) :
    ((c.natAbs : Groth (Q Γ)) * (i : Groth (Q Γ))) *
        (Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) -
      1 * ((c : Groth (Q Γ)) * ((Groth.ι (Q.mk Γ (pw (p + u) (num i))) - Groth.ι (Q.mk Γ (pw p (num i)))) *
          Groth.ι (Q.mk Γ (pw q (num (d - i)))))) = zf (d := d) hR hp i c := by
  cases i with
  | zero =>
    have e0 := natEq (pw_zero (Γ := Γ) (p + u)); have e1 := natEq (pw_zero (Γ := Γ) p)
    simp only [zf, num, Nat.cast_zero, mul_zero, zero_mul] at e0 e1 ⊢
    rw [e0, e1]; ring
  | succ k =>
    have hk : k + 1 ≤ d := by omega
    have pd := natEq (power_diff (Γ := Γ) (p + u) p (num (k + 1)))
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at pd
    have qs := qsplit1 (Γ := Γ) k hk q
    simp only [zf]
    split_ifs with hc
    · rw [natAbs_cast_of_nonneg hc, sl_def, qs]
      simp only [Q.mk_mul, Q.mk_num, map_mul, map_natCast]
      linear_combination (-(c : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw q (num (d - (k + 1)))))) * pd
    · rw [natAbs_cast_of_neg (lt_of_not_ge hc), qs]
      linear_combination (-(c : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw q (num (d - (k + 1)))))) * pd

theorem zf_eq_neg {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) (hp : Γ ⊢[PRAAx] le p q) (i : ℕ)
    (hi : i < d + 1) (c : ℤ) :
    1 * ((c : Groth (Q Γ)) * ((Groth.ι (Q.mk Γ (pw (p + u) (num i))) - Groth.ι (Q.mk Γ (pw p (num i)))) *
        Groth.ι (Q.mk Γ (pw q (num (d - i)))))) +
      ((c.natAbs : Groth (Q Γ)) * (i : Groth (Q Γ))) *
        (Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) = zf (d := d) hR hp i (-c) := by
  have h := zf_eq (d := d) hR hp i hi (-c)
  rw [Int.natAbs_neg] at h
  rw [← h]; push_cast; ring

/-- `|ΔP| ≤ S₁ h` on `[0, 1]`: `Σ a_i ((p + u)^i − p^i) q^{d−i} ≤ S₁ u q^{d−1}`. -/
theorem first_upper {S : ℕ} (hS : ∑ i : Fin (d + 1), (a i).natAbs * (i : ℕ) ≤ S) {p u q : PTm n}
    (hR : Γ ⊢[PRAAx] le (p + u) q) :
    Γ ⊢[PRAAx] zle (fv a p u q) (ZT.ofNat (num S * u * pw q (num (d - 1)))) := by
  have hp : Γ ⊢[PRAAx] le p q := le_trans (le_add_right p u) hR
  have key := cert_sub Finset.univ (Z := fun i : Fin (d + 1) => zf (d := d) hR hp i (a i))
    (N := fun i : Fin (d + 1) => ((a i).natAbs : Groth (Q Γ)) * ((i : ℕ) : Groth (Q Γ)))
    (W := Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) (K := 1) (Sg := (S : Groth (Q Γ)))
    (T := _) (h := fun i _ => zf_eq hR hp i i.isLt (a i))
  refine zle_of_comb ((∑ i : Fin (d + 1), zf (d := d) hR hp i (a i)) +
    ((S - ∑ i : Fin (d + 1), (a i).natAbs * (i : ℕ) : ℕ) : Groth (Q Γ)) * Groth.ι (Q.mk Γ u) *
      Groth.ι (Q.mk Γ (pw q (num (d - 1))))) ?_
    (nn_add (nn_sum _ _ fun i _ => zf_nn hR hp _ _) (nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_term _)))
  simp only [fv, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_sub, toZ_zint, ZT.toZ_ofNat, Q.mk_mul, map_mul, Q.mk_num,
    map_natCast]
  rw [Nat.cast_sub hS, Nat.cast_sum]
  push_cast
  linear_combination key

/-- `−S₁ u q^{d−1} ≤ Σ a_i ((p + u)^i − p^i) q^{d−i}`. -/
theorem first_lower {S : ℕ} (hS : ∑ i : Fin (d + 1), (a i).natAbs * (i : ℕ) ≤ S) {p u q : PTm n}
    (hR : Γ ⊢[PRAAx] le (p + u) q) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (num S * u * pw q (num (d - 1)))) (fv a p u q) := by
  have hp : Γ ⊢[PRAAx] le p q := le_trans (le_add_right p u) hR
  have key := cert_add Finset.univ (Z := fun i : Fin (d + 1) => zf (d := d) hR hp i (-a i))
    (N := fun i : Fin (d + 1) => ((a i).natAbs : Groth (Q Γ)) * ((i : ℕ) : Groth (Q Γ)))
    (W := Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) (K := 1) (Sg := (S : Groth (Q Γ)))
    (T := _) (h := fun i _ => zf_eq_neg hR hp i i.isLt (a i))
  refine zle_of_comb ((∑ i : Fin (d + 1), zf (d := d) hR hp i (-a i)) +
    ((S - ∑ i : Fin (d + 1), (a i).natAbs * (i : ℕ) : ℕ) : Groth (Q Γ)) * Groth.ι (Q.mk Γ u) *
      Groth.ι (Q.mk Γ (pw q (num (d - 1))))) ?_
    (nn_add (nn_sum _ _ fun i _ => zf_nn hR hp _ _) (nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_term _)))
  simp only [fv, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, toZ_zint, ZT.toZ_ofNat, Q.mk_mul, map_mul,
    Q.mk_num, map_natCast]
  rw [Nat.cast_sub hS, Nat.cast_sum]
  push_cast
  linear_combination key

/-! ### The second-order increment -/

/-- `power_inc_upper` at `R = q` in the `num (k + 1)` form. -/
theorem inc_up {p u q : PTm n} (k : ℕ) (hR : Γ ⊢[PRAAx] le (p + u) q) :
    Γ ⊢[PRAAx] le (two * q * pw (p + u) (num (k + 1)))
      (two * q * (pw p (num (k + 1)) + num (k + 1) * pw p (num k) * u) + num k * num (k + 1) * pw q (num k) * (u * u)) :=
  power_inc_upper (num k) hR

/-- `power_inc_lower` in the `num (k + 1)` form. -/
theorem inc_lo (p u : PTm n) (k : ℕ) :
    Γ ⊢[PRAAx] le (pw p (num (k + 1)) + num (k + 1) * pw p (num k) * u) (pw (p + u) (num (k + 1))) :=
  power_inc_lower p u (num k)

/-- The per-coefficient certificate of `second_upper`. -/
noncomputable def zs {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) : ℕ → ℤ → Groth (Q Γ)
  | 0, _ => 0
  | k + 1, c =>
    if 0 ≤ c then (c.natAbs : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw q (num (d - (k + 1))))) * sl (inc_up k hR)
    else (c.natAbs : Groth (Q Γ)) * ((k : Groth (Q Γ)) * ((k + 1 : ℕ) : Groth (Q Γ)) *
        (Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ u)) * Groth.ι (Q.mk Γ (pw q (num (d - 1)))) +
        Groth.ι (Q.mk Γ two) * Groth.ι (Q.mk Γ q) * Groth.ι (Q.mk Γ (pw q (num (d - (k + 1))))) *
          sl (inc_lo p u k))

theorem zs_nn {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) (j : ℕ) (c : ℤ) : Nonneg Γ (zs (d := d) hR j c) := by
  cases j with
  | zero => exact nn_zero
  | succ k =>
    simp only [zs]
    split_ifs
    · exact nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_sl _)
    · exact nn_mul (nn_natCast _) (nn_add
        (nn_mul (nn_mul (nn_mul (nn_natCast _) (nn_natCast _)) (nn_mul (nn_term _) (nn_term _))) (nn_term _))
        (nn_mul (nn_mul (nn_mul (nn_term _) (nn_term _)) (nn_term _)) (nn_sl _)))

theorem zs_eq {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) (i : ℕ) (hi : i < d + 1) (c : ℤ) :
    ((c.natAbs : Groth (Q Γ)) * ((i - 1 : ℕ) : Groth (Q Γ)) * (i : Groth (Q Γ))) *
        (Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) -
      (Groth.ι (Q.mk Γ two) * Groth.ι (Q.mk Γ q)) * ((c : Groth (Q Γ)) *
        ((Groth.ι (Q.mk Γ (pw (p + u) (num i))) - Groth.ι (Q.mk Γ (pw p (num i))) -
          (i : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw p (num (i - 1)))) * Groth.ι (Q.mk Γ u)) *
        Groth.ι (Q.mk Γ (pw q (num (d - i)))))) = zs (d := d) hR i c := by
  cases i with
  | zero =>
    have e0 := natEq (pw_zero (Γ := Γ) (p + u)); have e1 := natEq (pw_zero (Γ := Γ) p)
    simp only [zs, num, Nat.cast_zero, Nat.zero_sub, mul_zero, zero_mul] at e0 e1 ⊢
    rw [e0, e1]; ring
  | succ k =>
    have hk : k + 1 ≤ d := by omega
    have qs := qsplit1 (Γ := Γ) k hk q
    simp only [zs, Nat.add_sub_cancel]
    split_ifs with hc
    · rw [natAbs_cast_of_nonneg hc, sl_def, qs]
      simp only [Q.mk_add, Q.mk_mul, Q.mk_num, map_add, map_mul, map_natCast]
      ring
    · rw [natAbs_cast_of_neg (lt_of_not_ge hc), sl_def, qs]
      simp only [Q.mk_add, Q.mk_mul, Q.mk_num, map_add, map_mul, map_natCast]
      ring

theorem zs_eq_neg {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) (i : ℕ) (hi : i < d + 1) (c : ℤ) :
    (Groth.ι (Q.mk Γ two) * Groth.ι (Q.mk Γ q)) * ((c : Groth (Q Γ)) *
        ((Groth.ι (Q.mk Γ (pw (p + u) (num i))) - Groth.ι (Q.mk Γ (pw p (num i))) -
          (i : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw p (num (i - 1)))) * Groth.ι (Q.mk Γ u)) *
        Groth.ι (Q.mk Γ (pw q (num (d - i)))))) +
      ((c.natAbs : Groth (Q Γ)) * ((i - 1 : ℕ) : Groth (Q Γ)) * (i : Groth (Q Γ))) *
        (Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) =
      zs (d := d) hR i (-c) := by
  have h := zs_eq (d := d) hR i hi (-c)
  rw [Int.natAbs_neg] at h
  rw [← h]; push_cast; ring

/-- `2q · q^d (ΔP − h P′(t)) ≤ S₂ u² q^{d−1}`. -/
theorem second_upper {S : ℕ} (hS : ∑ i : Fin (d + 1), (a i).natAbs * ((i : ℕ) - 1) * (i : ℕ) ≤ S) {p u q : PTm n}
    (hR : Γ ⊢[PRAAx] le (p + u) q) :
    Γ ⊢[PRAAx] zle (ZT.ofNat (two * q) * tv a p u q) (ZT.ofNat (num S * (u * u) * pw q (num (d - 1)))) := by
  have key := cert_sub Finset.univ (Z := fun i : Fin (d + 1) => zs (d := d) hR i (a i))
    (N := fun i : Fin (d + 1) => ((a i).natAbs : Groth (Q Γ)) * (((i : ℕ) - 1 : ℕ) : Groth (Q Γ)) *
      ((i : ℕ) : Groth (Q Γ)))
    (W := Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1)))))
    (K := Groth.ι (Q.mk Γ two) * Groth.ι (Q.mk Γ q)) (Sg := (S : Groth (Q Γ)))
    (T := _) (h := fun i _ => zs_eq hR i i.isLt (a i))
  refine zle_of_comb ((∑ i : Fin (d + 1), zs (d := d) hR i (a i)) +
    ((S - ∑ i : Fin (d + 1), (a i).natAbs * ((i : ℕ) - 1) * (i : ℕ) : ℕ) : Groth (Q Γ)) *
      (Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ u)) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) ?_
    (nn_add (nn_sum _ _ fun i _ => zs_nn hR _ _)
      (nn_mul (nn_mul (nn_natCast _) (nn_mul (nn_term _) (nn_term _))) (nn_term _)))
  simp only [tv, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_sub, toZ_zint, ZT.toZ_ofNat, Q.mk_mul, map_mul, Q.mk_num,
    map_natCast]
  rw [Nat.cast_sub hS, Nat.cast_sum]
  push_cast
  linear_combination key

/-- `−S₂ u² q^{d−1} ≤ 2q · q^d (ΔP − h P′(t))`. -/
theorem second_lower {S : ℕ} (hS : ∑ i : Fin (d + 1), (a i).natAbs * ((i : ℕ) - 1) * (i : ℕ) ≤ S) {p u q : PTm n}
    (hR : Γ ⊢[PRAAx] le (p + u) q) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (num S * (u * u) * pw q (num (d - 1)))) (ZT.ofNat (two * q) * tv a p u q) := by
  have key := cert_add Finset.univ (Z := fun i : Fin (d + 1) => zs (d := d) hR i (-a i))
    (N := fun i : Fin (d + 1) => ((a i).natAbs : Groth (Q Γ)) * (((i : ℕ) - 1 : ℕ) : Groth (Q Γ)) *
      ((i : ℕ) : Groth (Q Γ)))
    (W := Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ (pw q (num (d - 1)))))
    (K := Groth.ι (Q.mk Γ two) * Groth.ι (Q.mk Γ q)) (Sg := (S : Groth (Q Γ)))
    (T := _) (h := fun i _ => zs_eq_neg hR i i.isLt (a i))
  refine zle_of_comb ((∑ i : Fin (d + 1), zs (d := d) hR i (-a i)) +
    ((S - ∑ i : Fin (d + 1), (a i).natAbs * ((i : ℕ) - 1) * (i : ℕ) : ℕ) : Groth (Q Γ)) *
      (Groth.ι (Q.mk Γ u) * Groth.ι (Q.mk Γ u)) * Groth.ι (Q.mk Γ (pw q (num (d - 1))))) ?_
    (nn_add (nn_sum _ _ fun i _ => zs_nn hR _ _)
      (nn_mul (nn_mul (nn_natCast _) (nn_mul (nn_term _) (nn_term _))) (nn_term _)))
  simp only [tv, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_neg, toZ_zint, ZT.toZ_ofNat, Q.mk_mul, map_mul,
    Q.mk_num, map_natCast]
  rw [Nat.cast_sub hS, Nat.cast_sum]
  push_cast
  linear_combination key

end Inc

/-! ## The Bernoulli instances -/

theorem bint_first_sum (j r : ℕ) (hj : j ≤ r) :
    ∑ i : Fin (j + 1), (bint j i).natAbs * (i : ℕ) ≤ bden j * 2 ^ r * r :=
  calc ∑ i : Fin (j + 1), (bint j i).natAbs * (i : ℕ)
      ≤ ∑ i : Fin (j + 1), (bint j i).natAbs * j :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp i.isLt)
    _ = (∑ i : Fin (j + 1), (bint j i).natAbs) * j := (Finset.sum_mul _ _ _).symm
    _ ≤ bden j * 2 ^ r * r := Nat.mul_le_mul (bint_abs_sum j r hj) hj

theorem bint_second_sum (j r : ℕ) (hj : j ≤ r) :
    ∑ i : Fin (j + 1), (bint j i).natAbs * ((i : ℕ) - 1) * (i : ℕ) ≤ bden j * 2 ^ r * (r * r) :=
  calc ∑ i : Fin (j + 1), (bint j i).natAbs * ((i : ℕ) - 1) * (i : ℕ)
      ≤ ∑ i : Fin (j + 1), (bint j i).natAbs * (j * j) :=
        Finset.sum_le_sum fun i _ => by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by have := i.isLt; omega) (Nat.lt_succ_iff.mp i.isLt))
    _ = (∑ i : Fin (j + 1), (bint j i).natAbs) * (j * j) := (Finset.sum_mul _ _ _).symm
    _ ≤ bden j * 2 ^ r * (r * r) := Nat.mul_le_mul (bint_abs_sum j r hj) (Nat.mul_le_mul hj hj)

/-- The second bound of `eq:Pfinitebounds`: `|ΔP_j| ≤ r 2^r h` for `j ≤ r`, cleared by `D_j q^j`. -/
theorem bernoulli_step {j r : ℕ} (hj : j ≤ r) {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) :
    (Γ ⊢[PRAAx] zle (-ZT.ofNat (num (bden j * 2 ^ r * r) * u * pw q (num (j - 1)))) (fv (bint j) p u q)) ∧
      (Γ ⊢[PRAAx] zle (fv (bint j) p u q) (ZT.ofNat (num (bden j * 2 ^ r * r) * u * pw q (num (j - 1))))) :=
  ⟨first_lower (bint j) (bint_first_sum j r hj) hR, first_upper (bint j) (bint_first_sum j r hj) hR⟩

/-- The third bound of `eq:Pfinitebounds`: `|ΔP_j − h P_j′(t)| ≤ (r² 2^r/2) h²` for `j ≤ r`, cleared by
`2 D_j q^{j+1}`; `P_j′ = P_{j−1}` by `bint_deriv`. -/
theorem bernoulli_second {j r : ℕ} (hj : j ≤ r) {p u q : PTm n} (hR : Γ ⊢[PRAAx] le (p + u) q) :
    (Γ ⊢[PRAAx] zle (-ZT.ofNat (num (bden j * 2 ^ r * (r * r)) * (u * u) * pw q (num (j - 1))))
        (ZT.ofNat (two * q) * tv (bint j) p u q)) ∧
      (Γ ⊢[PRAAx] zle (ZT.ofNat (two * q) * tv (bint j) p u q)
        (ZT.ofNat (num (bden j * 2 ^ r * (r * r)) * (u * u) * pw q (num (j - 1))))) :=
  ⟨second_lower (bint j) (bint_second_sum j r hj) hR, second_upper (bint j) (bint_second_sum j r hj) hR⟩

/-! ## `P_j′ = P_{j−1}` for the cleared coefficients -/

/-- `(k + 1) · (D_{j+1} bc (j+1) (k+1)) = D_{j+1} bc j k`: the derivative of `P_{j+1}` is `P_j`. -/
theorem bint_deriv (j k : ℕ) (hk : k + 1 < j + 2) :
    ((k + 1 : ℕ) : ℚ) * bint (j + 1) ⟨k + 1, hk⟩ = bden (j + 1) * bc j k := by
  have h := bc_deriv j k
  rw [bint_eq]
  simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one]
  linear_combination (bden (j + 1) : ℚ) * h

end LeanProofs.IPRA.Analysis.BernoulliIncrements
