import IPRADerivations.Core.IntCertificates
import IPRADerivations.Analysis.BernoulliCoefficients
import Mathlib.Data.Nat.Cast.Field

/-!
# Evaluation bounds for integer polynomials on `[0, 1]`, and the Bernoulli bound `|P_j(t)| ≤ 2^r`

Packet: `analysis/calculus_ipra`, `report.tex`, `eq:Pfinitebounds`: for every `j ≤ r` and `0 ≤ t ≤ 1`,
`|P_j(t)| ≤ C = 2^r`, from "`|P(t)| ≤ ‖P‖` for rational `t ∈ [0, 1]`" and the coefficient bound `eq:coefbound`.

A rational point `t = p/q` with `0 ≤ p ≤ q` is cleared by `q^d`: for integer coefficients `a_0, …, a_d` (fixed
metalevel data), `q^d P(p/q) = Σ_i a_i p^i q^{d−i}` is the integer term `pv a p q` (`ZT`, `Core/Integers`).

* `zint`, `toZ_zint`: an integer constant as an integer term;
* `poly_upper`, `poly_lower`: for `p ≤ q` and `Σ |a_i| ≤ S`, `−S q^d ≤ Σ_i a_i p^i q^{d−i} ≤ S q^d`, i.e.
  `|P(t)| ≤ ‖P‖` on `[0, 1]`. Each is an integer certificate: for `a_i ≥ 0` the slack `a_i q^{d−i} (q^i − p^i)` of
  `pw_le_pw`, for `a_i < 0` the natural combination `|a_i| (q^d + p^i q^{d−i})`;
* `bden`, `bint`, `bint_eq`: the Bernoulli coefficients `bc j i` cleared by the product `D_j` of their denominators;
* `bernoulli_value` (the first bound of `eq:Pfinitebounds`): for `j ≤ r` and `p ≤ q`,
  `−D_j 2^r q^j ≤ D_j q^j P_j(p/q) ≤ D_j 2^r q^j`, i.e. `|P_j(t)| ≤ 2^r`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BernoulliBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BernoulliCoefficients (bc nrm nrm_le_two bc_zero_of_gt)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Integer constants and polynomial values -/

/-- The integer constant `z` as an integer term. -/
def zint (z : ℤ) : ZT n := ZT.natLit z.toNat - ZT.natLit (-z).toNat

theorem toZ_zint (z : ℤ) : ZT.toZ Γ (zint z : ZT n) = (z : Groth (Q Γ)) := by
  simp only [zint, ZT.toZ_sub, ZT.toZ_natLit]
  have h := Int.toNat_sub_toNat_neg z
  conv_rhs => rw [← h]
  push_cast; ring

/-- `q^d P(p/q) = Σ_{i ≤ d} a_i p^i q^{d−i}`. -/
def pv {d : ℕ} (a : Fin (d + 1) → ℤ) (p q : PTm n) : ZT n :=
  ZT.sumFin fun i => zint (a i) * ZT.ofNat (pw p (num i) * pw q (num (d - i)))

theorem qsplit (d i : ℕ) (hi : i ≤ d) (q : PTm n) :
    Γ ⊢[PRAAx] pw q (num d) ≐ pw q (num i) * pw q (num (d - i)) := by
  have hd : d = i + (d - i) := by omega
  have e : Γ ⊢[PRAAx] (num d : PTm n) ≐ num i + num (d - i) := by
    apply deriveNat
    simp only [Q.mk_num, Q.mk_add, map_natCast, map_add]
    conv_lhs => rw [hd]
    push_cast; ring
  exact (congrAp2 powF e (.eqRefl q)).eqTrans (pw_add q _ _)

theorem natAbs_cast_of_nonneg {R : Type*} [CommRing R] {z : ℤ} (h : 0 ≤ z) : ((z.natAbs : ℕ) : R) = (z : R) := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg h]

theorem natAbs_cast_of_neg {R : Type*} [CommRing R] {z : ℤ} (h : z < 0) : ((z.natAbs : ℕ) : R) = -(z : R) := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg h, Int.cast_neg]

section Poly

variable {d : ℕ} (a : Fin (d + 1) → ℤ)

/-- `Σ_{i ≤ d} a_i p^i q^{d−i} ≤ S q^d` for `p ≤ q`, `Σ |a_i| ≤ S`. -/
theorem poly_upper {S : ℕ} (hS : ∑ i, (a i).natAbs ≤ S) {p q : PTm n} (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] zle (pv a p q) (ZT.ofNat (num S * pw q (num d))) := by
  let Qd : Groth (Q Γ) := Groth.ι (Q.mk Γ (pw q (num d)))
  let z : Fin (d + 1) → Groth (Q Γ) := fun i =>
    if 0 ≤ a i then ((a i).natAbs : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw q (num (d - i)))) *
        sl (pw_le_pw (num i) hpq)
    else ((a i).natAbs : Groth (Q Γ)) *
        (Qd + Groth.ι (Q.mk Γ (pw p (num i))) * Groth.ι (Q.mk Γ (pw q (num (d - i)))))
  refine zle_of_comb ((∑ i, z i) + ((S - ∑ i, (a i).natAbs : ℕ) : Groth (Q Γ)) * Qd) ?_ ?_
  · simp only [pv, ZT.toZ_sumFin, ZT.toZ_mul, toZ_zint, ZT.toZ_ofNat, Q.mk_mul, map_mul, Q.mk_num, map_natCast]
    rw [Nat.cast_sub hS, Nat.cast_sum]
    have key : ∀ i : Fin (d + 1), ((a i).natAbs : Groth (Q Γ)) * Qd -
        (a i : Groth (Q Γ)) * (Groth.ι (Q.mk Γ (pw p (num i))) * Groth.ι (Q.mk Γ (pw q (num (d - i))))) = z i := by
      intro i
      have e := natEq (qsplit (Γ := Γ) d i (Nat.lt_succ_iff.mp i.isLt) q)
      simp only [Q.mk_mul, map_mul] at e
      simp only [z, Qd]
      split_ifs with h
      · rw [natAbs_cast_of_nonneg h, sl_def, e]; ring
      · rw [natAbs_cast_of_neg (lt_of_not_ge h)]; ring
    rw [← Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  · refine nn_add (nn_sum _ _ fun i _ => ?_) (nn_mul (nn_natCast _) (nn_term _))
    simp only [z]
    split_ifs
    · exact nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_sl _)
    · exact nn_mul (nn_natCast _) (nn_add (nn_term _) (nn_mul (nn_term _) (nn_term _)))

/-- `−S q^d ≤ Σ_{i ≤ d} a_i p^i q^{d−i}` for `p ≤ q`, `Σ |a_i| ≤ S`. -/
theorem poly_lower {S : ℕ} (hS : ∑ i, (a i).natAbs ≤ S) {p q : PTm n} (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (num S * pw q (num d))) (pv a p q) := by
  let Qd : Groth (Q Γ) := Groth.ι (Q.mk Γ (pw q (num d)))
  let z : Fin (d + 1) → Groth (Q Γ) := fun i =>
    if 0 ≤ a i then ((a i).natAbs : Groth (Q Γ)) *
        (Qd + Groth.ι (Q.mk Γ (pw p (num i))) * Groth.ι (Q.mk Γ (pw q (num (d - i)))))
    else ((a i).natAbs : Groth (Q Γ)) * Groth.ι (Q.mk Γ (pw q (num (d - i)))) * sl (pw_le_pw (num i) hpq)
  refine zle_of_comb ((∑ i, z i) + ((S - ∑ i, (a i).natAbs : ℕ) : Groth (Q Γ)) * Qd) ?_ ?_
  · simp only [pv, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_neg, toZ_zint, ZT.toZ_ofNat, Q.mk_mul, map_mul, Q.mk_num,
      map_natCast]
    rw [Nat.cast_sub hS, Nat.cast_sum]
    have key : ∀ i : Fin (d + 1), (a i : Groth (Q Γ)) *
        (Groth.ι (Q.mk Γ (pw p (num i))) * Groth.ι (Q.mk Γ (pw q (num (d - i))))) +
        ((a i).natAbs : Groth (Q Γ)) * Qd = z i := by
      intro i
      have e := natEq (qsplit (Γ := Γ) d i (Nat.lt_succ_iff.mp i.isLt) q)
      simp only [Q.mk_mul, map_mul] at e
      simp only [z, Qd]
      split_ifs with h
      · rw [natAbs_cast_of_nonneg h]; ring
      · rw [natAbs_cast_of_neg (lt_of_not_ge h), sl_def, e]; ring
    rw [← Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  · refine nn_add (nn_sum _ _ fun i _ => ?_) (nn_mul (nn_natCast _) (nn_term _))
    simp only [z]
    split_ifs
    · exact nn_mul (nn_natCast _) (nn_add (nn_term _) (nn_mul (nn_term _) (nn_term _)))
    · exact nn_mul (nn_mul (nn_natCast _) (nn_term _)) (nn_sl _)

end Poly

/-! ## The cleared Bernoulli coefficients -/

/-- `D_j`, the product of the denominators of the coefficients of `P_j`. -/
def bden (j : ℕ) : ℕ := ∏ i ∈ Finset.range (j + 1), (bc j i).den

theorem den_dvd (j i : ℕ) (hi : i < j + 1) : (bc j i).den ∣ bden j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)

theorem bden_pos (j : ℕ) : 0 < bden j := Finset.prod_pos fun i _ => (bc j i).den_pos

/-- The integer coefficient `D_j · bc j i`. -/
def bint (j : ℕ) (i : Fin (j + 1)) : ℤ := (bc j i).num * ((bden j / (bc j i).den : ℕ) : ℤ)

theorem bint_eq (j : ℕ) (i : Fin (j + 1)) : (bint j i : ℚ) = bc j i * bden j := by
  have hd := den_dvd j i i.isLt
  have hpos : (0 : ℚ) < (bc j i).den := by exact_mod_cast (bc j i).den_pos
  rw [bint, Int.cast_mul, Int.cast_natCast, Nat.cast_div hd (ne_of_gt hpos)]
  conv_rhs => rw [← Rat.num_div_den (bc j i)]
  field_simp

theorem bint_abs_sum (j r : ℕ) (hj : j ≤ r) : ∑ i, (bint j i).natAbs ≤ bden j * 2 ^ r := by
  have hq : ((∑ i, (bint j i).natAbs : ℕ) : ℚ) = bden j * nrm j := by
    rw [Nat.cast_sum, nrm, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, bint_eq, abs_mul,
      abs_of_nonneg (a := (bden j : ℚ)) (Nat.cast_nonneg _), _root_.mul_comm]
  have hb : (bden j : ℚ) * nrm j ≤ bden j * 2 ^ r :=
    mul_le_mul_of_nonneg_left ((nrm_le_two j).trans (pow_le_pow_right₀ (by norm_num) hj)) (Nat.cast_nonneg _)
  rw [← hq] at hb
  exact_mod_cast hb

/-- The first bound of `eq:Pfinitebounds`, `|P_j(t)| ≤ 2^r` for `j ≤ r` and `t = p/q ∈ [0, 1]`, cleared by `D_j q^j`. -/
theorem bernoulli_value {j r : ℕ} (hj : j ≤ r) {p q : PTm n} (hpq : Γ ⊢[PRAAx] le p q) :
    (Γ ⊢[PRAAx] zle (-ZT.ofNat (num (bden j * 2 ^ r) * pw q (num j))) (pv (bint j) p q)) ∧
      (Γ ⊢[PRAAx] zle (pv (bint j) p q) (ZT.ofNat (num (bden j * 2 ^ r) * pw q (num j)))) :=
  ⟨poly_lower (bint j) (bint_abs_sum j r hj) hpq, poly_upper (bint j) (bint_abs_sum j r hj) hpq⟩

end LeanProofs.IPRA.Analysis.BernoulliBounds
