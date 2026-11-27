import IPRADerivations.DiophantineNumberTheory.AperyNumbers
import IPRADerivations.Analysis.RationalArithmetic.Powers.Pochhammer

/-!
# A prescribed coprime modulus

Packet: `diophantine-number-theory/transcendence_ipra` (`lem:modulus`). For `M, R ≥ 1` and any
`A`, put

  `L = 4R² + 4AR + 1`,   `q = M L`,   `p = 2q + 1`.

* `p_gt_one`: `1 < p`;
* `p_coprime`: `gcd(p, M) = 1`, from `p − 2L·M = 1`; `p` need not be prime;
* `poch_ge_pow`: `x^m ≤ (x)_m`, and `fact_ge_pow`: `q^q ≤ (2q)!`;
* `factorial_estimate` (2.2): `4 A R^p < (p − 1)!`, i.e. `A R^p / (p − 1)! < 1/4`.

The chain for the estimate is `(2q)! ≥ q^q ≥ (4R²)^q = 4^q R^{2q} ≥ (q + 1) R^{2q} > 4AR · R^{2q}`.
The transcendence argument that uses this modulus is not formalized.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.CoprimeModulus

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_zero poch_succ poch_fact)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.AperyNumbers (four_pow_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `L = 4R² + 4AR + 1`. -/
abbrev Lm (A R : PTm n) : PTm n := (two * two) * (R * R) + (two * two) * (A * R) + one
/-- `q = M L`. -/
abbrev qm (M A R : PTm n) : PTm n := M * Lm A R
/-- `p = 2q + 1`. -/
abbrev pm (M A R : PTm n) : PTm n := succ (two * qm M A R)

/-! ## `p > 1` and `gcd(p, M) = 1` -/

section Modulus

variable {M A R : PTm n}

theorem Lm_pos : Γ ⊢[PRAAx] Lm A R ≐ succ (pred (Lm A R)) :=
  pos_of_eq_succ (c := (two * two) * (R * R) + (two * two) * (A * R)) (succ_eq_add_one _).eqSymm

theorem qm_pos (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) : Γ ⊢[PRAAx] qm M A R ≐ succ (pred (qm M A R)) :=
  pos_mul' hM Lm_pos

/-- `1 < p`. -/
theorem p_gt_one (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) : Γ ⊢[PRAAx] lt one (pm M A R) := by
  refine le_of_eq_add (d := succ (two * pred (qm M A R))) ?_
  ipra_lc 2 * natEq (qm_pos (A := A) (R := R) hM)

theorem pm_pos : Γ ⊢[PRAAx] pm M A R ≐ succ (pred (pm M A R)) := congrSucc (pred_succ _).eqSymm

/-- `gcd(p, M) = 1`. -/
theorem p_coprime (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) : Γ ⊢[PRAAx] gcd (pm M A R) M ≐ one := by
  have hg := gcd_pos (B := M) (pm_pos (M := M) (A := A) (R := R) (Γ := Γ))
  have hd := gcd_dvd' (b := M) (pm_pos (M := M) (A := A) (R := R) (Γ := Γ))
  have e : Γ ⊢[PRAAx] pm M A R ≐ one + M * (two * Lm A R) := by ipra_ring
  exact eq_one_of_dvd_one hg
    (dvd_sub' hg (dvd_congr e (Prf.andE₁ hd)) (dvd_mul' hg (two * Lm A R) (Prf.andE₂ hd)))

/-- `4R² ≤ q`. -/
theorem four_sq_le (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) : Γ ⊢[PRAAx] le ((two * two) * (R * R)) (qm M A R) := by
  refine le_of_eq_add (d := ((two * two) * (A * R) + one) + pred M * Lm A R) ?_
  ipra_lc (4 * 𝔞(R) * 𝔞(R) + 4 * 𝔞(A) * 𝔞(R) + 1) * natEq hM

/-- `4AR < q`. -/
theorem four_ar_lt (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) : Γ ⊢[PRAAx] lt ((two * two) * (A * R)) (qm M A R) := by
  refine le_of_eq_add (d := (two * two) * (R * R) + pred M * Lm A R) ?_
  ipra_lc (4 * 𝔞(R) * 𝔞(R) + 4 * 𝔞(A) * 𝔞(R) + 1) * natEq hM

end Modulus

/-! ## `q^q ≤ (2q)!` -/

theorem pg_step {x m : PTm n} (ih : Γ ⊢[PRAAx] le (pw x m) (poch x m)) :
    Γ ⊢[PRAAx] le (pw x (succ m)) (poch x (succ m)) :=
  le_congr (pw_succ x m).eqSymm (poch_succ x m).eqSymm (le_mul_mono ih (le_add_right x m))

/-- Variables: `0 = m`, `1 = x`. -/
private abbrev pgF : Fm PTm 2 := le (pw (var 1) (var 0)) (poch (var 1) (var 0))

private theorem pg₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] pgF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (pw_zero _).eqSymm (poch_zero _).eqSymm (le_refl one)
  · exact pg_step Prf.hyp0

/-- `x^m ≤ (x)_m`. -/
theorem poch_ge_pow (x m : PTm n) : Γ ⊢[PRAAx] le (pw x m) (poch x m) := by
  have h := inst (Γ := Γ) pg₀ (![m, x] : Fin 2 → PTm n)
  simpa using h

/-- `q^q ≤ (2q)!`. -/
theorem fact_ge_pow (q : PTm n) : Γ ⊢[PRAAx] le (pw q q) (fact (two * q)) := by
  have h₁ : Γ ⊢[PRAAx] le (pw q q) (poch (succ q) q) :=
    le_trans (pw_le_pw q (le_succ_self q)) (poch_ge_pow (succ q) q)
  have h₂ : Γ ⊢[PRAAx] le (poch (succ q) q) (poch (succ q) q * fact q) :=
    le_congr ((mul_comm _ _).eqTrans (one_mul _)) (.eqRefl _)
      (le_mul_mono (le_refl (poch (succ q) q)) (one_le_of_pos (fact_pos q)))
  have hN : Γ ⊢[PRAAx] q + q ≐ two * q := by ipra_ring
  exact le_congr (.eqRefl _) ((poch_fact q q).eqTrans (congrAp2 factF hN (.eqRefl _))) (le_trans h₁ h₂)

/-! ## The factorial estimate -/

/-- `(R²)^q = R^{2q}`. -/
theorem pw_sq (R q : PTm n) : Γ ⊢[PRAAx] pw (R * R) q ≐ pw R (two * q) := by
  have hN : Γ ⊢[PRAAx] two * q ≐ q + q := by ipra_ring
  exact (pw_mul_base R R q).eqTrans ((pw_add R q q).eqSymm.eqTrans (congrAp2 powF hN.eqSymm (.eqRefl _)))

/-- `(R²)^q > 0` for `R ≥ 1`. -/
theorem sq_pow_pos {R : PTm n} (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) (q : PTm n) :
    Γ ⊢[PRAAx] pw (R * R) q ≐ succ (pred (pw (R * R) q)) :=
  Common.pos_pw (Common.pos_mul hR hR) q

/-- `(2.2)`: `4 A R^p < (p − 1)!` for `p = 2q + 1`, `q = M (4R² + 4AR + 1)`, `M, R ≥ 1`. -/
theorem factorial_estimate {M A R : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) :
    Γ ⊢[PRAAx] lt ((two * two) * (A * pw R (pm M A R))) (fact (two * qm M A R)) := by
  -- `X = (R²)^q = R^{2q}`, and `R^p = X R`.
  have eX : Γ ⊢[PRAAx] pw R (pm M A R) ≐ pw (R * R) (qm M A R) * R :=
    (pw_succ R (two * qm M A R)).eqTrans (congrMul (pw_sq R (qm M A R)).eqSymm (.eqRefl _))
  have eL : Γ ⊢[PRAAx] (two * two) * (A * pw R (pm M A R)) ≐
      ((two * two) * (A * R)) * pw (R * R) (qm M A R) := by
    ipra_lc 4 * 𝔞(A) * natEq eX
  -- `(4AR) X < (4AR + 1) X`, since `X ≥ 1`.
  have s₁ : Γ ⊢[PRAAx] lt (((two * two) * (A * R)) * pw (R * R) (qm M A R))
      (succ ((two * two) * (A * R)) * pw (R * R) (qm M A R)) := by
    refine le_of_eq_add (d := pred (pw (R * R) (qm M A R))) ?_
    ipra_lc natEq (sq_pow_pos hR (qm M A R))
  -- `(4AR + 1) X ≤ q X ≤ (q + 1) X ≤ 4^q X = (4R²)^q ≤ q^q ≤ (2q)!`.
  have s₂ : Γ ⊢[PRAAx] le (succ ((two * two) * (A * R)) * pw (R * R) (qm M A R))
      (pw (two * two) (qm M A R) * pw (R * R) (qm M A R)) :=
    le_mul_mono (le_trans (four_ar_lt hM) (le_trans (le_succ_self _) (four_pow_ge _))) (le_refl _)
  have s₃ : Γ ⊢[PRAAx] le (pw (two * two) (qm M A R) * pw (R * R) (qm M A R)) (fact (two * qm M A R)) :=
    le_congr (pw_mul_base _ _ _) (.eqRefl _)
      (le_trans (pw_le_pw (qm M A R) (four_sq_le hM)) (fact_ge_pow (qm M A R)))
  exact lt_congr eL.eqSymm (.eqRefl _) (lt_of_lt_of_le s₁ (le_trans s₂ s₃))

end LeanProofs.IPRA.DiophantineNumberTheory.CoprimeModulus
