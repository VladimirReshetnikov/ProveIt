import IPRADerivations.AnalyticNumberTheory.ZetaPrecision

/-!
# The integer thresholds and the closed modulus of the PNT contraction (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, §"Integer thresholds and the
modulus". With `q ≥ 1` (written `q = p + 1`), `D = 2^{20} q³`, `H̄ = 1024 q`, `S = 2^{18}`:

  `T₀ = 2`,  `T_{j+1} = 16(T_j + H̄) + D(16 T_j + S) + 1`  (`con:recurrence`, `Tt`, `T_zero`, `T_succ`),

and, with `F = 2^{20} D`, "one checks `T_{j+1} + 1 ≤ F(T_j + 1)`, `T_J + 1 ≤ 3F^J`" (`T_step`, `T_closed`).
"`D ≤ 2^{D/16}` … Hence `F = 2^{20} D ≤ 2^{D/8}`" (`sixteen_m`, `F_le`, with `m = D/16`), "`3F^J ≤ 2^{D²}`, where
`J ≤ 4D` was used. Thus `T_J ≤ 2^{D²}` and `P_J ≤ N_ψ(q) := 2^{2^{D²+1}}`" (`T_double`, `closed_modulus`, for
every `j ≤ 4D`), the modulus being elementary. The levels `J = 4D − D/q`, `a_J = 4 − J/D = 1/q`
(`con:levels`): `J_spec`, `J_le`, `levels_end`, `modulus_J`.

No numeral power is evaluated: `16m ≤ 2^m` comes from `(k + 1)² ≤ 4^k` (`ZetaFiniteContract.sq_le_pow`) at
`m = 2k`, and `F = 2^{20}·16m ≤ 2^m 2^m` from `16m ≤ 2^m` and `2^{20} ≤ 16m`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PNTThresholds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (le_pow_self sq_le_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaErrorBudget (pw2_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockGeo (congrPw2)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Parameters (`q = p + 1`) -/

abbrev Q3 (p : PTm n) : PTm n := succ p * succ p * succ p
/-- `D = 2^{20} q³`. -/
abbrev Dq (p : PTm n) : PTm n := num 1048576 * Q3 p
/-- `m = D/16 = 2^{16} q³`. -/
abbrev mq (p : PTm n) : PTm n := num 65536 * Q3 p
/-- `k = m/2 = 2^{15} q³`. -/
abbrev kq (p : PTm n) : PTm n := num 32768 * Q3 p
/-- `F = 2^{20} D`. -/
abbrev Fq (p : PTm n) : PTm n := num 1048576 * Dq p

/-! ## The recursion -/

/-- The step body over `0 = j`, `1 = T_j`, `2 = p`: `16(T_j + 1024q) + D(16 T_j + 2^{18}) + 1`. -/
def stepT : PTm 3 :=
  num 16 * (var 1 + num 1024 * succ (var 2)) + Dq (var 2) * (num 16 * var 1 + num 262144) + one

/-- `T_j`. -/
def Tt (j p : PTm n) : PTm n := ap2 (rec2 (num 2) stepT) j p

@[simp] theorem subst_Tt {k : ℕ} (σ : Fin n → PTm k) (j p : PTm n) :
    Syn.subst σ (Tt j p) = Tt (Syn.subst σ j) (Syn.subst σ p) := by simp [Tt]

theorem T_zero (p : PTm n) : Γ ⊢[PRAAx] Tt zero p ≐ num 2 := by
  unfold Tt; simpa using rec2_zero (Γ := Γ) (num 2) stepT p

theorem T_succ (j p : PTm n) :
    Γ ⊢[PRAAx] Tt (succ j) p ≐
      num 16 * (Tt j p + num 1024 * succ p) + Dq p * (num 16 * Tt j p + num 262144) + one := by
  unfold Tt; simpa [stepT] using rec2_succ (Γ := Γ) (num 2) stepT j p

/-- `T_{j+1} + 1 ≤ F (T_j + 1)`. -/
theorem T_step (j p : PTm n) : Γ ⊢[PRAAx] le (succ (Tt (succ j) p)) (Fq p * succ (Tt j p)) := by
  have e := natEq (T_succ (Γ := Γ) j p)
  ipra_le 1099494850560 * 𝔞 p ^ 3 * 𝔞 (Tt j p) + 3298484551680 * 𝔞 p ^ 2 * 𝔞 (Tt j p) +
      3298484551680 * 𝔞 p * 𝔞 (Tt j p) + 1099494850544 * 𝔞 (Tt j p) + 824633720832 * 𝔞 p ^ 3 +
      2473901162496 * 𝔞 p ^ 2 + 2473901146112 * 𝔞 p + 824633704446 with e

/-- The closed-form invariant `T_j + 1 ≤ 3 F^j`. -/
def clInv (j p : PTm n) : Fm PTm n := le (succ (Tt j p)) (num 3 * pw (Fq p) j)

@[simp] theorem subst_clInv {k : ℕ} (σ : Fin n → PTm k) (j p : PTm n) :
    (clInv j p).subst σ = clInv (Syn.subst σ j) (Syn.subst σ p) := by
  simp [clInv, subst_ap2]

/-- `T_j + 1 ≤ 3 F^j`. -/
theorem T_closed (j p : PTm n) : Γ ⊢[PRAAx] le (succ (Tt j p)) (num 3 * pw (Fq p) j) := by
  have hall : Γ ⊢[PRAAx] Fm.all (clInv (var 0) (Syn.shift p)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · rw [subst_clInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have e1 := natEq (T_zero (Γ := Γ) p)
      have e2 := natEq (pw_zero (Γ := Γ) (Fq p))
      show Γ ⊢[PRAAx] le (succ (Tt zero p)) (num 3 * pw (Fq p) zero)
      ipra_le 0 with 3 * e2 - e1
    · rw [subst_clInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := clInv (var 0) (Syn.shift p) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (succ (Tt (var 0) (Syn.shift p))) (num 3 * pw (Fq (Syn.shift p)) (var 0)) :=
        Prf.hyp0
      have st := T_step (Γ := Δ) (var 0) (Syn.shift p)
      have e := natEq (pw_succ (Γ := Δ) (Fq (Syn.shift p)) (var 0))
      show Δ ⊢[PRAAx] le (succ (Tt (succ (var 0)) (Syn.shift p))) (num 3 * pw (Fq (Syn.shift p)) (succ (var 0)))
      ipra_le sl st + 1099511627776 * (𝔞 (Syn.shift p) + 1) ^ 3 * sl ih with 3 * e
  have h := Prf.allE j hall
  rw [subst_clInv] at h
  simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact h

/-! ## `F ≤ 2^{D/8}` -/

/-- `16 m ≤ 2^m` (`D ≤ 2^{D/16}`). -/
theorem sixteen_m (p : PTm n) : Γ ⊢[PRAAx] le (num 16 * mq p) (pw two (mq p)) := by
  have s := sq_le_pow (Γ := Γ) (kq p)
  have e1 := natEq (congrPw2 (Γ := Γ) (show Γ ⊢[PRAAx] mq p ≐ kq p + kq p by apply deriveNat; ipra_simps; ring))
  have e2 := natEq (pw_add (Γ := Γ) two (kq p) (kq p))
  ipra_le sl s + 32768 * (𝔞 p + 1) ^ 3 *
      (32768 * 𝔞 p ^ 3 + 98304 * 𝔞 p ^ 2 + 98304 * 𝔞 p + 32738) + 1 with e1 + e2

/-- `F = 2^{20} D ≤ 2^{D/8} = 2^{2m}`. -/
theorem F_le (p : PTm n) : Γ ⊢[PRAAx] le (Fq p) (pw two (num 2 * mq p)) := by
  have a := sixteen_m (Γ := Γ) p
  have b : Γ ⊢[PRAAx] le (num 1048576) (num 16 * mq p) := by
    ipra_le 1048576 * (𝔞 p ^ 3 + 3 * 𝔞 p ^ 2 + 3 * 𝔞 p)
  have e1 := natEq (congrPw2 (Γ := Γ) (show Γ ⊢[PRAAx] num 2 * mq p ≐ mq p + mq p by
    apply deriveNat; ipra_simps; ring))
  have e2 := natEq (pw_add (Γ := Γ) two (mq p) (mq p))
  ipra_le sl a * 𝔞 (pw two (mq p)) + 1048576 * (𝔞 p + 1) ^ 3 * sl a + 1048576 * (𝔞 p + 1) ^ 3 * sl b with
    e1 + e2

/-! ## The closed modulus -/

/-- `T_j + 1 ≤ 2^{D²}` for `j ≤ 4D`. -/
theorem T_double {j : PTm n} (p : PTm n) (hj : Γ ⊢[PRAAx] le j (num 4 * Dq p)) :
    Γ ⊢[PRAAx] le (succ (Tt j p)) (pw two (Dq p * Dq p)) := by
  have c := T_closed (Γ := Γ) j p
  have f1 : Γ ⊢[PRAAx] le (pw (Fq p) j) (pw (pw two (num 2 * mq p)) j) := pw_le_pw j (F_le p)
  have f2 := natEq (AnalyticNumberTheory.RSA.pw_mul (Γ := Γ) two (num 2 * mq p) j)
  have f3 : Γ ⊢[PRAAx] le (pw two (num 2 * mq p * j)) (pw two (num 8 * mq p * Dq p)) :=
    pw2_mono (by ipra_le 2 * (65536 * (𝔞 p + 1) ^ 3) * sl hj)
  have x3 : Γ ⊢[PRAAx] le (num 3) (num 8 * mq p * Dq p) := by
    ipra_le 549755813888 * 𝔞 p * ((𝔞 p + 1) ^ 5 + (𝔞 p + 1) ^ 4 + (𝔞 p + 1) ^ 3 + (𝔞 p + 1) ^ 2 + (𝔞 p + 1) + 1) +
      549755813885
  have g1 : Γ ⊢[PRAAx] le (num 3) (pw two (num 8 * mq p * Dq p)) := by
    have l := le_pow_self (Γ := Γ) (num 8 * mq p * Dq p)
    ipra_le sl x3 + sl l
  have e3 := natEq (congrPw2 (Γ := Γ) (show Γ ⊢[PRAAx] Dq p * Dq p ≐
      num 8 * mq p * Dq p + num 8 * mq p * Dq p by apply deriveNat; ipra_simps; ring))
  have e4 := natEq (pw_add (Γ := Γ) two (num 8 * mq p * Dq p) (num 8 * mq p * Dq p))
  ipra_le sl c + 3 * sl f1 + 3 * sl f3 + 𝔞 (pw two (num 8 * mq p * Dq p)) * sl g1 with e3 + e4 - 3 * f2

/-- `con:closed-modulus`: `P_j = 2^{2T_j} ≤ 2^{2^{D²+1}}` for every `j ≤ 4D`. -/
theorem closed_modulus {j : PTm n} (p : PTm n) (hj : Γ ⊢[PRAAx] le j (num 4 * Dq p)) :
    Γ ⊢[PRAAx] le (pw two (two * Tt j p)) (pw two (pw two (succ (Dq p * Dq p)))) := by
  have td := T_double p hj
  have e := natEq (pw_succ (Γ := Γ) two (Dq p * Dq p))
  exact pw2_mono (by ipra_le 2 * sl td + 2 with e)

/-! ## The levels `J = 4D − D/q` -/

/-- `J = 4D − D/q`, `D/q = 2^{20} q²`. -/
abbrev Jq (p : PTm n) : PTm n := monus (num 4 * Dq p) (num 1048576 * (succ p * succ p))

theorem J_spec (p : PTm n) : Γ ⊢[PRAAx] num 4 * Dq p ≐ num 1048576 * (succ p * succ p) + Jq p := by
  have h : Γ ⊢[PRAAx] le (num 1048576 * (succ p * succ p)) (num 4 * Dq p) := by
    ipra_le 1048576 * (𝔞 p + 1) ^ 2 * (4 * 𝔞 p + 3)
  exact eq_add_of_le h

theorem J_le (p : PTm n) : Γ ⊢[PRAAx] le (Jq p) (num 4 * Dq p) :=
  le_of_eq_add ((J_spec p).eqTrans (add_comm _ _))

/-- `a_J = 4 − J/D = 1/q`, cleared: `q (4D − J) = D`. -/
theorem levels_end (p : PTm n) : Γ ⊢[PRAAx] succ p * monus (num 4 * Dq p) (Jq p) ≐ Dq p := by
  have hle := J_le (Γ := Γ) p
  have e1 := natEq (eq_add_of_le hle)
  have e2 := natEq (J_spec (Γ := Γ) p)
  apply deriveNat; ipra_simps; linear_combination (𝔞 p + 1) * (e2 - e1)

/-- The modulus at the final level: `P_J ≤ N_ψ(q) = 2^{2^{D²+1}}`. -/
theorem modulus_J (p : PTm n) :
    Γ ⊢[PRAAx] le (pw two (two * Tt (Jq p) p)) (pw two (pw two (succ (Dq p * Dq p)))) :=
  closed_modulus p (J_le p)

end LeanProofs.IPRA.AnalyticNumberTheory.PNTThresholds
