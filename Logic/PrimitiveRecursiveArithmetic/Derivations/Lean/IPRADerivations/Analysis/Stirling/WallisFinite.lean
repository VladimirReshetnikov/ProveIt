import IPRADerivations.Analysis.Stirling.WallisRecurrence
import IPRADerivations.Analysis.Integration.BaselRiemann
import IPRADerivations.Core.CommonLemmas

/-!
# The finite Wallis inequality

Packet: `analysis/stirling_ipra`, `stirling_ipra.tex`, Section `sec:wallis`: the case `k = 1` of `eq:Jrec`,
the iterated bounds `eq:evenerr`, `eq:odderr`, and Theorem `thm:finitewallis`:
for `m, M ≥ 1` and `D_m = 16 · 2^m (m + 1)²`,
`W_m − D_m/M ≤ J_0(M) ≤ ((2m + 1)/(2m)) W_m + D_m/M`, where `W_m = ∏_{j ≤ m} 4j²/(4j² − 1)` is the Wallis
product and `J_0(M) = (1/M) ∑_{j<M} 2/(1 + (j/M)²)` is the left Riemann sum naming `π/2`.

Everything is cleared by `F = L!` with `2M² ≤ L` (`M = M₀ + 1`), as in `WallisGrid` and `WallisRecurrence`:
`𝒥_k = ∑_{j<M} om_j sg_j^k = M F^{k+1} J_k(M)`. The products are the double factorials
`da m = ∏_{k<m} (2k + 1) = (2m − 1)!!` and `db m = ∏_{k<m} (2k + 2) = (2m)!!`, so that
`p_m = da m / db m`, `q_m = db m / da (m + 1)` and `W_m = (db m)² / (da m · da (m + 1))`.

The last section derives the paper's exact consequence `W_m ≤ 2` (`wallis_le_two`), a statement about double
factorials alone, by using the inequality at one explicit mesh.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.WallisFinite

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselQuadrature (uq d_pos lift4 inst2_lift4)
open LeanProofs.IPRA.Analysis.WallisGrid
open LeanProofs.IPRA.Analysis.WallisRecurrence (J Jb inst_Jb om_D Mj_le ds_le wallis_rec_paper)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Double factorials -/

abbrev aB : PTm 2 := succ (two * var 0)
abbrev bB : PTm 2 := two * succ (var 0)

/-- `(2m − 1)!! = ∏_{k<m} (2k + 1)`. -/
abbrev da (m : PTm n) : PTm n := ap2 (prodF aB) m zero
/-- `(2m)!! = ∏_{k<m} (2k + 2)`. -/
abbrev db (m : PTm n) : PTm n := ap2 (prodF bB) m zero

theorem da_zero : Γ ⊢[PRAAx] da (zero : PTm n) ≐ succ zero := prod_zero _ _
theorem db_zero : Γ ⊢[PRAAx] db (zero : PTm n) ≐ succ zero := prod_zero _ _

theorem da_succ (m : PTm n) : Γ ⊢[PRAAx] da (succ m) ≐ da m * succ (two * m) := by
  have h := prod_succ (Γ := Γ) aB m zero
  simpa using h

theorem db_succ (m : PTm n) : Γ ⊢[PRAAx] db (succ m) ≐ db m * (two * succ m) := by
  have h := prod_succ (Γ := Γ) bB m zero
  simpa using h

theorem db_le_base : Γ ⊢[PRAAx] le (db (zero : PTm n)) (pw two zero * da zero) := by
  have a0 := natEq (da_zero (Γ := Γ)); have b0 := natEq (db_zero (Γ := Γ))
  have p0 := natEq (pw_zero (Γ := Γ) (two : PTm n))
  ipra_le 0 using rw [a0, b0, p0]; ring

theorem db_le_step {m : PTm n} (ih : Γ ⊢[PRAAx] le (db m) (pw two m * da m)) :
    Γ ⊢[PRAAx] le (db (succ m)) (pw two (succ m) * da (succ m)) := by
  have a1 := natEq (da_succ (Γ := Γ) m); have b1 := natEq (db_succ (Γ := Γ) m)
  have p := natEq (pw_succ (Γ := Γ) two m)
  ipra_le 2 * (𝔞 m + 1) * sl ih + 2 * 𝔞 m * (𝔞 (pw two m) * 𝔞 (da m)) using rw [a1, b1, p]; ring

/-- Variable `0 = m`. -/
private abbrev dbF : Fm PTm 1 := le (db (var 0)) (pw two (var 0) * da (var 0))

private theorem db₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] dbF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact db_le_base
  · simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact db_le_step Prf.hyp0

/-- `p_m ≥ 2^{−m}`: `(2m)!! ≤ 2^m (2m − 1)!!`. -/
theorem db_le (m : PTm n) : Γ ⊢[PRAAx] le (db m) (pw two m * da m) := by
  have h := inst (Γ := Γ) db₀ (![m] : Fin 1 → PTm n)
  simp at h
  exact h

/-! ## Monotonicity in the exponent -/

/-- `F om_j sg_j^k` over `(j, k, M, L)`. -/
abbrev FJb : PTm 2 := lift4 (fact (var 3) * (om (var 0) (var 2) (var 3) * pw (sg (var 0) (var 2) (var 3)) (var 1)))

theorem inst_FJb (j k M L : PTm n) :
    Γ ⊢[PRAAx] inst2 FJb j (pairT k (pairT M L)) ≐ fact L * (om j M L * pw (sg j M L) k) := by
  have h := inst2_lift4 (Γ := Γ) (fact (var 3) * (om (var 0) (var 2) (var 3) * pw (sg (var 0) (var 2) (var 3)) (var 1)))
    j k M L
  simp at h; exact h

/-- `J_{k+1} ≤ J_k`, from `s ≤ 1` at each grid point: `𝒥_{k+1} ≤ F 𝒥_k`. -/
theorem J_mono {k M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (J (succ k) (succ M₀) L) (fact L * J k (succ M₀) L) := by
  have hLs := (LeanProofs.IPRA.Analysis.BaselAverages.shift_le hL).wk (ψ := lt (var 0) (Syn.shift (succ M₀)))
  have es2 : Syn.shift (two * (succ M₀ * succ M₀)) = two * (succ (Syn.shift M₀) * succ (Syn.shift M₀)) := by
    simp [Syn.shift]
  have es1 : Syn.shift (succ M₀) = succ (Syn.shift M₀) := by simp [Syn.shift]
  have esk : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
  rw [es2, es1] at hLs
  have h1 := sum_le_params (Γ := Γ) Jb FJb (pairT (succ k) (pairT (succ M₀) L)) (pairT k (pairT (succ M₀) L))
    (succ M₀) (.allI (.impI (by
      simp only [shift_pairT, es1, esk]
      have hj : (lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (succ (Syn.shift M₀)) :=
        le_trans (le_succ_self _) Prf.hyp0
      have bs := sg_le hj hLs
      have p := natEq (pw_succ (Γ := lt (var 0) (succ (Syn.shift M₀)) :: Γ.map Fm.shift)
        (sg (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) (Syn.shift k))
      refine le_congr (inst_Jb _ _ _ _).eqSymm (inst_FJb _ _ _ _).eqSymm ?_
      ipra_le 𝔟 (om (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) *
        𝔟 (pw (sg (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) (Syn.shift k)) * sl bs with
        𝔟 (om (var 0) (succ (Syn.shift M₀)) (Syn.shift L)) * p)))
  have h2 := sum_scale (Γ := Γ) FJb Jb (succ M₀) (fact L) (pairT k (pairT (succ M₀) L))
    (pairT k (pairT (succ M₀) L)) (.allI (.impI (by
      simp only [shift_pairT, es1]
      have e : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
      rw [e]
      exact (inst_FJb _ _ _ _).eqTrans (congrMul (.eqRefl _) (inst_Jb _ _ _ _).eqSymm))))
  exact le_congr (.eqRefl _) h2 h1

/-! ## The case `k = 1` -/

/-- The exact error of one cell for the increment of `c`. -/
theorem cell1_ring {R : Type*} [CommRing R] (M F T D j s s' c c' ω : R) (hT : T = D + j)
    (r2 : T * c = T * c' + M * (s + s')) (r5 : ω * D = 2 * (M * M) * F) :
    T * D * (M * F * (c - c') - ω * s) = M * M * F * (D * (s' - s) - 2 * j * s) := by
  linear_combination (D * M * F) * r2 - (T * s) * r5 - (2 * M * M * F * s) * hT

section cell

variable {j M₀ L : PTm n}

local notation "s₀" => sg j (succ M₀) L
local notation "s₁" => sg (succ j) (succ M₀) L
local notation "c₀" => gm j (succ M₀) L
local notation "c₁" => gm (succ j) (succ M₀) L
local notation "ω₀" => om j (succ M₀) L
local notation "𝔉" => fact L
local notation "𝔐" => succ M₀
local notation "𝔗" => (succ M₀ * succ M₀ + j * succ j)
local notation "𝔇" => (succ M₀ * succ M₀ + j * j)

/-- `M · M F (c − c') ≤ M · om · s + 2F²`. -/
theorem cell1_up (hj : Γ ⊢[PRAAx] le (succ j) 𝔐) (hL : Γ ⊢[PRAAx] le (two * (𝔐 * 𝔐)) L) :
    Γ ⊢[PRAAx] le (𝔐 * (𝔐 * 𝔉 * c₀)) (𝔐 * (𝔐 * 𝔉 * c₁ + ω₀ * s₀) + two * (𝔉 * 𝔉)) := by
  have hj0 : Γ ⊢[PRAAx] le j 𝔐 := le_trans (le_succ_self j) hj
  have bd := ds_le hj hL
  have r2 := natEq (gm_step hj hL); have r5 := natEq (om_D hj0 hL)
  have eds := natEq (eq_add_of_le (sg_mono hj hL))
  refine mul_le_cancel (d' := M₀ * M₀ + two * M₀ + j * succ j)
    (le_congr (congrMul (T_pos j M₀) (.eqRefl _)) (congrMul (T_pos j M₀) (.eqRefl _))
      (mul_le_cancel (d' := pred 𝔇) (le_congr (congrMul (d_pos j M₀) (.eqRefl _))
        (congrMul (d_pos j M₀) (.eqRefl _)) ?_)))
  ipra_le 2 * (𝔞 j * (𝔞 j + 1)) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * (𝔞 𝔉 * 𝔞 𝔉) +
      (𝔞 M₀ + 1) * (𝔞 M₀ + 1) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * 𝔞 𝔉 * sl bd +
      2 * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) * (𝔞 M₀ + 1)) * 𝔞 𝔉 * 𝔞 j * 𝔞 s₀ using
    have hds : 𝔞 (monus s₁ s₀) = 𝔞 s₁ - 𝔞 s₀ := by linear_combination -eds
    have X := cell1_ring (𝔞 M₀ + 1) (𝔞 𝔉) ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * (𝔞 j + 1))
      ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) (𝔞 j) (𝔞 s₀) (𝔞 s₁) (𝔞 c₀) (𝔞 c₁) (𝔞 ω₀) (by ring)
      (by linear_combination r2) (by linear_combination r5)
    rw [hds]
    generalize (𝔞 M₀ + 1) = Mv at X ⊢
    generalize Mv * Mv + 𝔞 j * 𝔞 j = Dv at X ⊢
    linear_combination (-Mv) * X

/-- `M · om · s ≤ M · M F (c − c') + 2F²`. -/
theorem cell1_dn (hj : Γ ⊢[PRAAx] le (succ j) 𝔐) (hL : Γ ⊢[PRAAx] le (two * (𝔐 * 𝔐)) L) :
    Γ ⊢[PRAAx] le (𝔐 * (𝔐 * 𝔉 * c₁ + ω₀ * s₀)) (𝔐 * (𝔐 * 𝔉 * c₀) + two * (𝔉 * 𝔉)) := by
  have hj0 : Γ ⊢[PRAAx] le j 𝔐 := le_trans (le_succ_self j) hj
  have p := le_mul_mono (Mj_le hj0) (sg_le hj0 hL)
  have r2 := natEq (gm_step hj hL); have r5 := natEq (om_D hj0 hL)
  have eds := natEq (eq_add_of_le (sg_mono hj hL))
  refine mul_le_cancel (d' := M₀ * M₀ + two * M₀ + j * succ j)
    (le_congr (congrMul (T_pos j M₀) (.eqRefl _)) (congrMul (T_pos j M₀) (.eqRefl _))
      (mul_le_cancel (d' := pred 𝔇) (le_congr (congrMul (d_pos j M₀) (.eqRefl _))
        (congrMul (d_pos j M₀) (.eqRefl _)) ?_)))
  ipra_le (𝔞 M₀ + 1) * (𝔞 M₀ + 1) * (𝔞 M₀ + 1) * 𝔞 𝔉 * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) *
        𝔞 (monus s₁ s₀) +
      2 * (𝔞 j * (𝔞 j + 1)) * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) * (𝔞 𝔉 * 𝔞 𝔉) +
      2 * ((𝔞 M₀ + 1) * (𝔞 M₀ + 1)) * 𝔞 𝔉 * sl p using
    have hds : 𝔞 (monus s₁ s₀) = 𝔞 s₁ - 𝔞 s₀ := by linear_combination -eds
    have X := cell1_ring (𝔞 M₀ + 1) (𝔞 𝔉) ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * (𝔞 j + 1))
      ((𝔞 M₀ + 1) * (𝔞 M₀ + 1) + 𝔞 j * 𝔞 j) (𝔞 j) (𝔞 s₀) (𝔞 s₁) (𝔞 c₀) (𝔞 c₁) (𝔞 ω₀) (by ring)
      (by linear_combination r2) (by linear_combination r5)
    rw [hds]
    generalize (𝔞 M₀ + 1) = Mv at X ⊢
    generalize Mv * Mv + 𝔞 j * 𝔞 j = Dv at X ⊢
    linear_combination Mv * X

end cell

/-! ## The partial sums for `k = 1` -/

alias pw_one' := Common.pw_one

abbrev U1Inv (j M₀ L : PTm n) : Fm PTm n :=
  le (succ M₀ * (succ M₀ * fact L * gm zero (succ M₀) L))
    (succ M₀ * (succ M₀ * fact L * gm j (succ M₀) L) +
      succ M₀ * ap2 (sumF Jb) j (pairT one (pairT (succ M₀) L)) + j * (two * (fact L * fact L)))

abbrev D1Inv (j M₀ L : PTm n) : Fm PTm n :=
  le (succ M₀ * (succ M₀ * fact L * gm j (succ M₀) L) +
      succ M₀ * ap2 (sumF Jb) j (pairT one (pairT (succ M₀) L)))
    (succ M₀ * (succ M₀ * fact L * gm zero (succ M₀) L) + j * (two * (fact L * fact L)))

theorem u1_base (M₀ L : PTm n) : Γ ⊢[PRAAx] U1Inv zero M₀ L := by
  have z1 := natEq (sum_zero (Γ := Γ) Jb (pairT one (pairT (succ M₀) L)))
  ipra_le 0 using rw [z1]; ring

theorem d1_base (M₀ L : PTm n) : Γ ⊢[PRAAx] D1Inv zero M₀ L := by
  have z1 := natEq (sum_zero (Γ := Γ) Jb (pairT one (pairT (succ M₀) L)))
  ipra_le 0 using rw [z1]; ring

theorem u1_step {j M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (ih : Γ ⊢[PRAAx] U1Inv j M₀ L) : Γ ⊢[PRAAx] U1Inv (succ j) M₀ L := by
  have c := cell1_up hj hL
  have e1 := natEq (sum_succ' (Γ := Γ) Jb j (pairT one (pairT (succ M₀) L)))
  have e2 := natEq (inst_Jb (Γ := Γ) j one (succ M₀) L)
  have p1 := natEq (pw_one' (Γ := Γ) (sg j (succ M₀) L))
  ipra_le sl ih + sl c using rw [e1, e2, p1]; ring

theorem d1_step {j M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (hj : Γ ⊢[PRAAx] le (succ j) (succ M₀)) (ih : Γ ⊢[PRAAx] D1Inv j M₀ L) : Γ ⊢[PRAAx] D1Inv (succ j) M₀ L := by
  have c := cell1_dn hj hL
  have e1 := natEq (sum_succ' (Γ := Γ) Jb j (pairT one (pairT (succ M₀) L)))
  have e2 := natEq (inst_Jb (Γ := Γ) j one (succ M₀) L)
  have p1 := natEq (pw_one' (Γ := Γ) (sg j (succ M₀) L))
  ipra_le sl ih + sl c using rw [e1, e2, p1]; ring

/-- Variables: `0 = j` (induction), `1 = M₀`, `2 = L`. -/
private abbrev u1F : Fm PTm 3 :=
  le (two * (succ (var 1) * succ (var 1))) (var 2) ⟶ le (var 0) (succ (var 1)) ⟶ U1Inv (var 0) (var 1) (var 2)

private abbrev d1F : Fm PTm 3 :=
  le (two * (succ (var 1) * succ (var 1))) (var 2) ⟶ le (var 0) (succ (var 1)) ⟶ D1Inv (var 0) (var 1) (var 2)

private theorem u1₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] u1F := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (u1_base _ _))
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (u1_step Prf.hyp1 Prf.hyp0
      (Prf.impE (Prf.impE Prf.hyp1.wk Prf.hyp1) (le_trans (le_succ_self _) Prf.hyp0))))

private theorem d1₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] d1F := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (d1_base _ _))
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      subst_sg, subst_gm, subst_om, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (d1_step Prf.hyp1 Prf.hyp0
      (Prf.impE (Prf.impE Prf.hyp1.wk Prf.hyp1) (le_trans (le_succ_self _) Prf.hyp0))))

/-- `eq:Jrec` for `k = 1`: `|J_1(M) − 1| ≤ 2/M`, cleared: `|𝒥_1 − M F²| ≤ 2F²`. -/
theorem J1_bounds {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] le (succ M₀ * (fact L * fact L)) (J one (succ M₀) L + two * (fact L * fact L)) ⋏
      le (J one (succ M₀) L) (succ M₀ * (fact L * fact L) + two * (fact L * fact L)) := by
  have hu := inst (Γ := Γ) u1₀ (![succ M₀, M₀, L] : Fin 3 → PTm n)
  have hd := inst (Γ := Γ) d1₀ (![succ M₀, M₀, L] : Fin 3 → PTm n)
  simp at hu hd
  have u := Prf.impE (Prf.impE hu hL) (le_refl (succ M₀))
  have d := Prf.impE (Prf.impE hd hL) (le_refl (succ M₀))
  have gt := natEq (gm_top (Γ := Γ) (succ M₀) L)
  have g0 := natEq (gm_zero hL)
  refine .andI (mul_le_cancel (d' := M₀) ?_) (mul_le_cancel (d' := M₀) ?_)
  · ipra_le sl u using rw [gt, g0]; ring
  · ipra_le sl d using rw [gt, g0]; ring

/-! ## The iterated bounds (`eq:evenerr`, `eq:odderr`) -/

alias two_succ := Common.two_mul_succ

/-- `eq:evenerr`: `|J_{2m} − p_m J_0| ≤ 8m(m+1)/M`, cleared:
`|db m · 𝒥_{2m} − da m · F^{2m} 𝒥_0| ≤ 8m(m+1) · db m · F^{2m+1}`. -/
abbrev EvInv (m M₀ L : PTm n) : Fm PTm n :=
  le (db m * J (two * m) (succ M₀) L)
      (da m * (pw (fact L) (two * m) * J zero (succ M₀) L) +
        num 8 * (m * succ m) * (db m * pw (fact L) (succ (two * m)))) ⋏
    le (da m * (pw (fact L) (two * m) * J zero (succ M₀) L))
      (db m * J (two * m) (succ M₀) L + num 8 * (m * succ m) * (db m * pw (fact L) (succ (two * m))))

theorem ev_base (M₀ L : PTm n) : Γ ⊢[PRAAx] EvInv zero M₀ L := by
  have a0 := natEq (da_zero (Γ := Γ)); have b0 := natEq (db_zero (Γ := Γ))
  have ez : Γ ⊢[PRAAx] two * zero ≐ (zero : PTm n) := by ipra_ring
  have jz := natEq (congrAp2 (sumF Jb) (.eqRefl (succ M₀)) (congrPairT ez (.eqRefl (pairT (succ M₀) L))))
  have pz := natEq ((congrAp2 powF ez (.eqRefl (fact L))).eqTrans (pw_zero _))
  refine .andI ?_ ?_
  · ipra_le 0 using rw [a0, b0, jz, pz]; ring
  · ipra_le 0 using rw [a0, b0, jz, pz]; ring

theorem ev_step {m M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (ih : Γ ⊢[PRAAx] EvInv m M₀ L) : Γ ⊢[PRAAx] EvInv (succ m) M₀ L := by
  have r := wallis_rec_paper (i := two * m) hL
  have rU := Prf.andE₁ r; have rD := Prf.andE₂ r
  have ihU := Prf.andE₁ ih; have ihD := Prf.andE₂ ih
  have e2 := two_succ (Γ := Γ) m
  have qJ := natEq (congrAp2 (sumF Jb) (.eqRefl (succ M₀)) (congrPairT e2 (.eqRefl (pairT (succ M₀) L))))
  have pF := natEq (congrAp2 powF e2 (.eqRefl (fact L)))
  have pF' := natEq (congrAp2 powF (congrSucc e2) (.eqRefl (fact L)))
  have a1 := natEq (da_succ (Γ := Γ) m); have b1 := natEq (db_succ (Γ := Γ) m)
  have f1 := natEq (pw_succ (Γ := Γ) (fact L) (two * m))
  have f2 := natEq (pw_succ (Γ := Γ) (fact L) (succ (two * m)))
  have f3 := natEq (pw_succ (Γ := Γ) (fact L) (succ (succ (two * m))))
  refine .andI ?_ ?_
  · ipra_le 𝔞 (db m) * sl rU + (2 * 𝔞 m + 1) * (𝔞 (fact L) * 𝔞 (fact L)) * sl ihU +
        8 * ((𝔞 m + 1) * 𝔞 m) * (𝔞 (db m) * 𝔞 (pw (fact L) (succ (succ (succ (two * m)))))) using
      rw [qJ, pF, pF', a1, b1, f3, f2, f1]; ring
  · ipra_le 𝔞 (db m) * sl rD + (2 * 𝔞 m + 1) * (𝔞 (fact L) * 𝔞 (fact L)) * sl ihD +
        8 * ((𝔞 m + 1) * 𝔞 m) * (𝔞 (db m) * 𝔞 (pw (fact L) (succ (succ (succ (two * m)))))) using
      rw [qJ, pF, pF', a1, b1, f3, f2, f1]; ring

/-- Variables: `0 = m` (induction), `1 = M₀`, `2 = L`. -/
private abbrev evF : Fm PTm 3 :=
  le (two * (succ (var 1) * succ (var 1))) (var 2) ⟶ EvInv (var 0) (var 1) (var 2)

private theorem ev₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] evF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_num, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (ev_base _ _)
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_num, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (ev_step Prf.hyp0 (Prf.impE Prf.hyp1 Prf.hyp0))

theorem ev_all {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) (m : PTm n) :
    Γ ⊢[PRAAx] EvInv m M₀ L := by
  have h := inst (Γ := Γ) ev₀ (![m, M₀, L] : Fin 3 → PTm n)
  simp at h
  exact Prf.impE h hL

/-- The error constant `8m² + 16m + 12` of `eq:odderr`. -/
abbrev Em (m : PTm n) : PTm n := num 8 * (m * m) + num 16 * m + num 12

/-- `eq:odderr`: `|J_{2m+1} − q_m| ≤ (8m² + 16m + 12)/M`, cleared:
`|da (m+1) · 𝒥_{2m+1} − db m · M F^{2m+2}| ≤ (8m² + 16m + 12) · da (m+1) · F^{2m+2}`. -/
abbrev OdInv (m M₀ L : PTm n) : Fm PTm n :=
  le (da (succ m) * J (succ (two * m)) (succ M₀) L)
      (db m * (succ M₀ * pw (fact L) (two * succ m)) + Em m * (da (succ m) * pw (fact L) (two * succ m))) ⋏
    le (db m * (succ M₀ * pw (fact L) (two * succ m)))
      (da (succ m) * J (succ (two * m)) (succ M₀) L + Em m * (da (succ m) * pw (fact L) (two * succ m)))

theorem od_base {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) :
    Γ ⊢[PRAAx] OdInv zero M₀ L := by
  have jb := J1_bounds hL
  have j1 := Prf.andE₁ jb; have j2 := Prf.andE₂ jb
  have a1 := natEq (da_succ (Γ := Γ) zero)
  have a0 := natEq (da_zero (Γ := Γ)); have b0 := natEq (db_zero (Γ := Γ))
  have ez : Γ ⊢[PRAAx] two * zero ≐ (zero : PTm n) := by ipra_ring
  have e1 : Γ ⊢[PRAAx] two * succ zero ≐ (succ (succ zero) : PTm n) := by ipra_ring
  have jz := natEq (congrAp2 (sumF Jb) (.eqRefl (succ M₀))
    (congrPairT (congrSucc ez) (.eqRefl (pairT (succ M₀) L))))
  have pf := natEq ((congrAp2 powF e1 (.eqRefl (fact L))).eqTrans ((pw_succ (fact L) (succ zero)).eqTrans
    (congrMul ((pw_succ (fact L) zero).eqTrans (congrMul (pw_zero (fact L)) (.eqRefl (fact L))))
      (.eqRefl (fact L)))))
  refine .andI ?_ ?_
  · ipra_le sl j2 + 10 * (𝔞 (fact L) * 𝔞 (fact L)) using rw [a1, a0, b0, jz, pf]; ring
  · ipra_le sl j1 + 10 * (𝔞 (fact L) * 𝔞 (fact L)) using rw [a1, a0, b0, jz, pf]; ring

theorem od_step {m M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L)
    (ih : Γ ⊢[PRAAx] OdInv m M₀ L) : Γ ⊢[PRAAx] OdInv (succ m) M₀ L := by
  have r := wallis_rec_paper (i := succ (two * m)) hL
  have rU := Prf.andE₁ r; have rD := Prf.andE₂ r
  have ihU := Prf.andE₁ ih; have ihD := Prf.andE₂ ih
  have e2 := two_succ (Γ := Γ) m
  have e4 : Γ ⊢[PRAAx] two * succ (succ m) ≐ succ (succ (succ (succ (two * m)))) := by
    ipra_ring
  have qJ := natEq (congrAp2 (sumF Jb) (.eqRefl (succ M₀))
    (congrPairT (congrSucc e2) (.eqRefl (pairT (succ M₀) L))))
  have pF := natEq (congrAp2 powF e2 (.eqRefl (fact L)))
  have pF4 := natEq (congrAp2 powF e4 (.eqRefl (fact L)))
  have a2 := natEq (da_succ (Γ := Γ) (succ m)); have b1 := natEq (db_succ (Γ := Γ) m)
  have g3 := natEq (pw_succ (Γ := Γ) (fact L) (succ (succ (two * m))))
  have g4 := natEq (pw_succ (Γ := Γ) (fact L) (succ (succ (succ (two * m)))))
  refine .andI ?_ ?_
  · ipra_le 𝔞 (da (succ m)) * sl rU + (2 * 𝔞 m + 2) * (𝔞 (fact L) * 𝔞 (fact L)) * sl ihU +
        𝔞 (Em m) * (𝔞 (da (succ m)) * 𝔞 (pw (fact L) (succ (succ (succ (succ (two * m))))))) using
      rw [qJ, pF4, pF, a2, b1, g4, g3]; ring
  · ipra_le 𝔞 (da (succ m)) * sl rD + (2 * 𝔞 m + 2) * (𝔞 (fact L) * 𝔞 (fact L)) * sl ihD +
        𝔞 (Em m) * (𝔞 (da (succ m)) * 𝔞 (pw (fact L) (succ (succ (succ (succ (two * m))))))) using
      rw [qJ, pF4, pF, a2, b1, g4, g3]; ring

private abbrev odF : Fm PTm 3 :=
  le (two * (succ (var 1) * succ (var 1))) (var 2) ⟶ OdInv (var 0) (var 1) (var 2)

private theorem od₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] odF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_num, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (od_base Prf.hyp0)
  · simp only [Fm.subst_imp, Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_num, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (od_step Prf.hyp0 (Prf.impE Prf.hyp1 Prf.hyp0))

theorem od_all {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) (m : PTm n) :
    Γ ⊢[PRAAx] OdInv m M₀ L := by
  have h := inst (Γ := Γ) od₀ (![m, M₀, L] : Fin 3 → PTm n)
  simp at h
  exact Prf.impE h hL

/-! ## The finite Wallis inequality (`thm:finitewallis`) -/

/-- `D_m = 16 · 2^m (m + 1)²`. -/
abbrev Dm (m : PTm n) : PTm n := num 16 * pw two m * (succ m * succ m)

/-- The lower bound `W_m − D_m/M ≤ J_0(M)`, cleared by `M F · da m · da (m+1)`:
`M F (db m)² ≤ da m · da (m+1) · (𝒥_0 + D_m F)`. From `q_m − e ≤ J_{2m+1} ≤ J_{2m} ≤ p_m J_0 + e'`. -/
theorem finite_wallis_lower {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) (m : PTm n) :
    Γ ⊢[PRAAx] le (succ M₀ * fact L * (db m * db m))
      (da m * da (succ m) * (J zero (succ M₀) L + Dm m * fact L)) := by
  have evU := Prf.andE₁ (ev_all hL m)
  have odD := Prf.andE₂ (od_all hL m)
  have mo := J_mono (k := two * m) hL
  have bl := db_le (Γ := Γ) m
  have pF := natEq (congrAp2 powF (two_succ (Γ := Γ) m) (.eqRefl (fact L)))
  have f1 := natEq (pw_succ (Γ := Γ) (fact L) (two * m))
  have f2 := natEq (pw_succ (Γ := Γ) (fact L) (succ (two * m)))
  have hP := LeanProofs.IPRA.AnalyticNumberTheory.Valuation.pw_pos'
    (LeanProofs.IPRA.AnalyticNumberTheory.Primes.fact_pos (Γ := Γ) L) (succ (two * m))
  refine mul_le_cancel (d' := pred (pw (fact L) (succ (two * m))))
    (le_congr (congrMul hP (.eqRefl _)) (congrMul hP (.eqRefl _)) ?_)
  ipra_le 𝔞 (db m) * sl odD + 𝔞 (da (succ m)) * 𝔞 (db m) * sl mo + 𝔞 (da (succ m)) * 𝔞 (fact L) * sl evU +
      𝔞 (da (succ m)) * 𝔞 (pw (fact L) (succ (two * m))) * 𝔞 (fact L) *
        (16 * ((𝔞 m + 1) * (𝔞 m + 1)) * sl bl + (8 * 𝔞 m + 4) * 𝔞 (db m)) using
    rw [pF, f2, f1]; ring

/-- The upper bound `J_0(M) ≤ ((2m+1)/(2m)) W_m + D_m/M` for `m = r + 1`, cleared by
`2m · M F · da m · da (m+1)`: `2m · da m · da (m+1) · 𝒥_0 ≤ (2m+1) (db m)² M F + 2m · da m · da (m+1) · D_m F`.
From `p_m J_0 − e' ≤ J_{2m} ≤ J_{2m−1} ≤ q_{m−1} + e`. -/
theorem finite_wallis_upper {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) (r : PTm n) :
    Γ ⊢[PRAAx] le (two * succ r * (da (succ r) * da (succ (succ r))) * J zero (succ M₀) L)
      (succ (two * succ r) * (db (succ r) * db (succ r)) * (succ M₀ * fact L) +
        two * succ r * (da (succ r) * da (succ (succ r))) * (Dm (succ r) * fact L)) := by
  have evD := Prf.andE₂ (ev_all hL (succ r))
  have odU := Prf.andE₁ (od_all hL r)
  have mo := J_mono (k := succ (two * r)) hL
  have bl := db_le (Γ := Γ) (succ r)
  have qJ := natEq (congrAp2 (sumF Jb) (.eqRefl (succ M₀))
    (congrPairT (two_succ (Γ := Γ) r) (.eqRefl (pairT (succ M₀) L))))
  have a2 := natEq (da_succ (Γ := Γ) (succ r)); have b1 := natEq (db_succ (Γ := Γ) r)
  have f := natEq (pw_succ (Γ := Γ) (fact L) (two * succ r))
  have hP := LeanProofs.IPRA.AnalyticNumberTheory.Valuation.pw_pos'
    (LeanProofs.IPRA.AnalyticNumberTheory.Primes.fact_pos (Γ := Γ) L) (two * succ r)
  refine mul_le_cancel (d' := pred (pw (fact L) (two * succ r)))
    (le_congr (congrMul hP (.eqRefl _)) (congrMul hP (.eqRefl _)) ?_)
  ipra_le 2 * (𝔞 r + 1) * 𝔞 (da (succ (succ r))) * sl evD +
      2 * (𝔞 r + 1) * (𝔞 (da (succ (succ r))) * 𝔞 (db (succ r))) * sl mo +
      2 * (𝔞 r + 1) * (2 * 𝔞 r + 3) * (𝔞 (db (succ r)) * 𝔞 (fact L)) * sl odU +
      2 * (𝔞 r + 1) * (𝔞 (da (succ (succ r))) * 𝔞 (pw (fact L) (two * succ r)) * 𝔞 (fact L)) *
        (16 * ((𝔞 r + 2) * (𝔞 r + 2)) * sl bl + (24 * 𝔞 r + 36) * 𝔞 (db (succ r))) using
    rw [qJ, a2, b1, f]; ring

/-- `thm:finitewallis` (`eq:finitewallis`) for `m = r + 1 ≥ 1` and `M = M₀ + 1 ≥ 1`, cleared by `F = L!`
with `2M² ≤ L`: `W_m − D_m/M ≤ J_0(M) ≤ ((2m+1)/(2m)) W_m + D_m/M` with `W_m = (db m)²/(da m · da (m+1))`,
`J_0(M) = 𝒥_0/(M F)` and `D_m = 16 · 2^m (m+1)²`. -/
theorem finite_wallis {M₀ L : PTm n} (hL : Γ ⊢[PRAAx] le (two * (succ M₀ * succ M₀)) L) (r : PTm n) :
    Γ ⊢[PRAAx] le (succ M₀ * fact L * (db (succ r) * db (succ r)))
        (da (succ r) * da (succ (succ r)) * (J zero (succ M₀) L + Dm (succ r) * fact L)) ⋏
      le (two * succ r * (da (succ r) * da (succ (succ r))) * J zero (succ M₀) L)
        (succ (two * succ r) * (db (succ r) * db (succ r)) * (succ M₀ * fact L) +
          two * succ r * (da (succ r) * da (succ (succ r))) * (Dm (succ r) * fact L)) :=
  .andI (finite_wallis_lower hL (succ r)) (finite_wallis_upper hL r)

/-! ## The same code as in the Basel packet -/

open LeanProofs.IPRA.Analysis.BaselQuadrature (Qb inst_Qb) in
/-- `J_0(M) = 2 Q_M`: the Riemann sum naming `π/2` here is twice the code `Q_M` of `basel_ipra`
(`prop:quadrature`), `𝒥_0 = 2M · Q(M)`. -/
theorem J_zero_eq (M L : PTm n) :
    Γ ⊢[PRAAx] J zero M L ≐ two * M * LeanProofs.IPRA.Analysis.BaselQuadrature.Q M L := by
  refine sum_scale Jb Qb M (two * M) (pairT M L) (pairT zero (pairT M L)) (.allI (.impI ?_))
  simp only [shift_pairT]
  have e0 : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  have e2 : Syn.shift (two * M) = two * Syn.shift M := by simp [Syn.shift]
  rw [e0, e2]
  have a := natEq (inst_Jb (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) zero (Syn.shift M)
    (Syn.shift L))
  have b := natEq (inst_Qb (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) (Syn.shift M) (Syn.shift L))
  have c := natEq (pw_zero (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift)
    (sg (var 0) (Syn.shift M) (Syn.shift L)))
  apply deriveNat; simp only [om] at a ⊢; ipra_simps
  rw [a, b, c]
  ring

/-! ## The closed sentence -/

/-- Variables: `0 = r` (`m = r + 1`), `1 = M₀` (`M = M₀ + 1`), `2 = L`. -/
abbrev finiteWallisFormula : Fm PTm 3 :=
  le (two * (succ (var 1) * succ (var 1))) (var 2) ⟶
    (le (succ (var 1) * fact (var 2) * (db (succ (var 0)) * db (succ (var 0))))
        (da (succ (var 0)) * da (succ (succ (var 0))) *
          (J zero (succ (var 1)) (var 2) + Dm (succ (var 0)) * fact (var 2))) ⋏
      le (two * succ (var 0) * (da (succ (var 0)) * da (succ (succ (var 0)))) * J zero (succ (var 1)) (var 2))
        (succ (two * succ (var 0)) * (db (succ (var 0)) * db (succ (var 0))) * (succ (var 1) * fact (var 2)) +
          two * succ (var 0) * (da (succ (var 0)) * da (succ (succ (var 0)))) *
            (Dm (succ (var 0)) * fact (var 2))))

/-- `thm:finitewallis` as a closed sentence of iPRA. -/
theorem finite_wallis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 finiteWallisFormula :=
  closeUniv 3 (.impI (finite_wallis Prf.hyp0 (var 0)))

/-! ## An exact rational consequence: `W_m ≤ 2` -/

/-- The mesh `M₀ = D_m · da m · da (m+1)` (so `M = M₀ + 1`) at which the finite Wallis inequality is used. -/
abbrev Mw (m : PTm n) : PTm n := Dm m * (da m * da (succ m))
/-- The clearing bound `L = 2M²` for that mesh. -/
abbrev Lw (m : PTm n) : PTm n := two * (succ (Mw m) * succ (Mw m))

/-- `W_m ≤ 2`: `(db m)² ≤ 2 · da m · da (m+1)`. The paper substitutes a large mesh in `eq:finitewallis` and
uses `J_0 ≤ 2` and the discreteness of the integers; here the mesh is `M = D_m · da m · da (m+1) + 1`, with
`J_0 ≤ 2` from `Q_M ≤ 1` (`BaselRiemann.Q_le`), and the case `2 · da m · da (m+1) < (db m)²` is refuted. No
limit is taken. -/
theorem wallis_le_two (m : PTm n) : Γ ⊢[PRAAx] le (db m * db m) (two * (da m * da (succ m))) := by
  have hL : Γ ⊢[PRAAx] le (two * (succ (Mw m) * succ (Mw m))) (Lw m) := le_refl _
  have lo := finite_wallis_lower hL m
  have jz := natEq (J_zero_eq (Γ := Γ) (succ (Mw m)) (Lw m))
  have ql := LeanProofs.IPRA.Analysis.BaselRiemann.Q_le hL
  have hF := LeanProofs.IPRA.AnalyticNumberTheory.Primes.fact_pos (Γ := Γ) (Lw m)
  have h1 : Γ ⊢[PRAAx] le (succ (Mw m) * (db m * db m))
      (da m * da (succ m) * (two * succ (Mw m) + Dm m)) := by
    refine mul_le_cancel (d' := pred (fact (Lw m)))
      (le_congr (congrMul hF (.eqRefl _)) (congrMul hF (.eqRefl _)) ?_)
    ipra_le sl lo + 2 * (𝔞 (da m) * 𝔞 (da (succ m))) * (𝔞 (Mw m) + 1) * sl ql using
      rw [jz]; ring
  refine .orE (lt_or_le (two * (da m * da (succ m))) (db m * db m)) ?_ Prf.hyp0
  have h0 : (lt (two * (da m * da (succ m))) (db m * db m) :: Γ) ⊢[PRAAx]
      le (succ (two * (da m * da (succ m)))) (db m * db m) := Prf.hyp0
  have h2 : (lt (two * (da m * da (succ m))) (db m * db m) :: Γ) ⊢[PRAAx]
      le (succ (da m * da (succ m) * (two * succ (Mw m) + Dm m))) (succ (Mw m) * (db m * db m)) := by
    ipra_le (𝔟 (Mw m) + 1) * sl h0
  exact not_succ_le_self _ _ (le_trans h2 h1.wk)

/-- Variable `0 = m`. -/
abbrev wallisTwoFormula : Fm PTm 1 :=
  le (db (var 0) * db (var 0)) (two * (da (var 0) * da (succ (var 0))))

/-- `W_m ≤ 2` as a closed sentence: `∀ m, ((2m)!!)² ≤ 2 (2m − 1)!! (2m + 1)!!`. -/
theorem wallis_le_two_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 wallisTwoFormula :=
  closeUniv 1 (wallis_le_two (var 0))

end LeanProofs.IPRA.Analysis.WallisFinite
