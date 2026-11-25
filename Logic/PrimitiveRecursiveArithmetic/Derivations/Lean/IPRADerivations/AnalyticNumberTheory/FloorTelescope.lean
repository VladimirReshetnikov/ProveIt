import IPRADerivations.AnalyticNumberTheory.TauLogAbel

/-!
# Floor telescoping and the cube identity (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
"a finite rectangle comparison gives `Σ_{d≤x} d^{−3/4} ≤ 1 + ∫_1^x t^{−3/4} dt ≤ 4x^{1/4}`. Consequently the last
error is at most `1280x`." The integer route to these sublinear sums is a layer-cake count over fourth roots,
whose two arithmetic ingredients are proved here:

* `cube_sum`: `Σ_{j<N} (3j² + 3j + 1) = N³`;
* `floor_step`: `⌊x/(N+1)²⌋ + ⌊x/(N+1)⌋ ≤ ⌊x/N⌋` for `N ≥ 1`
  (`(1/(N+1)² + 1/(N+1)) N ≤ 1` and `⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋`);
* `floor_square_sum`: `Σ_{j≤N} ⌊x/j²⌋ ≤ 2x` — the integer form of `ζ(2) ≤ 2`, by telescoping `floor_step`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.FloorTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel (quo_one')
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop (quo_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The cube identity -/

/-- `3j² + 3j + 1`. -/
abbrev cB : PTm 2 := succ (succ two * (var 0 * var 0 + var 0))

theorem inst2_cB (j x : PTm n) : inst2 cB j x = succ (succ two * (j * j + j)) := by simp [inst2]

/-- Variable `0 = N`, `1 = x`. -/
private abbrev cubeF : Fm PTm 2 := ap2 (sumF cB) (var 0) (var 1) ≐ var 0 * var 0 * var 0

private theorem cube₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] cubeF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have e := natEq (sum_zero (Γ := ([] : List (Fm PTm 1))) cB (var 0))
    apply deriveNat; ipra_simps; linear_combination e
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih := natEq (Prf.hyp0 : [cubeF] ⊢[PRAAx] cubeF)
    have s := sum_succ' (Γ := [cubeF]) cB (var 0) (var 1)
    rw [inst2_cB] at s
    have e := natEq s
    apply deriveNat; ipra_simps; linear_combination e + ih

/-- `Σ_{j<N} (3j² + 3j + 1) = N³`. -/
theorem cube_sum (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF cB) N x ≐ N * N * N := by
  simpa using inst (Γ := Γ) cube₀ (![N, x] : Fin 2 → PTm n)

/-! ## Floor telescoping -/

theorem sq_pos (N : PTm n) : Γ ⊢[PRAAx] succ N * succ N ≐ succ (pred (succ N * succ N)) :=
  pos_of_lt_zero (le_of_eq_add (d := N * N + two * N) (by ipra_ring))

/-- `⌊x/(N+1)²⌋ + ⌊x/(N+1)⌋ ≤ ⌊x/N⌋` for `N ≥ 1`. -/
theorem floor_step {N : PTm n} (x : PTm n) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] le (quo x (succ N * succ N) + quo x (succ N)) (quo x N) := by
  refine le_quo_of_mul_le hN ?_
  have f1 := le_scale N (quo_mul_le (x := x) (sq_pos (Γ := Γ) N))
  have f2 := le_scale (N * succ N) (quo_mul_le (x := x) (congrSucc (pred_succ N).eqSymm : Γ ⊢[PRAAx] succ N ≐ succ (pred (succ N))))
  refine mul_le_cancel (d' := N * N + two * N) ?_
  have c : Γ ⊢[PRAAx] le (succ (N * N + two * N) * (N * (quo x (succ N * succ N) + quo x (succ N))))
      (succ (N * N + two * N) * x) := by
    ipra_le sl f1 + sl f2 + 𝔞 x
  exact c

/-- The body `⌊x/(j+1)²⌋`. -/
abbrev qB : PTm 2 := quo (var 1) (succ (var 0) * succ (var 0))

theorem inst2_qB (j x : PTm n) : inst2 qB j x = quo x (succ j * succ j) := by simp [inst2]

/-- Variable `0 = k`, `1 = x`: `Σ_{j<k+1} ⌊x/(j+1)²⌋ + ⌊x/(k+1)⌋ ≤ 2x`. -/
private abbrev telF : Fm PTm 2 :=
  le (ap2 (sumF qB) (succ (var 0)) (var 1) + quo (var 1) (succ (var 0))) (two * var 1)

private theorem tel₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] telF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have s := sum_succ' (Γ := ([] : List (Fm PTm 1))) qB zero (var 0)
    rw [inst2_qB] at s
    have e1 := natEq s
    have e0 := natEq (sum_zero (Γ := ([] : List (Fm PTm 1))) qB (var 0))
    have q1 := natEq (quo_one' (Γ := ([] : List (Fm PTm 1))) (var 0))
    have q11 : ([] : List (Fm PTm 1)) ⊢[PRAAx] quo (var 0) (succ zero * succ zero) ≐ quo (var 0) (succ zero) :=
      congrAp2 quoF (.eqRefl _) (by ipra_ring)
    have e11 := natEq q11
    ipra_le 0 with e1 + e0 + e11 + 2 * q1
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [telF] ⊢[PRAAx] telF := Prf.hyp0
    have s := sum_succ' (Γ := [telF]) qB (succ (var 0)) (var 1)
    rw [inst2_qB] at s
    have e := natEq s
    have st := floor_step (Γ := [telF]) (var 1) (congrSucc (pred_succ _).eqSymm : [telF] ⊢[PRAAx] succ (var 0) ≐ succ (pred (succ (var 0))))
    ipra_le sl ih + sl st with e

/-- `Σ_{j≤k+1} ⌊x/j²⌋ ≤ 2x`. -/
theorem floor_square_sum (k x : PTm n) : Γ ⊢[PRAAx] le (ap2 (sumF qB) (succ k) x) (two * x) := by
  have h := inst (Γ := Γ) tel₀ (![k, x] : Fin 2 → PTm n)
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact le_trans (le_add_right _ _) h

end LeanProofs.IPRA.AnalyticNumberTheory.FloorTelescope
