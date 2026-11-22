import IPRADerivations.Probability.Independence
import IPRADerivations.AnalyticNumberTheory.Mobius

/-!
# Exchanging a weighted sum with a sum over divisors

A reusable rearrangement, used for the expansion of the square in the proof of `thm:finite-sieve`
(`analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`: "Sum `eq:sieve-majorant` over the
progression. Expanding its square …"), where a sum over `n` of `(Σ_{d ∣ n} λ_d)²` is rewritten as a sum over the
pairs `(d, e)` of the number of `n` divisible by both.

For natural bodies `c(n, y)` and `u(d, y)` with a common parameter `y`:

  `Σ_{n<X} c(n) · Σ_{d<Z} [d ∣ n] u(d) = Σ_{d<Z} u(d) · Σ_{n<X} c(n) [d ∣ n]`            (`div_exchange`).

* `dvB u`: the body `[d ∣ n] u(d, y)` over `(d, ⟨n, y⟩)`; `mdB c`: the body `c(n, y) [d ∣ n]` over `(n, ⟨d, y⟩)`;
* `LW c u`, `RW c u`: the two outer bodies, over `(n, ⟨Z, y⟩)` and `(d, ⟨X, y⟩)`;
* `LW_row`, `RW_col`: they are the row and column sums of `aB c u (n, d, y) = c(n, y) [d ∣ n] u(d, y)`
  (`Independence.sum_scale`), and `Core/Fubini.fubini` exchanges the two sums.

The indicator is `[n mod d = 0]`; a body `u` that vanishes at `d = 0` restricts the sum to `d ≥ 1`. Since `mdB c` is
again a body in `n`, the lemma iterates: `mdB (mdB c)` is `c(n) [d ∣ n] [e ∣ n]`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.Probability.Independence (row_pt col_pt sum_scale shift_inst2)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `C (E U) = U (C E)`. -/
theorem rot (C E U : PTm n) : Γ ⊢[PRAAx] C * (E * U) ≐ U * (C * E) := by
  apply deriveNat; ipra_simps; ring

section Exchange

variable (c u : PTm 2)

/-! ## Bodies -/

/-- `[d ∣ n] u(d, y)` over `0 = d`, `1 = ⟨n, y⟩`. -/
def dvB : PTm 2 := eqb (rem (fstT (var 1)) (var 0)) zero * Syn.subst ![var 0, sndT (var 1)] u

theorem inst2_dvB (d z : PTm n) : inst2 (dvB u) d z = eqb (rem (fstT z) d) zero * inst2 u d (sndT z) := by
  have hf : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (var 1)] u) = inst2 u d (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, dvB, PTm.subst_mul, hf]
  simp

theorem dvB_at (d m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (dvB u) d (pairT m y) ≐ eqb (rem m d) zero * inst2 u d y := by
  rw [inst2_dvB]
  exact congrMul (congrEqb' (congrAp2 remF (fst_pair m y) (.eqRefl d)) (.eqRefl zero))
    (congrInst2 u (.eqRefl _) (snd_pair m y))

/-- `c(m, y) [d ∣ m]` over `0 = m`, `1 = ⟨d, y⟩`. -/
def mdB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] c * eqb (rem (var 0) (fstT (var 1))) zero

theorem inst2_mdB (m z : PTm n) : inst2 (mdB c) m z = inst2 c m (sndT z) * eqb (rem m (fstT z)) zero := by
  have hf : Syn.subst ![m, z] (Syn.subst ![var 0, sndT (var 1)] c) = inst2 c m (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, mdB, PTm.subst_mul, hf]
  simp

theorem mdB_at (m d y : PTm n) :
    Γ ⊢[PRAAx] inst2 (mdB c) m (pairT d y) ≐ inst2 c m y * eqb (rem m d) zero := by
  rw [inst2_mdB]
  exact congrMul (congrInst2 c (.eqRefl _) (snd_pair d y))
    (congrEqb' (congrAp2 remF (.eqRefl m) (fst_pair d y)) (.eqRefl zero))

/-- `c(m, y) [d ∣ m] u(d, y)` over `(m, d, y)`. -/
def aB : PTm 3 :=
  Syn.subst ![var 0, var 2] c * (eqb (rem (var 0) (var 1)) zero * Syn.subst ![var 1, var 2] u)

theorem inst3_aB (m d y : PTm n) :
    inst3 (aB c u) m d y = inst2 c m y * (eqb (rem m d) zero * inst2 u d y) := by
  have hc : Syn.subst ![m, d, y] (Syn.subst ![var 0, var 2] c) = inst2 c m y := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
  have hu : Syn.subst ![m, d, y] (Syn.subst ![var 1, var 2] u) = inst2 u d y := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
  simp only [inst3, aB, PTm.subst_mul, hc, hu]
  simp

/-- `c(m, y) · Σ_{d<Z} [d ∣ m] u(d, y)` over `0 = m`, `1 = ⟨Z, y⟩`. -/
def LW : PTm 2 :=
  Syn.subst ![var 0, sndT (var 1)] c * ap2 (sumF (dvB u)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_LW (m z : PTm n) :
    inst2 (LW c u) m z = inst2 c m (sndT z) * ap2 (sumF (dvB u)) (fstT z) (pairT m (sndT z)) := by
  have hf : Syn.subst ![m, z] (Syn.subst ![var 0, sndT (var 1)] c) = inst2 c m (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, LW, PTm.subst_mul, hf]
  simp

theorem LW_at (m Z y : PTm n) :
    Γ ⊢[PRAAx] inst2 (LW c u) m (pairT Z y) ≐ inst2 c m y * ap2 (sumF (dvB u)) Z (pairT m y) := by
  rw [inst2_LW]
  exact congrMul (congrInst2 c (.eqRefl _) (snd_pair Z y))
    (congrAp2 _ (fst_pair Z y) (congrPairT (.eqRefl _) (snd_pair Z y)))

/-- `u(d, y) · Σ_{m<X} c(m, y) [d ∣ m]` over `0 = d`, `1 = ⟨X, y⟩`. -/
def RW : PTm 2 :=
  Syn.subst ![var 0, sndT (var 1)] u * ap2 (sumF (mdB c)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_RW (d z : PTm n) :
    inst2 (RW c u) d z = inst2 u d (sndT z) * ap2 (sumF (mdB c)) (fstT z) (pairT d (sndT z)) := by
  have hf : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (var 1)] u) = inst2 u d (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, RW, PTm.subst_mul, hf]
  simp

theorem RW_at (d X y : PTm n) :
    Γ ⊢[PRAAx] inst2 (RW c u) d (pairT X y) ≐ inst2 u d y * ap2 (sumF (mdB c)) X (pairT d y) := by
  rw [inst2_RW]
  exact congrMul (congrInst2 u (.eqRefl _) (snd_pair X y))
    (congrAp2 _ (fst_pair X y) (congrPairT (.eqRefl _) (snd_pair X y)))

/-! ## Rows and columns -/

/-- The left body is the row sum of `aB`. -/
theorem LW_row (m Z y : PTm n) :
    Γ ⊢[PRAAx] inst2 (LW c u) m (pairT Z y) ≐ inst2 (oB (aB c u)) m (pairT Z y) := by
  rw [inst2_oB]
  have eR : Γ ⊢[PRAAx] ap2 (sumF (rowB (aB c u))) (fstT (pairT Z y)) (pairT m (sndT (pairT Z y))) ≐
      ap2 (sumF (rowB (aB c u))) Z (pairT m y) :=
    congrAp2 _ (fst_pair Z y) (congrPairT (.eqRefl _) (snd_pair Z y))
  have sc : Γ ⊢[PRAAx] ap2 (sumF (rowB (aB c u))) Z (pairT m y) ≐
      inst2 c m y * ap2 (sumF (dvB u)) Z (pairT m y) := by
    refine sum_scale (rowB (aB c u)) (dvB u) Z (inst2 c m y) (pairT m y) (pairT m y) (.allI (.impI ?_))
    rw [shift_pairT, shift_inst2]
    refine (row_pt (aB c u) _ _ _).eqTrans ?_
    rw [inst3_aB]
    exact congrMul (.eqRefl _) (dvB_at u _ _ _).eqSymm
  exact (LW_at c u m Z y).eqTrans (sc.eqSymm.eqTrans eR.eqSymm)

/-- The column sum of `aB` is the right body. -/
theorem RW_col (d X y : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (aB c u)) d (pairT X y) ≐ inst2 (RW c u) d (pairT X y) := by
  rw [inst2_pB]
  have eL : Γ ⊢[PRAAx] ap2 (sumF (colB (aB c u))) (fstT (pairT X y)) (pairT d (sndT (pairT X y))) ≐
      ap2 (sumF (colB (aB c u))) X (pairT d y) :=
    congrAp2 _ (fst_pair X y) (congrPairT (.eqRefl _) (snd_pair X y))
  have sc : Γ ⊢[PRAAx] ap2 (sumF (colB (aB c u))) X (pairT d y) ≐
      inst2 u d y * ap2 (sumF (mdB c)) X (pairT d y) := by
    refine sum_scale (colB (aB c u)) (mdB c) X (inst2 u d y) (pairT d y) (pairT d y) (.allI (.impI ?_))
    rw [shift_pairT, shift_inst2]
    refine (col_pt (aB c u) _ _ _).eqTrans ?_
    rw [inst3_aB]
    exact (rot _ _ _).eqTrans (congrMul (.eqRefl _) (mdB_at c _ _ _).eqSymm)
  exact eL.eqTrans (sc.eqTrans (RW_at c u d X y).eqSymm)

/-! ## The exchange -/

/-- `Σ_{m<X} c(m) · Σ_{d<Z} [d ∣ m] u(d) = Σ_{d<Z} u(d) · Σ_{m<X} c(m) [d ∣ m]`. -/
theorem div_exchange (X Z y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (LW c u)) X (pairT Z y) ≐ ap2 (sumF (RW c u)) Z (pairT X y) := by
  have e1 : Γ ⊢[PRAAx] ap2 (sumF (LW c u)) X (pairT Z y) ≐ ap2 (sumF (oB (aB c u))) X (pairT Z y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    exact LW_row c u _ _ _
  have e3 : Γ ⊢[PRAAx] ap2 (sumF (pB (aB c u))) Z (pairT X y) ≐ ap2 (sumF (RW c u)) Z (pairT X y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    exact RW_col c u _ _ _
  exact e1.eqTrans ((fubini (aB c u) X Z y).eqTrans e3)

end Exchange

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorExchange
