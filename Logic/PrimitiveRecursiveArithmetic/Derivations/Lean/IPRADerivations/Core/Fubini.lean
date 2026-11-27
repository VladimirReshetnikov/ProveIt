import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.MultiSums

/-!
# Exchanging finite sums, and weighted delta sums

Reusable sum tools (the "finite Fubini" of `expected_value_ipra_2026-11-16`,
Corollary `cor:finite-fubini`):

* `fubini`: `∑_{i<M} ∑_{j<N} a(i, j, x) = ∑_{j<N} ∑_{i<M} a(i, j, x)` for a body `a : PTm 3`;
* `sum_delta`: `∑_{j<N} [c = j] · G(j, x) = G(c, x)` for `c < N`.

Nested sums are single `sumF` sums whose bodies contain a `sumF` term and read a pair parameter:
`rowB a (j, ⟨i, x⟩) = a(i, j, x)`, `colB a (i, ⟨j, x⟩) = a(i, j, x)`,
`oB a (i, ⟨N, x⟩) = ∑_{j<N} a(i, j, x)` and `pB a (j, ⟨M, x⟩) = ∑_{i<M} a(i, j, x)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem congrPairT {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] pairT a b ≐ pairT a' b' := by
  have h := Prf.eqCongr (Γ := Γ) (pairT (var 0) (var 1) : PTm 2) (σ := ![a, b]) (σ' := ![a', b'])
    (fun j => by fin_cases j <;> assumption)
  simpa using h

/-! ## The zero body -/

/-- `∑_{i<N} 0 = 0`. -/
theorem sum_zeroB (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (zero : PTm 2)) N x ≐ zero := by
  refine sum_zero_of_all _ x (.allI ?_) N
  simp only [inst2, ConciseIPRA.PTm.subst_zero]
  exact .eqRefl _

/-! ## Fubini -/

/-- `a(fst z, j, snd z)`: the row `i = fst z`. -/
def rowB (a : PTm 3) : PTm 2 := Syn.subst ![fstT (var 1), var 0, sndT (var 1)] a
/-- `a(i, fst z, snd z)`: the column `j = fst z`. -/
def colB (a : PTm 3) : PTm 2 := Syn.subst ![var 0, fstT (var 1), sndT (var 1)] a
/-- The row sum `∑_{j < fst y} a(i, j, snd y)`. -/
def oB (a : PTm 3) : PTm 2 := ap2 (sumF (rowB a)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))
/-- The column sum `∑_{i < fst y} a(i, j, snd y)`. -/
def pB (a : PTm 3) : PTm 2 := ap2 (sumF (colB a)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_rowB (a : PTm 3) (j z : PTm n) : inst2 (rowB a) j z = inst3 a (fstT z) j (sndT z) := by
  simp only [inst2, inst3, rowB, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem inst2_colB (a : PTm 3) (i z : PTm n) : inst2 (colB a) i z = inst3 a i (fstT z) (sndT z) := by
  simp only [inst2, inst3, colB, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem inst2_oB (a : PTm 3) (i y : PTm n) :
    inst2 (oB a) i y = ap2 (sumF (rowB a)) (fstT y) (pairT i (sndT y)) := by simp [inst2, oB]

theorem inst2_pB (a : PTm 3) (j y : PTm n) :
    inst2 (pB a) j y = ap2 (sumF (colB a)) (fstT y) (pairT j (sndT y)) := by simp [inst2, pB]

theorem shift_succ'' (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]

/-- The row sum at `i = M`, as an outer term. -/
theorem oB_at (a : PTm 3) (M N x : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB a) M (pairT N x) ≐ ap2 (sumF (rowB a)) N (pairT M x) := by
  rw [inst2_oB]
  exact congrAp2 (sumF (rowB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

theorem fub_point (a : PTm 3) (M j x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB a) j (pairT (succ M) x) ≐ inst2 (addBody (pB a) (rowB a)) j (pairT M x) := by
  rw [inst2_addBody, inst2_pB, inst2_pB, inst2_rowB]
  have e₁ : Γ ⊢[PRAAx] ap2 (sumF (colB a)) (fstT (pairT (succ M) x)) (pairT j (sndT (pairT (succ M) x))) ≐
      ap2 (sumF (colB a)) M (pairT j x) + inst3 a M j x := by
    refine (congrAp2 (sumF (colB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      ((sum_succ' (colB a) M (pairT j x)).eqTrans (congrAdd (.eqRefl _) ?_))
    rw [inst2_colB]
    exact congrInst3 a (.eqRefl _) (fst_pair _ _) (snd_pair _ _)
  have e₂ : Γ ⊢[PRAAx] ap2 (sumF (colB a)) (fstT (pairT M x)) (pairT j (sndT (pairT M x))) ≐
      ap2 (sumF (colB a)) M (pairT j x) :=
    congrAp2 (sumF (colB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  exact e₁.eqTrans (congrAdd e₂ (congrInst3 a (fst_pair _ _) (.eqRefl _) (snd_pair _ _))).eqSymm

theorem fub_step (a : PTm 3) {M N x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF (oB a)) M (pairT N x) ≐ ap2 (sumF (pB a)) N (pairT M x)) :
    Γ ⊢[PRAAx] ap2 (sumF (oB a)) (succ M) (pairT N x) ≐ ap2 (sumF (pB a)) N (pairT (succ M) x) := by
  have eL := (sum_succ' (Γ := Γ) (oB a) M (pairT N x)).eqTrans (congrAdd ih (oB_at a M N x))
  have eR : Γ ⊢[PRAAx] ap2 (sumF (pB a)) N (pairT (succ M) x) ≐
      ap2 (sumF (pB a)) N (pairT M x) + ap2 (sumF (rowB a)) N (pairT M x) := by
    refine (sum_congr_bounded (pB a) (addBody (pB a) (rowB a)) (pairT (succ M) x) (pairT M x) N
      (.allI (.impI ?_))).eqTrans (sum_add (pB a) (rowB a) N (pairT M x))
    rw [shift_pairT, shift_pairT, shift_succ'']
    exact fub_point a _ _ _
  exact eL.eqTrans eR.eqSymm

/-- Variables: `0 = M`, `1 = N`, `2 = x`. -/
private abbrev fubF (a : PTm 3) : Fm PTm 3 :=
  ap2 (sumF (oB a)) (var 0) (pairT (var 1) (var 2)) ≐ ap2 (sumF (pB a)) (var 1) (pairT (var 0) (var 2))

private theorem fub₀ (a : PTm 3) : ([] : List (Fm PTm 3)) ⊢[PRAAx] fubF a := by
  ipra_ind [subst_ap2, subst_pairT]
  · refine (sum_zero _ _).eqTrans (.eqSymm ?_)
    -- every column sum over `i < 0` vanishes
    refine (sum_congr_bounded (pB a) (zero : PTm 2) (pairT zero (var 1)) (pairT zero (var 1)) (var 0)
      (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    have e : inst2 (zero : PTm 2) (var 0 : PTm 3) (Syn.shift (pairT (zero : PTm 2) (var 1))) = zero := by
      simp [inst2]
    have e0 : Syn.shift (zero : PTm 2) = zero := by simp [Syn.shift]
    rw [e, inst2_pB, shift_pairT, e0]
    exact (congrAp2 (sumF (colB a)) (fst_pair _ _) (.eqRefl _)).eqTrans (sum_zero _ _)
  · exact fub_step a Prf.hyp0

/-- `∑_{i<M} ∑_{j<N} a(i, j, x) = ∑_{j<N} ∑_{i<M} a(i, j, x)`. -/
theorem fubini (a : PTm 3) (M N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (oB a)) M (pairT N x) ≐ ap2 (sumF (pB a)) N (pairT M x) := by
  have h := inst (Γ := Γ) (fub₀ a) (![M, N, x] : Fin 3 → PTm n)
  simpa using h

/-! ## Weighted delta sums -/

/-- `[fst z = j] · G(j, snd z)`. -/
def dB (G : PTm 2) : PTm 2 := eqb (fstT (var 1)) (var 0) * Syn.subst ![var 0, sndT (var 1)] G

theorem inst2_dB (G : PTm 2) (j z : PTm n) : inst2 (dB G) j z = eqb (fstT z) j * inst2 G j (sndT z) := by
  simp only [inst2, dB, PTm.subst_mul, Syn.subst_subst]
  congr 1
  · simp
  · congr 1; funext k; fin_cases k <;> simp

/-- `D(N) = ∑_{j<N} [c = j] G(j, x)`. -/
abbrev dS (G : PTm 2) (N c x : PTm n) : PTm n := ap2 (sumF (dB G)) N (pairT c x)

theorem dS_succ (G : PTm 2) (N c x : PTm n) :
    Γ ⊢[PRAAx] dS G (succ N) c x ≐ dS G N c x + eqb c N * inst2 G N x := by
  refine (sum_succ' (dB G) N (pairT c x)).eqTrans (congrAdd (.eqRefl _) ?_)
  rw [inst2_dB]
  unfold eqb
  exact congrMul (congrMonus (.eqRefl _) (congrAdd (congrMonus (fst_pair _ _) (.eqRefl _))
    (congrMonus (.eqRefl _) (fst_pair _ _)))) (congrInst2 G (.eqRefl _) (snd_pair _ _))

section DeltaStep

variable (G : PTm 2) {N c x : PTm n}

theorem dstep_above (ihB : Γ ⊢[PRAAx] le N c ⟶ (dS G N c x ≐ zero)) (h : Γ ⊢[PRAAx] le (succ N) c) :
    Γ ⊢[PRAAx] dS G (succ N) c x ≐ zero :=
  (dS_succ G N c x).eqTrans ((congrAdd (Prf.impE ihB (le_trans (le_succ_self N) h))
    ((congrMul (eqb_zero_of_gt h) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (add_zero _))

theorem dstep_lt (ihA : Γ ⊢[PRAAx] lt c N ⟶ (dS G N c x ≐ inst2 G c x)) (h : Γ ⊢[PRAAx] lt c N) :
    Γ ⊢[PRAAx] dS G (succ N) c x ≐ inst2 G c x :=
  (dS_succ G N c x).eqTrans ((congrAdd (Prf.impE ihA h)
    ((congrMul (eqb_zero_of_lt h) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (add_zero _))

theorem dstep_eq (ihB : Γ ⊢[PRAAx] le N c ⟶ (dS G N c x ≐ zero)) (h : Γ ⊢[PRAAx] c ≐ N) :
    Γ ⊢[PRAAx] dS G (succ N) c x ≐ inst2 G c x :=
  (dS_succ G N c x).eqTrans ((congrAdd (Prf.impE ihB (le_congr (.eqRefl _) h.eqSymm (le_refl N)))
    ((congrMul (eqb_of_eq h) (congrInst2 G h.eqSymm (.eqRefl _))).eqTrans (one_mul _))).eqTrans (zero_add _))

theorem dstep (ihA : Γ ⊢[PRAAx] lt c N ⟶ (dS G N c x ≐ inst2 G c x))
    (ihB : Γ ⊢[PRAAx] le N c ⟶ (dS G N c x ≐ zero)) :
    Γ ⊢[PRAAx] (lt c (succ N) ⟶ (dS G (succ N) c x ≐ inst2 G c x)) ⋏
      (le (succ N) c ⟶ (dS G (succ N) c x ≐ zero)) :=
  .andI (.impI (.orE (Order.lt_succ_cases Prf.hyp0)
      (dstep_lt G ihA.wk.wk Prf.hyp0) (dstep_eq G ihB.wk.wk Prf.hyp0)))
    (.impI (dstep_above G ihB.wk Prf.hyp0))

end DeltaStep

/-- Variables: `0 = N`, `1 = c`, `2 = x`. -/
private abbrev dltF (G : PTm 2) : Fm PTm 3 :=
  (lt (var 1) (var 0) ⟶ (dS G (var 0) (var 1) (var 2) ≐ inst2 G (var 1) (var 2))) ⋏
    (le (var 0) (var 1) ⟶ (dS G (var 0) (var 1) (var 2) ≐ zero))

private theorem dlt₀ (G : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] dltF G := by
  ipra_ind (⟨⟨lt_QF _ _, trivial⟩, ⟨le_QF _ _, trivial⟩⟩) [subst_lt, subst_le, subst_ap2, subst_pairT, subst_inst2]
  · exact .andI (.impI (lt_zero_absurd _ Prf.hyp0)) (.impI (sum_zero _ _))
  · exact dstep G (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)

/-- `∑_{j<N} [c = j] · G(j, x) = G(c, x)` for `c < N`. -/
theorem sum_delta (G : PTm 2) {N c x : PTm n} (h : Γ ⊢[PRAAx] lt c N) :
    Γ ⊢[PRAAx] ap2 (sumF (dB G)) N (pairT c x) ≐ inst2 G c x := by
  have i := inst (Γ := Γ) (dlt₀ G) (![N, c, x] : Fin 3 → PTm n)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_le, subst_ap2, subst_pairT, subst_inst2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact Prf.impE (Prf.andE₁ i) h

end LeanProofs.IPRA
