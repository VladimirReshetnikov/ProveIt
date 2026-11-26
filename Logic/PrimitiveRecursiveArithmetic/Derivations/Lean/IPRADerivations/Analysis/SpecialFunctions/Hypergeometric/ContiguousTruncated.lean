import IPRADerivations.Analysis.SpecialFunctions.Hypergeometric.ContiguousRelations

/-!
# A truncated contiguous relation of the Gauss series

Packets: `foundations/pcfm_ipra_framework_2026-11-16`, `paper/sections/12_examples.tex`, Theorem "Finite
contiguous relation" ("for every `N`, the exact truncated identity is derivable in iPRA ... at the successor
step subtract the `N`-case from the `N + 1`-case; only the newly added summands remain"), for the finite sums
`S_N(a, b; c; z) = ∑_{n<N} (a)_n (b)_n / ((c)_n n!) z^n`; and `analysis/hypergeometric_ipra_2026-11-16`, the
contiguous relations `eq:contig-a+`, `eq:contig-b+` summed.

With an arbitrary weight `w(k, y)` (the cleared `z^k / ((c)_k k!)`) and the numerators
`T_k(a, b) = (a)_k (b)_k` (`ContiguousRelations.Tn`), the truncated sums are read from the parameter
`⟨a, ⟨b, y⟩⟩`:

* `TAB`, `TBB`, `T0B` (with `TA_at`, `TB_at`, `T0_at`): the summands `w_k T_k(a + 1, b)`, `w_k T_k(a, b + 1)`,
  `w_k T_k(a, b)`;
* `contig_truncated`: for every `N`,
  `a S_N(a + 1, b) + b S_N(a, b) = b S_N(a, b + 1) + a S_N(a, b)`, i.e.
  `a F_N(a+) − b F_N(b+) = (a − b) F_N` exactly, with no boundary term (each summand is
  `ContiguousRelations.contig_a_plus` and `contig_b_plus`), by quantifier-free induction on `N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ContiguousTruncated

open_ipra
open LeanProofs.IPRA.Analysis.Pochhammer (poch)
open LeanProofs.IPRA.Analysis.ContiguousRelations (Tn contig_a_plus contig_b_plus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (w : PTm 2)

/-- `w(k, y)` read from `⟨a, ⟨b, y⟩⟩`. -/
abbrev wB : PTm 2 := Syn.subst ![Syn.var 0, sndT (sndT (Syn.var 1))] w

/-- `w_k T_k(a + 1, b)`. -/
abbrev TAB : PTm 2 := wB w * Tn (succ (fstT (Syn.var 1))) (fstT (sndT (Syn.var 1))) (Syn.var 0)
/-- `w_k T_k(a, b + 1)`. -/
abbrev TBB : PTm 2 := wB w * Tn (fstT (Syn.var 1)) (succ (fstT (sndT (Syn.var 1)))) (Syn.var 0)
/-- `w_k T_k(a, b)`. -/
abbrev T0B : PTm 2 := wB w * Tn (fstT (Syn.var 1)) (fstT (sndT (Syn.var 1))) (Syn.var 0)

theorem inst2_wB (k p : PTm n) : inst2 (wB w) k p = inst2 w k (sndT (sndT p)) := by
  simp only [inst2, wB, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

theorem congrTn {a a' b b' k : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] Tn a b k ≐ Tn a' b' k :=
  congrMul (congrAp2 _ (.eqRefl k) ha) (congrAp2 _ (.eqRefl k) hb)

theorem wB_at (k a b y : PTm n) : Γ ⊢[PRAAx] inst2 (wB w) k (pairT a (pairT b y)) ≐ inst2 w k y := by
  rw [inst2_wB]
  exact congrInst2 w (.eqRefl k) (snd_pair _ _).sndE

theorem fa (a b y : PTm n) : Γ ⊢[PRAAx] fstT (pairT a (pairT b y)) ≐ a := fst_pair _ _
theorem fb (a b y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (pairT a (pairT b y))) ≐ b :=
  (snd_pair _ _).fstE

theorem TA_at (k a b y : PTm n) :
    Γ ⊢[PRAAx] inst2 (TAB w) k (pairT a (pairT b y)) ≐ inst2 w k y * Tn (succ a) b k := by
  have e : inst2 (TAB w) k (pairT a (pairT b y)) = inst2 (wB w) k (pairT a (pairT b y)) *
      Tn (succ (fstT (pairT a (pairT b y)))) (fstT (sndT (pairT a (pairT b y)))) k := by
    simp [inst2, TAB, Tn, poch, LeanProofs.IPRA.Analysis.Products.P]
  rw [e]
  exact congrMul (wB_at w k a b y) (congrTn (congrSucc (fa a b y)) (fb a b y))

theorem TB_at (k a b y : PTm n) :
    Γ ⊢[PRAAx] inst2 (TBB w) k (pairT a (pairT b y)) ≐ inst2 w k y * Tn a (succ b) k := by
  have e : inst2 (TBB w) k (pairT a (pairT b y)) = inst2 (wB w) k (pairT a (pairT b y)) *
      Tn (fstT (pairT a (pairT b y))) (succ (fstT (sndT (pairT a (pairT b y))))) k := by
    simp [inst2, TBB, Tn, poch, LeanProofs.IPRA.Analysis.Products.P]
  rw [e]
  exact congrMul (wB_at w k a b y) (congrTn (fa a b y) (congrSucc (fb a b y)))

theorem T0_at (k a b y : PTm n) :
    Γ ⊢[PRAAx] inst2 (T0B w) k (pairT a (pairT b y)) ≐ inst2 w k y * Tn a b k := by
  have e : inst2 (T0B w) k (pairT a (pairT b y)) = inst2 (wB w) k (pairT a (pairT b y)) *
      Tn (fstT (pairT a (pairT b y))) (fstT (sndT (pairT a (pairT b y)))) k := by
    simp [inst2, T0B, Tn, poch, LeanProofs.IPRA.Analysis.Products.P]
  rw [e]
  exact congrMul (wB_at w k a b y) (congrTn (fa a b y) (fb a b y))

/-- The truncated identity for the first `N` coefficients. -/
abbrev CInv (a b y N : PTm n) : Fm PTm n :=
  a * ap2 (sumF (TAB w)) N (pairT a (pairT b y)) + b * ap2 (sumF (T0B w)) N (pairT a (pairT b y)) ≐
    b * ap2 (sumF (TBB w)) N (pairT a (pairT b y)) + a * ap2 (sumF (T0B w)) N (pairT a (pairT b y))

theorem contig_step {a b y N : PTm n} (ih : Γ ⊢[PRAAx] CInv w a b y N) : Γ ⊢[PRAAx] CInv w a b y (succ N) := by
  have s1 := natEq (sum_succ' (Γ := Γ) (TAB w) N (pairT a (pairT b y)))
  have s2 := natEq (sum_succ' (Γ := Γ) (T0B w) N (pairT a (pairT b y)))
  have s3 := natEq (sum_succ' (Γ := Γ) (TBB w) N (pairT a (pairT b y)))
  have t1 := natEq (TA_at (Γ := Γ) w N a b y)
  have t2 := natEq (T0_at (Γ := Γ) w N a b y)
  have t3 := natEq (TB_at (Γ := Γ) w N a b y)
  have ca := natEq (contig_a_plus (Γ := Γ) a b N)
  have cb := natEq (contig_b_plus (Γ := Γ) a b N)
  have e := natEq ih
  apply deriveNat
  ipra_simps
  rw [s1, s2, s3, t1, t2, t3]
  linear_combination e + 𝔟 (inst2 w N y) * ca - 𝔟 (inst2 w N y) * cb

/-- "Finite contiguous relation": `a S_N(a + 1, b) + b S_N(a, b) = b S_N(a, b + 1) + a S_N(a, b)`. -/
theorem contig_truncated (a b y N : PTm n) : Γ ⊢[PRAAx] CInv w a b y N := by
  have hall : Γ ⊢[PRAAx] Fm.all (CInv w (Syn.shift a) (Syn.shift b) (Syn.shift y) (Syn.var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have z1 := natEq (sum_zero (Γ := Γ) (TAB w) (pairT a (pairT b y)))
      have z2 := natEq (sum_zero (Γ := Γ) (T0B w) (pairT a (pairT b y)))
      have z3 := natEq (sum_zero (Γ := Γ) (TBB w) (pairT a (pairT b y)))
      apply deriveNat
      ipra_simps
      rw [z1, z2, z3]; ring
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact contig_step w Prf.hyp0
  have h2 := Prf.allE N hall
  simpa only [Fm.subst_eq, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using h2

end LeanProofs.IPRA.Analysis.ContiguousTruncated
