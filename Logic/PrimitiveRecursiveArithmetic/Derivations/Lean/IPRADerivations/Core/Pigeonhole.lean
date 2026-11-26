import IPRADerivations.AnalyticNumberTheory.TotientCorollaries

/-!
# The pigeonhole principle, with explicit search witnesses

Reusable for `diophantine-number-theory/dirichlet_kronecker_ipra` (`lem:php`),
`diophantine-number-theory/minkowski_ipra` (`lem:php`) and
`diophantine-number-theory/pell_ipra_2026-11-15` (`thm:modular`).

For a body `σ(i, x)` with `σ(i, x) < K` for every `i`, the indices `0, …, K` collide:
`j₀ = μ j ≤ K. E(j) ≠ 0`, with `E(j) = #{i < j : σ(i) = σ(j)}`, and `i₀ = μ i < j₀. σ(i) = σ(j₀)`
satisfy `i₀ < j₀ ≤ K` and `σ(i₀) = σ(j₀)`.

If no `E(j)` were nonzero, every value count `c(v) = #{i ≤ K : σ(i) = v}` would be at most `1`
(`count_le_one`: `E(M) = c_M(σ(M))`), while the counts add up to `K + 1`
(`SumPhi.sum_fiber`), and `K` values counted at most once give at most `K`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Pigeonhole

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_fiber cB inst3_cB sum_ones)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (sum2_lift term_le_sum2)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne ne_of_eqb_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (eqb_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (lift3 inst2_lift3 at_pair)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (S : PTm 2)

/-- `c_M(v) = #{i < M : σ(i) = v}`. -/
abbrev cnt (M v x : PTm n) : PTm n := ap3 (sum2F (Permutation.mB S)) M v x

/-- `E(j) = c_j(σ(j))`, over `0 = j`, `1 = x`. -/
abbrev EB : PTm 2 := ap3 (sum2F (Permutation.mB S)) (var 0) S (var 1)

theorem inst2_E (j x : PTm n) : inst2 (EB S) j x = cnt S j (inst2 S j x) x := by
  simp only [inst2, EB, subst_ap3, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

variable {S}

theorem cnt_succ (M v x : PTm n) :
    Γ ⊢[PRAAx] cnt S (succ M) v x ≐ cnt S M v x + eqb (inst2 S M x) v := by
  have h := sum2_succ (Γ := Γ) (Permutation.mB S) M v x
  rw [Permutation.inst3_mB] at h
  exact h

/-- Without a repetition below `M`, every value is taken at most once below `M`. -/
theorem count_le_one {M v x : PTm n}
    (hE : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ (inst2 (EB S) (var 0) (Syn.shift x) ≐ zero))) :
    Γ ⊢[PRAAx] le (cnt S M v x) one := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift M) ⟶
      le (cnt S (var 0) (Syn.shift v) (Syn.shift x)) one) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap3, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact .impI (le_congr (sum2_zero _ _ _).eqSymm (.eqRefl _) (zero_monus _))
    · simp only [Fm.subst_imp, subst_le, subst_ap3, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have hlt : (le (succ (var 0)) (Syn.shift M) :: (le (var 0) (Syn.shift M) ⟶
          le (cnt S (var 0) (Syn.shift v) (Syn.shift x)) one) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift M) :=
        Prf.hyp0
      have ih := Prf.impE Prf.hyp1 (le_of_lt hlt)
      have hE0 := Prf.impE hE.allOpen.wk.wk hlt
      rw [inst2_E] at hE0
      refine le_congr (cnt_succ _ _ _).eqSymm (.eqRefl _) ?_
      refine .orE (eq_or_ne (inst2 S (var 0) (Syn.shift x)) (Syn.shift v)) ?_ ?_
      · -- `σ(M) = v`: then `c_M(v) = E(M) = 0`.
        have c0 : ((inst2 S (var 0) (Syn.shift x) ≐ Syn.shift v) :: _) ⊢[PRAAx]
            cnt S (var 0) (Syn.shift v) (Syn.shift x) ≐ zero :=
          (congrAp3 _ (.eqRefl _) Prf.hyp0.eqSymm (.eqRefl _)).eqTrans hE0.wk
        exact le_congr ((zero_add _).eqSymm.eqTrans (congrAdd c0.eqSymm (eqb_of_eq Prf.hyp0).eqSymm)) (.eqRefl _)
          (le_refl _)
      · exact le_congr ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) (eqb_of_ne Prf.hyp0).eqSymm))
          (.eqRefl _) ih.wk
  have h := Prf.allE M hall
  simp only [Fm.subst_imp, subst_le, subst_ap3, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact .impE h (le_refl M)

open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')

/-- `∀ j < M. E(j) = 0`: no value repeats below `M`. -/
def noRep (S : PTm 2) (M x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift M) ⟶ (inst2 (EB S) (var 0) (Syn.shift x) ≐ zero))

ipra_subst noRep [subst_up_shift', Syn.up]

theorem shift_noRep {M x : PTm n} (h : Γ ⊢[PRAAx] noRep S M x) :
    Γ.map Fm.shift ⊢[PRAAx] noRep S (Syn.shift M) (Syn.shift x) := by
  have e := h.shift
  simp only [Fm.shift, subst_noRep] at e
  exact e

theorem shift_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  have e := h.shift
  simp only [Fm.shift, subst_le] at e
  exact e

/-- The counts below `K + 1` add up to `K + 1`, but without a repetition they total at most `K`. -/
theorem no_rep_absurd {K x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S K x)
    (hE : Γ ⊢[PRAAx] noRep S (succ K) x) : Γ ⊢[PRAAx] Fm.bot := by
  have eFS : Permutation.FS (one : PTm 2) S = one := by simp [Permutation.FS]
  have hf := sum_fiber (f := one) hr (succ K)
  rw [eFS] at hf
  have hs := (sum_ones (Γ := Γ) (succ K) x).eqSymm.eqTrans (hf.eqTrans (sum2_lift _ _ _ _))
  have e₁ : ∀ {k : ℕ} (y z : PTm k), inst2 (one : PTm 2) y z = one := by intro k y z; simp [inst2]
  have hE' := shift_noRep hE
  have e : Syn.shift (succ K) = succ (Syn.shift K) := by simp [Syn.shift]
  rw [e] at hE'
  have hpt : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      le (inst2 (lift3 (cB one S)) (var 0) (Syn.shift (pairT (succ K) x))) (inst2 (one : PTm 2) (var 0)
        (Syn.shift (pairT (succ K) x)))) := by
    refine .allI (.impI ?_)
    rw [AnalyticNumberTheory.Euler.shift_pair, inst2_lift3, e₁, inst3_cB, e₁, e]
    have c := count_le_one (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) (v := var 0) hE'.wk
    refine le_congr ?_ (.eqRefl _) c
    refine .eqTrans ?_ (one_mul _).eqSymm
    exact congrAp3 _ (fst_pair _ _).eqSymm (.eqRefl _) (snd_pair _ _).eqSymm
  have hle := Analysis.PowerSums.sum_le (lift3 (cB one S)) one (pairT (succ K) x) K hpt
  have hb := le_congr hs.eqSymm (sum_ones _ _) hle
  exact not_succ_le_self K _ hb

/-! ## The witnesses -/

/-- `j₀`: the first `j ≤ K` whose value occurred before. -/
abbrev phpJ (S : PTm 2) (K x : PTm n) : PTm n := Search.mu (eqb (EB S) zero) (succ K) x

theorem inst2_fJ (j x : PTm n) : inst2 (eqb (EB S) zero) j x = eqb (inst2 (EB S) j x) zero := by
  simp [inst2]

/-- Below the search result, every `E(j)` vanishes. -/
theorem noRep_below {K x : PTm n} (h : Γ ⊢[PRAAx] le (succ K) (phpJ S K x)) : Γ ⊢[PRAAx] noRep S (succ K) x := by
  have hle := shift_le h
  have e₁ : Syn.shift (succ K) = succ (Syn.shift K) := by simp [Syn.shift]
  have e₂ : Syn.shift (phpJ S K x) = phpJ S (Syn.shift K) (Syn.shift x) := by simp [Syn.shift]
  rw [e₁, e₂] at hle
  unfold noRep
  rw [e₁]
  refine .allI (.impI ?_)
  have hlt0 : (lt (var 0) (succ (Syn.shift K)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (phpJ S (Syn.shift K) (Syn.shift x)) := le_trans Prf.hyp0 hle.wk
  have hne := Search.search_minimal (f := eqb (EB S) zero) hlt0
  rw [inst2_fJ] at hne
  exact eq_of_eqb_ne hne

theorem phpJ_spec {K x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S K x) :
    Γ ⊢[PRAAx] lt (phpJ S K x) (succ K) ⋏ neg (inst2 (EB S) (phpJ S K x) x ≐ zero) := by
  have sp := Search.search_spec (Γ := Γ) (f := eqb (EB S) zero) (succ K) zero x
  refine .orE (lt_or_le (phpJ S K x) (succ K)) ?_ ?_
  · have f0 := Prf.impE (Prf.andE₁ (Prf.andE₂ sp)).wk Prf.hyp0
    rw [inst2_fJ] at f0
    exact .andI Prf.hyp0 (ne_of_eqb_zero f0)
  · exact .botE _ (no_rep_absurd hr.wk (noRep_below Prf.hyp0))

/-- `[σ(i) ≠ σ(j)]`, over `0 = i`, `1 = j`, `2 = x`. -/
abbrev g3 (S : PTm 2) : PTm 3 :=
  monus one (eqb (Syn.subst ![var 0, var 2] S) (Syn.subst ![var 1, var 2] S))

theorem inst3_g3 (i j x : PTm n) : inst3 (g3 S) i j x = monus one (eqb (inst2 S i x) (inst2 S j x)) := by
  simp only [inst3, inst2, g3, subst_eqb, Syn.subst_subst, PTm.subst_monus, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]
  congr 3 <;> (funext k; fin_cases k <;> rfl)

/-- The first `i < J` with `σ(i) = σ(J)`. -/
abbrev firstMatch (S : PTm 2) (J x : PTm n) : PTm n := Search.mu (lift3 (g3 S)) J (pairT J x)

theorem cnt_zero_of_none {J x : PTm n} (h : Γ ⊢[PRAAx] le J (firstMatch S J x)) :
    Γ ⊢[PRAAx] cnt S J (inst2 S J x) x ≐ zero := by
  refine AnalyticNumberTheory.SumPhi.sum2_zero_of_bounded _ (.allI (.impI ?_))
  have hle := shift_le h
  have e₂ : Syn.shift (firstMatch S J x) = firstMatch S (Syn.shift J) (Syn.shift x) := by simp [Syn.shift]
  have e₃ : Syn.shift (inst2 S J x) = inst2 S (Syn.shift J) (Syn.shift x) := by simp only [Syn.shift, subst_inst2]
  rw [e₂] at hle
  rw [Permutation.inst3_mB, e₃]
  have hlt0 : (lt (var 0) (Syn.shift J) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (firstMatch S (Syn.shift J) (Syn.shift x)) := lt_of_lt_of_le Prf.hyp0 hle.wk
  have hne := Search.search_minimal (f := lift3 (g3 S)) hlt0
  have e := at_pair (g3 S) (var 0) (Syn.shift J) (Syn.shift x)
    (Γ := lt (var 0) (Syn.shift J) :: Γ.map Fm.shift)
  rw [inst3_g3] at e
  refine .orE (eq_or_ne (inst2 S (var 0) (Syn.shift x)) (inst2 S (Syn.shift J) (Syn.shift x))) ?_ (eqb_of_ne Prf.hyp0)
  refine .botE _ (.impE hne.wk (e.wk.eqTrans ?_))
  exact (congrMonus (.eqRefl _) (eqb_of_eq Prf.hyp0)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))

theorem firstMatch_spec {J x : PTm n} (hne : Γ ⊢[PRAAx] neg (cnt S J (inst2 S J x) x ≐ zero)) :
    Γ ⊢[PRAAx] lt (firstMatch S J x) J ⋏ (inst2 S (firstMatch S J x) x ≐ inst2 S J x) := by
  have hlt : Γ ⊢[PRAAx] lt (firstMatch S J x) J := by
    refine .orE (lt_or_le (firstMatch S J x) J) Prf.hyp0 ?_
    exact .botE _ (.impE hne.wk (cnt_zero_of_none Prf.hyp0))
  have sp := Search.search_spec (Γ := Γ) (f := lift3 (g3 S)) J zero (pairT J x)
  have f0 := Prf.impE (Prf.andE₁ (Prf.andE₂ sp)) hlt
  have e := (at_pair (g3 S) (firstMatch S J x) J x (Γ := Γ)).eqSymm.eqTrans f0
  rw [inst3_g3] at e
  exact .andI hlt (eq_of_viol e)

/-- `i₀`. -/
abbrev phpI (S : PTm 2) (K x : PTm n) : PTm n := firstMatch S (phpJ S K x) x

/-- The pigeonhole principle: `i₀ < j₀ ≤ K` and `σ(i₀) = σ(j₀)`. -/
theorem pigeonhole {K x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S K x) :
    Γ ⊢[PRAAx] lt (phpI S K x) (phpJ S K x) ⋏
      (le (phpJ S K x) K ⋏ (inst2 S (phpI S K x) x ≐ inst2 S (phpJ S K x) x)) := by
  have hj := phpJ_spec hr
  have hJK : Γ ⊢[PRAAx] le (phpJ S K x) K := (succ_monus_succ _ _).eqSymm.eqTrans (Prf.andE₁ hj)
  have hE := Prf.andE₂ hj
  rw [inst2_E] at hE
  have fm := firstMatch_spec hE
  exact .andI (Prf.andE₁ fm) (.andI hJK (Prf.andE₂ fm))

end LeanProofs.IPRA.Pigeonhole
