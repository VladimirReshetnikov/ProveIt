import IPRADerivations.Probability.Lotus
import IPRADerivations.Probability.ExpectationCorollaries
import IPRADerivations.Foundations.BoundedReflection

/-!
# The histogram normal form

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:histogram`. For an
observable `X(i, x)` on outcomes `i < M`, the representative of `i` is the first earlier index with
the same value, found by bounded search (`Core/Search`):
  `rep(i) = μ k ≤ i. [X_k = X_i]`  (search body `ad(X_k, X_i)`).
One slot per outcome is kept (slots `j` that are not first occurrences get zero weight), so no
sorting and no variable-length quotient is needed:

* `rep_spec`, `rep_min`: `rep(i) ≤ i`, `X_{rep(i)} = X_i`, and `X_k ≠ X_i` for `k < rep(i)`;
* `lotus_bounded`: the finite LOTUS with the range hypothesis only on the outcomes `i < M`;
* `histogram`: `∑_{i<M} w_i X_i = ∑_{j<M} X_j v_j` with `v_j = ∑_{i<M} w_i [rep(i) = j]`;
* `hist_support`: a slot with `rep(i) = j` is a first occurrence, `rep(j) = j`;
* `hist_distinct`: first occurrences `j < k` carry distinct values `X_j ≠ X_k`;
* `rep_fiber`, `hist_weight`: at a first occurrence `j`, `[rep(i) = j] = [X_i = X_j]`, so
  `v_j = ∑_{i<M} w_i [X_i = X_j]` is the total weight of the value `X_j`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Histogram

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew inst2_mul')
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.ExpectationCorollaries (ad_zero)
open LeanProofs.IPRA.Probability.Lotus (aB rB vB gσ inst2_gσ inst2_rB inst2_vB row_eval col_eval)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The finite LOTUS on bounded outcomes -/

/-- `thm:finite-lotus` with `σ(i) < N` assumed only for `i < M`. -/
theorem lotus_bounded (w σ g : PTm 2) {N x M : PTm n}
    (hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ lt (inst2 σ (var 0) (Syn.shift x)) (Syn.shift N))) :
    Γ ⊢[PRAAx] ap2 (sumF (w * gσ σ g)) M x ≐ ap2 (sumF (rB w σ g)) N (pairT M x) := by
  have e₁ : Γ ⊢[PRAAx] ap2 (sumF (w * gσ σ g)) M x ≐ ap2 (sumF (oB (aB w σ g))) M (pairT N x) := by
    refine sum_congr_bounded (w * gσ σ g) (oB (aB w σ g)) x (pairT N x) M (.allI (.impI ?_))
    rw [Expectation.inst2_mul', inst2_gσ, shift_pairT]
    exact ((oB_at _ _ _ _).eqTrans (row_eval w σ g (Prf.impE hr.allOpen.wk Prf.hyp0))).eqSymm
  have e₂ : Γ ⊢[PRAAx] ap2 (sumF (pB (aB w σ g))) N (pairT M x) ≐ ap2 (sumF (rB w σ g)) N (pairT M x) := by
    refine sum_congr_bounded (pB (aB w σ g)) (rB w σ g) (pairT M x) (pairT M x) N (.allI (.impI ?_))
    rw [inst2_pB, inst2_rB, shift_pairT]
    exact (congrAp2 (sumF (colB (aB w σ g))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      ((col_eval w σ g _ _ _).eqTrans (congrMul (congrInst2 g (.eqRefl _) (snd_pair _ _)).eqSymm
        (congrAp2 (sumF (vB w σ)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm))
  exact e₁.eqTrans ((fubini (aB w σ g) M N x).eqTrans e₂)

/-! ## The first-occurrence representative -/

theorem congrAd {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ad a b ≐ ad a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

theorem ad_self (a : PTm n) : Γ ⊢[PRAAx] ad a a ≐ zero :=
  (congrAdd (monus_self a) (monus_self a)).eqTrans (zero_add _)

section Rep

variable (X : PTm 2)

/-- The search body `ad(X(k, x), X(i, x))`, over `0 = k`, `1 = ⟨i, x⟩`. -/
abbrev fH : PTm 2 := ad (Syn.subst ![var 0, sndT (var 1)] X) (Syn.subst ![fstT (var 1), sndT (var 1)] X)

theorem fH_at (k i x : PTm n) : Γ ⊢[PRAAx] inst2 (fH X) k (pairT i x) ≐ ad (inst2 X k x) (inst2 X i x) := by
  have e : inst2 (fH X) k (pairT i x) =
      ad (inst2 X k (sndT (pairT i x))) (inst2 X (fstT (pairT i x)) (sndT (pairT i x))) := by
    simp only [inst2, fH, ad, PTm.subst_add, PTm.subst_monus, Syn.subst_subst]
    congr 2 <;> (try congr 1) <;> funext j <;> fin_cases j <;> simp
  rw [e]
  exact congrAd (congrInst2 X (.eqRefl _) (snd_pair _ _)) (congrInst2 X (fst_pair _ _) (snd_pair _ _))

/-- `rep(i, x) = μ k < i + 1. [X_k = X_i]`. -/
abbrev rep (i x : PTm n) : PTm n := Search.mu (fH X) (succ i) (pairT i x)

/-- The representative as a body. -/
abbrev repB : PTm 2 := ap2 (Search.muF (fH X)) (succ (var 0)) (pairT (var 0) (var 1))

theorem inst2_repB (i x : PTm n) : inst2 (repB X) i x = rep X i x := by
  simp [inst2, repB, rep, Search.mu]

theorem rep_spec (i x : PTm n) : Γ ⊢[PRAAx] le (rep X i x) i ⋏ (inst2 X (rep X i x) x ≐ inst2 X i x) := by
  have f0 : Γ ⊢[PRAAx] inst2 (fH X) i (pairT i x) ≐ zero := (fH_at X i i x).eqTrans (ad_self _)
  have s := Search.search_found (f := fH X) (N := succ i) f0 (le_refl (succ i))
  exact .andI (Prf.andE₂ (Prf.andE₂ s)) (ad_zero ((fH_at X _ i x).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ s))))

theorem rep_min {i k x : PTm n} (hk : Γ ⊢[PRAAx] lt k (rep X i x)) :
    Γ ⊢[PRAAx] neg (inst2 X k x ≐ inst2 X i x) := by
  refine .impI (.impE (Search.search_minimal (f := fH X) hk).wk ?_)
  exact (fH_at X k i x).eqTrans ((congrAd Prf.hyp0 (.eqRefl _)).eqTrans (ad_self _))

/-- A slot that receives an outcome is a first occurrence: `rep(i) = j → rep(j) = j`. -/
theorem hist_support {i j x : PTm n} (h : Γ ⊢[PRAAx] rep X i x ≐ j) : Γ ⊢[PRAAx] rep X j x ≐ j := by
  refine le_antisymm (Prf.andE₁ (rep_spec X j x)) (.orE (lt_or_le (rep X j x) j) ?_ Prf.hyp0)
  let C := lt (rep X j x) j :: Γ
  have hl : C ⊢[PRAAx] lt (rep X j x) (rep X i x) := lt_congr (.eqRefl _) h.wk.eqSymm Prf.hyp0
  have xe : C ⊢[PRAAx] inst2 X (rep X j x) x ≐ inst2 X i x :=
    (Prf.andE₂ (rep_spec X j x)).eqTrans ((congrInst2 X h.wk.eqSymm (.eqRefl _)).eqTrans (Prf.andE₂ (rep_spec X i x)))
  exact .botE _ (.impE (rep_min X hl) xe)

/-- First occurrences carry distinct values. -/
theorem hist_distinct {j k x : PTm n} (hk : Γ ⊢[PRAAx] rep X k x ≐ k) (hjk : Γ ⊢[PRAAx] lt j k) :
    Γ ⊢[PRAAx] neg (inst2 X j x ≐ inst2 X k x) :=
  rep_min X (lt_congr (.eqRefl _) hk.eqSymm hjk)

/-- At a first occurrence `j`: `[rep(i) = j] = [X_i = X_j]`. -/
theorem rep_fiber {j x : PTm n} (hj : Γ ⊢[PRAAx] rep X j x ≐ j) (i : PTm n) :
    Γ ⊢[PRAAx] eqb (rep X i x) j ≐ eqb (inst2 X i x) (inst2 X j x) := by
  refine .orE (eqb_cases (inst2 X i x) (inst2 X j x)) ?_ ?_
  · let C := (eqb (inst2 X i x) (inst2 X j x) ≐ zero) :: Γ
    refine .orE (eqb_cases (rep X i x) j) (Prf.hyp0.eqTrans Prf.hyp1.eqSymm) ?_
    let D := (eqb (rep X i x) j ≐ one) :: C
    have e : D ⊢[PRAAx] rep X i x ≐ j := eq_of_eqb Prf.hyp0
    have xe : D ⊢[PRAAx] inst2 X i x ≐ inst2 X j x :=
      (Prf.andE₂ (rep_spec X i x)).eqSymm.eqTrans (congrInst2 X e (.eqRefl _))
    exact .botE _ (succ_ne_zero ((eqb_of_eq xe).eqSymm.eqTrans Prf.hyp1))
  · let C := (eqb (inst2 X i x) (inst2 X j x) ≐ one) :: Γ
    have xe : C ⊢[PRAAx] inst2 X i x ≐ inst2 X j x := eq_of_eqb Prf.hyp0
    have hji : C ⊢[PRAAx] le j i := by
      refine .orE (lt_or_le i j) ?_ Prf.hyp0
      exact .botE _ (.impE (rep_min X (lt_congr (.eqRefl _) hj.wk.wk.eqSymm Prf.hyp0)) xe.wk)
    have f0 : C ⊢[PRAAx] inst2 (fH X) j (pairT i x) ≐ zero :=
      (fH_at X j i x).eqTrans ((congrAd xe.eqSymm (.eqRefl _)).eqTrans (ad_self _))
    have hs : C ⊢[PRAAx] lt j (succ i) := (succ_monus_succ _ _).eqTrans hji
    have up : C ⊢[PRAAx] le (rep X i x) j := Prf.andE₂ (Prf.andE₂ (Search.search_found (f := fH X) f0 hs))
    have dn : C ⊢[PRAAx] le j (rep X i x) := by
      refine .orE (lt_or_le (rep X i x) j) ?_ Prf.hyp0
      have hl : (lt (rep X i x) j :: C) ⊢[PRAAx] lt (rep X i x) (rep X j x) :=
        lt_congr (.eqRefl _) hj.wk.wk.eqSymm Prf.hyp0
      exact .botE _ (.impE (rep_min X hl) ((Prf.andE₂ (rep_spec X i x)).eqTrans xe.wk))
    exact (eqb_of_eq (le_antisymm up dn)).eqTrans Prf.hyp0.eqSymm

end Rep

/-! ## The histogram -/

section Hist

variable (w X : PTm 2)

/-- `prop:histogram`: `∑_{i<M} w_i X_i = ∑_{j<M} X_j v_j`, `v_j = ∑_{i<M} w_i [rep(i) = j]`. -/
theorem histogram (M x : PTm n) :
    Γ ⊢[PRAAx] Ew w X M x ≐ ap2 (sumF (rB w (repB X) X)) M (pairT M x) := by
  have hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      lt (inst2 (repB X) (var 0) (Syn.shift x)) (Syn.shift M)) := by
    refine .allI (.impI ?_)
    rw [inst2_repB]
    exact lt_of_le_of_lt (Prf.andE₁ (rep_spec X _ _)) Prf.hyp0
  refine .eqTrans ?_ (lotus_bounded w (repB X) X hr)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_mul', inst2_mul', inst2_gσ, inst2_repB]
  exact congrMul (.eqRefl _) (Prf.andE₂ (rep_spec X _ _)).eqSymm

/-- At a first occurrence `j`, the slot weight is the total weight of the value `X_j`:
`∑_{i<M} w_i [rep(i) = j] = ∑_{i<M} w_i [X_i = X_j]`. -/
theorem hist_weight {j x : PTm n} (hj : Γ ⊢[PRAAx] rep X j x ≐ j) (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (vB w (repB X))) M (pairT j x) ≐ ap2 (sumF (vB w X)) M (pairT (inst2 X j x) x) := by
  have hj' : Γ.map Fm.shift ⊢[PRAAx] rep X (Syn.shift j) (Syn.shift x) ≐ Syn.shift j := by
    simpa [Fm.shift, Syn.shift] using hj.shift
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, Independence.shift_inst2, inst2_vB, inst2_vB, inst2_repB]
  refine (congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _))
    (congrEqb (congrAp2 _ (congrSucc (.eqRefl _)) (congrPairT (.eqRefl _) (snd_pair _ _))) (fst_pair _ _))).eqTrans ?_
  refine .eqTrans ?_ (congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _))
    (congrEqb (congrInst2 X (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))).eqSymm
  exact congrMul (.eqRefl _) (rep_fiber X hj'.wk (var 0))

end Hist

end LeanProofs.IPRA.Probability.Histogram
