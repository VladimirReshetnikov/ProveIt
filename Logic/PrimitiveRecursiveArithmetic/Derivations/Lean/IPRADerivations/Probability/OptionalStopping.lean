import IPRADerivations.Probability.Expectation
import IPRADerivations.Probability.FirstCrossing
import IPRADerivations.Core.Fubini

/-!
# The bounded optional stopping theorem

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/conditioning.tex`, "A finite stopping theorem":
"Let `M_j` be an integrable martingale for the first-`j`-bit filtration … Let `τ ≤ N` be a stopping rule whose
decision `{τ > j}` is a certified event depending only on the first `j` observations. … On a common finite table,
`M_τ = M_0 + Σ_{j<N} 1_{τ>j} (M_{j+1} − M_j)`. Each summand has expectation zero by the conditional identity and
past measurability. Hence `E M_τ = E M_0`."

On a finite weighted law (outcomes `t < T`, weights `w(t, x)`), a natural-valued process `M(j, t, x)` and a
stopping time `τ(t, x) ≤ N`, with `[τ > j] = ge (j + 1) τ`:

* `tele` (the finite table identity, signs moved across):
  `Σ_{j<N} [τ>j] w M_{j+1} + w M_0 = Σ_{j<N} [τ>j] w M_j + w M_τ`, by induction on `N` with the invariant at
  `min(N, τ) = N ∸ (N ∸ τ)`;
* `optional_stopping`: if for every `j < N` the martingale identity on the stopping event holds,
  `E[[τ>j] M_{j+1}] = E[[τ>j] M_j]` (what the conditional identity gives for the `F_j`-measurable `[τ > j]`), then
  `E[M_τ] = E[M_0]`, i.e. `Σ_t w_t M(τ_t, t) = Σ_t w_t M(0, t)`. The two double sums are exchanged by the finite
  Fubini theorem `fubini`.

Measurability enters only through the hypothesis; `ConditionalAveraging.cond_defining` is one way to supply it.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.OptionalStopping

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open LeanProofs.IPRA.Probability.FirstCrossing (ge ge_of_le ge_of_lt)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Substitution helpers -/

theorem inst2_fs (f : PTm 2) (j y : PTm n) :
    inst2 (Syn.subst ![fstT (var 1), sndT (var 1)] f) j y = inst2 f (fstT y) (sndT y) := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem inst2_fs3 (M : PTm 3) (e : PTm 2) (j y : PTm n) :
    inst2 (Syn.subst ![e, fstT (var 1), sndT (var 1)] M) j y = inst3 M (inst2 e j y) (fstT y) (sndT y) := by
  simp only [inst2, inst3, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp [inst2]

theorem inst2_s3 (M : PTm 3) (e : PTm 2) (t x : PTm n) :
    inst2 (Syn.subst ![e, var 0, var 1] M) t x = inst3 M (inst2 e t x) t x := by
  simp only [inst2, inst3, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp [inst2]

/-- `f(i, snd y)`. -/
def lw (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_lw (f : PTm 2) (i y : PTm n) : inst2 (lw f) i y = inst2 f i (sndT y) := by
  simp only [lw, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

/-- The three-variable body `f(j, ⟨t, x⟩)` at `(t, j, x)`. -/
def lift (f : PTm 2) : PTm 3 := Syn.subst ![var 1, pairT (var 0) (var 2)] f

theorem inst3_lift (f : PTm 2) (t j x : PTm n) : inst3 (lift f) t j x = inst2 f j (pairT t x) := by
  simp only [inst3, inst2, lift, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

section Stopping

variable (w τ : PTm 2) (M : PTm 3)

/-! ## The bodies -/

/-- `w_t [τ_t > j] M_{j+1}(t)` over `(j, ⟨t, x⟩)`. -/
def aR : PTm 2 :=
  Syn.subst ![fstT (var 1), sndT (var 1)] w * ge (succ (var 0)) (Syn.subst ![fstT (var 1), sndT (var 1)] τ) *
    Syn.subst ![succ (var 0), fstT (var 1), sndT (var 1)] M

/-- `w_t [τ_t > j] M_j(t)` over `(j, ⟨t, x⟩)`. -/
def bR : PTm 2 :=
  Syn.subst ![fstT (var 1), sndT (var 1)] w * ge (succ (var 0)) (Syn.subst ![fstT (var 1), sndT (var 1)] τ) *
    Syn.subst ![var 0, fstT (var 1), sndT (var 1)] M

theorem ge_fs (j y : PTm n) :
    inst2 (ge (succ (var 0)) (Syn.subst ![fstT (var 1), sndT (var 1)] τ)) j y =
      ge (succ j) (inst2 τ (fstT y) (sndT y)) := by
  rw [← inst2_fs τ j y]; simp [inst2]

theorem aR_at (j t x : PTm n) :
    Γ ⊢[PRAAx] inst2 (aR w τ M) j (pairT t x) ≐ inst2 w t x * ge (succ j) (inst2 τ t x) * inst3 M (succ j) t x := by
  have e1 : inst2 (succ (var 0) : PTm 2) j (pairT t x) = succ j := by simp [inst2]
  have h : inst2 (aR w τ M) j (pairT t x) =
      inst2 w (fstT (pairT t x)) (sndT (pairT t x)) * ge (succ j) (inst2 τ (fstT (pairT t x)) (sndT (pairT t x))) *
        inst3 M (succ j) (fstT (pairT t x)) (sndT (pairT t x)) := by
    rw [aR, inst2_mul', inst2_mul', inst2_fs, ge_fs, inst2_fs3, e1]
  rw [h]
  have f := fst_pair (Γ := Γ) t x
  have s := snd_pair (Γ := Γ) t x
  exact congrMul (congrMul (congrInst2 w f s)
    (congrMonus (.eqRefl one) (congrMonus (.eqRefl _) (congrInst2 τ f s)))) (congrInst3 M (.eqRefl _) f s)

theorem bR_at (j t x : PTm n) :
    Γ ⊢[PRAAx] inst2 (bR w τ M) j (pairT t x) ≐ inst2 w t x * ge (succ j) (inst2 τ t x) * inst3 M j t x := by
  have e1 : inst2 (var 0 : PTm 2) j (pairT t x) = j := by simp [inst2]
  have h : inst2 (bR w τ M) j (pairT t x) =
      inst2 w (fstT (pairT t x)) (sndT (pairT t x)) * ge (succ j) (inst2 τ (fstT (pairT t x)) (sndT (pairT t x))) *
        inst3 M j (fstT (pairT t x)) (sndT (pairT t x)) := by
    rw [bR, inst2_mul', inst2_mul', inst2_fs, ge_fs, inst2_fs3, e1]
  rw [h]
  have f := fst_pair (Γ := Γ) t x
  have s := snd_pair (Γ := Γ) t x
  exact congrMul (congrMul (congrInst2 w f s)
    (congrMonus (.eqRefl one) (congrMonus (.eqRefl _) (congrInst2 τ f s)))) (congrInst3 M (.eqRefl _) f s)

/-! ## The finite table identity -/

/-- `min(N, τ) = N ∸ (N ∸ τ)`. -/
abbrev mN (N t : PTm n) : PTm n := monus N (monus N t)

/-- The telescoping invariant at one outcome `t`. -/
abbrev SInv (t N x : PTm n) : Fm PTm n :=
  ap2 (sumF (aR w τ M)) N (pairT t x) + inst2 w t x * inst3 M zero t x ≐
    ap2 (sumF (bR w τ M)) N (pairT t x) + inst2 w t x * inst3 M (mN N (inst2 τ t x)) t x

theorem tele_base (t x : PTm n) : Γ ⊢[PRAAx] SInv w τ M t zero x := by
  have za := natEq (sum_zero (Γ := Γ) (aR w τ M) (pairT t x))
  have zb := natEq (sum_zero (Γ := Γ) (bR w τ M) (pairT t x))
  have em := natEq (congrInst3 (Γ := Γ) M (zero_monus (monus zero (inst2 τ t x))) (.eqRefl t) (.eqRefl x))
  apply deriveNat; ipra_simps
  linear_combination za - zb - 𝔟 (inst2 w t x) * em

theorem tele_step {t N x : PTm n} (ih : Γ ⊢[PRAAx] SInv w τ M t N x) : Γ ⊢[PRAAx] SInv w τ M t (succ N) x := by
  have sa := natEq (sum_succ' (Γ := Γ) (aR w τ M) N (pairT t x))
  have sb := natEq (sum_succ' (Γ := Γ) (bR w τ M) N (pairT t x))
  have ea := natEq (aR_at (Γ := Γ) w τ M N t x)
  have eb := natEq (bR_at (Γ := Γ) w τ M N t x)
  have i := natEq ih
  refine .orE (lt_or_le N (inst2 τ t x)) ?_ ?_
  · let C : List (Fm PTm n) := lt N (inst2 τ t x) :: Γ
    have h : C ⊢[PRAAx] lt N (inst2 τ t x) := Prf.hyp0
    have eg := natEq (ge_of_le h)
    have m1 : C ⊢[PRAAx] mN N (inst2 τ t x) ≐ N := (congrMonus (.eqRefl N) (le_of_lt h)).eqTrans (monus_zero N)
    have m2 : C ⊢[PRAAx] mN (succ N) (inst2 τ t x) ≐ succ N := (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)
    have em := natEq (congrInst3 M m1 (.eqRefl t) (.eqRefl x))
    have em2 := natEq (congrInst3 M m2 (.eqRefl t) (.eqRefl x))
    have sa' := natEq (sum_succ' (Γ := C) (aR w τ M) N (pairT t x))
    have sb' := natEq (sum_succ' (Γ := C) (bR w τ M) N (pairT t x))
    have ea' := natEq (aR_at (Γ := C) w τ M N t x)
    have eb' := natEq (bR_at (Γ := C) w τ M N t x)
    have i' := natEq (ih.wk : C ⊢[PRAAx] SInv w τ M t N x)
    apply deriveNat; ipra_simps
    linear_combination sa' - sb' + i' + ea' - eb' + 𝔟 (inst2 w t x) * em - 𝔟 (inst2 w t x) * em2 +
      (𝔟 (inst2 w t x) * 𝔟 (inst3 M (succ N) t x) - 𝔟 (inst2 w t x) * 𝔟 (inst3 M N t x)) * eg
  · let C : List (Fm PTm n) := le (inst2 τ t x) N :: Γ
    have h : C ⊢[PRAAx] le (inst2 τ t x) N := Prf.hyp0
    have hl : C ⊢[PRAAx] lt (inst2 τ t x) (succ N) := (succ_monus_succ _ _).eqTrans h
    have eg := natEq (ge_of_lt hl)
    have h2 : C ⊢[PRAAx] le (inst2 τ t x) (succ N) := le_trans h (le_succ_self N)
    have m1 : C ⊢[PRAAx] mN N (inst2 τ t x) ≐ inst2 τ t x :=
      (congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans (add_monus _ _)
    have m2 : C ⊢[PRAAx] mN (succ N) (inst2 τ t x) ≐ inst2 τ t x :=
      (congrMonus (eq_add_of_le h2) (.eqRefl _)).eqTrans (add_monus _ _)
    have em := natEq (congrInst3 M m1 (.eqRefl t) (.eqRefl x))
    have em2 := natEq (congrInst3 M m2 (.eqRefl t) (.eqRefl x))
    have sa' := natEq (sum_succ' (Γ := C) (aR w τ M) N (pairT t x))
    have sb' := natEq (sum_succ' (Γ := C) (bR w τ M) N (pairT t x))
    have ea' := natEq (aR_at (Γ := C) w τ M N t x)
    have eb' := natEq (bR_at (Γ := C) w τ M N t x)
    have i' := natEq (ih.wk : C ⊢[PRAAx] SInv w τ M t N x)
    apply deriveNat; ipra_simps
    linear_combination sa' - sb' + i' + ea' - eb' + 𝔟 (inst2 w t x) * em - 𝔟 (inst2 w t x) * em2 +
      (𝔟 (inst2 w t x) * 𝔟 (inst3 M (succ N) t x) - 𝔟 (inst2 w t x) * 𝔟 (inst3 M N t x)) * eg

theorem tele_all (t x : PTm n) : Γ ⊢[PRAAx] Fm.all (SInv w τ M (Syn.shift t) (var 0) (Syn.shift x)) := by
  refine PRA.qfInd _ trivial ?_ ?_
  · have e : (SInv w τ M (Syn.shift t) (var 0) (Syn.shift x)).subst (Syn.inst zero) = SInv w τ M t zero x := by
      simp
    rw [e]
    exact tele_base w τ M t x
  · have e : (SInv w τ M (Syn.shift t) (var 0) (Syn.shift x)).subst (Syn.repl (succ (var 0))) =
        SInv w τ M (Syn.shift t) (succ (var 0)) (Syn.shift x) := by
      simp
    rw [e]
    exact tele_step w τ M Prf.hyp0

/-- The finite table identity `Σ_{j<N} [τ>j] w M_{j+1} + w M_0 = Σ_{j<N} [τ>j] w M_j + w M_τ` for `τ ≤ N`. -/
theorem tele {t N x : PTm n} (hτ : Γ ⊢[PRAAx] le (inst2 τ t x) N) :
    Γ ⊢[PRAAx] ap2 (sumF (aR w τ M)) N (pairT t x) + inst2 w t x * inst3 M zero t x ≐
      ap2 (sumF (bR w τ M)) N (pairT t x) + inst2 w t x * inst3 M (inst2 τ t x) t x := by
  have a := Prf.allE N (tele_all (Γ := Γ) w τ M t x)
  have e : (SInv w τ M (Syn.shift t) (var 0) (Syn.shift x)).subst (Syn.inst N) = SInv w τ M t N x := by simp
  rw [e] at a
  have m : Γ ⊢[PRAAx] mN N (inst2 τ t x) ≐ inst2 τ t x :=
    (congrMonus (eq_add_of_le hτ) (.eqRefl _)).eqTrans (add_monus _ _)
  exact a.eqTrans (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (congrInst3 M m (.eqRefl t) (.eqRefl x))))

/-! ## Expectations -/

/-- `w_t M_0(t)` over `(t, x)`. -/
def wM0 : PTm 2 := w * Syn.subst ![zero, var 0, var 1] M
/-- `w_t M_{τ_t}(t)` over `(t, x)`. -/
def wMt : PTm 2 := w * Syn.subst ![τ, var 0, var 1] M

theorem row_eq (f : PTm 2) (t N x : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB (lift f)) t (pairT N x) ≐ ap2 (sumF f) N (pairT t x) := by
  rw [inst2_oB]
  refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [inst2_rowB, inst3_lift]
  exact congrInst2 f (.eqRefl _) (congrPairT (fst_pair _ _) (snd_pair _ _))

theorem col_eq (f : PTm 2) (j T x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (lift f)) j (pairT T x) ≐ ap2 (sumF (colB (lift f))) T (pairT j x) := by
  rw [inst2_pB]
  exact congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

/-- The summand of the martingale hypothesis: `colB (lift aR)` at `(t, ⟨j, x⟩)` is `w_t [τ_t > j] M_{j+1}(t)`. -/
theorem colA_at (t j x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (lift (aR w τ M))) t (pairT j x) ≐
      inst2 w t x * ge (succ j) (inst2 τ t x) * inst3 M (succ j) t x := by
  rw [inst2_colB, inst3_lift]
  exact (congrInst2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans (aR_at w τ M j t x)

theorem colB_at (t j x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (lift (bR w τ M))) t (pairT j x) ≐
      inst2 w t x * ge (succ j) (inst2 τ t x) * inst3 M j t x := by
  rw [inst2_colB, inst3_lift]
  exact (congrInst2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans (bR_at w τ M j t x)

theorem lw_sum (f : PTm 2) (T N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (lw f)) T (pairT N x) ≐ ap2 (sumF f) T x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [inst2_lw]
  exact congrInst2 f (.eqRefl _) (snd_pair _ _)

theorem stop_pt {t N x : PTm n} (hτ : Γ ⊢[PRAAx] le (inst2 τ t x) N) :
    Γ ⊢[PRAAx] inst2 (addBody (oB (lift (aR w τ M))) (lw (wM0 w M))) t (pairT N x) ≐
      inst2 (addBody (oB (lift (bR w τ M))) (lw (wMt w τ M))) t (pairT N x) := by
  rw [inst2_addBody, inst2_addBody, inst2_lw, inst2_lw]
  have s := snd_pair (Γ := Γ) N x
  have h0 : Γ ⊢[PRAAx] inst2 (wM0 w M) t (sndT (pairT N x)) ≐ inst2 w t x * inst3 M zero t x := by
    have e : inst2 (wM0 w M) t x = inst2 w t x * inst3 M zero t x := by
      rw [wM0, inst2_mul', inst2_s3]; simp [inst2]
    rw [← e]; exact congrInst2 _ (.eqRefl _) s
  have ht : Γ ⊢[PRAAx] inst2 (wMt w τ M) t (sndT (pairT N x)) ≐ inst2 w t x * inst3 M (inst2 τ t x) t x := by
    have e : inst2 (wMt w τ M) t x = inst2 w t x * inst3 M (inst2 τ t x) t x := by
      rw [wMt, inst2_mul', inst2_s3]
    rw [← e]; exact congrInst2 _ (.eqRefl _) s
  exact (congrAdd (row_eq _ t N x) h0).eqTrans ((tele w τ M hτ).eqTrans (congrAdd (row_eq _ t N x) ht).eqSymm)

/-- The bounded optional stopping theorem: if `τ ≤ N` on every outcome and the martingale identity
`E[[τ>j] M_{j+1}] = E[[τ>j] M_j]` holds for every `j < N`, then `E[M_τ] = E[M_0]`. -/
theorem optional_stopping {T N x : PTm n}
    (hτ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift T) ⟶ le (inst2 τ (var 0) (Syn.shift x)) (Syn.shift N)))
    (hm : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (ap2 (sumF (colB (lift (aR w τ M)))) (Syn.shift T) (pairT (var 0) (Syn.shift x)) ≐
        ap2 (sumF (colB (lift (bR w τ M)))) (Syn.shift T) (pairT (var 0) (Syn.shift x))))) :
    Γ ⊢[PRAAx] ap2 (sumF (wMt w τ M)) T x ≐ ap2 (sumF (wM0 w M)) T x := by
  -- the table identity summed over the outcomes
  have hS : Γ ⊢[PRAAx] ap2 (sumF (addBody (oB (lift (aR w τ M))) (lw (wM0 w M)))) T (pairT N x) ≐
      ap2 (sumF (addBody (oB (lift (bR w τ M))) (lw (wMt w τ M)))) T (pairT N x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact stop_pt w τ M (Prf.impE hτ.allOpen.wk Prf.hyp0)
  have hA := (sum_add (Γ := Γ) (oB (lift (aR w τ M))) (lw (wM0 w M)) T (pairT N x)).eqSymm.eqTrans
    (hS.eqTrans (sum_add (oB (lift (bR w τ M))) (lw (wMt w τ M)) T (pairT N x)))
  -- the double sums agree, by Fubini and the martingale identity
  have hF : Γ ⊢[PRAAx] ap2 (sumF (oB (lift (aR w τ M)))) T (pairT N x) ≐
      ap2 (sumF (oB (lift (bR w τ M)))) T (pairT N x) := by
    refine (fubini (lift (aR w τ M)) T N x).eqTrans ((sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqTrans
      (fubini (lift (bR w τ M)) T N x).eqSymm)
    simp only [shift_pairT]
    exact (col_eq _ _ _ _).eqTrans ((Prf.impE hm.allOpen.wk Prf.hyp0).eqTrans (col_eq _ _ _ _).eqSymm)
  have l0 := natEq (lw_sum (Γ := Γ) (wM0 w M) T N x)
  have lt' := natEq (lw_sum (Γ := Γ) (wMt w τ M) T N x)
  have a := natEq hA
  have f := natEq hF
  apply deriveNat; ipra_simps
  linear_combination f - a - lt' + l0

end Stopping

end LeanProofs.IPRA.Probability.OptionalStopping
