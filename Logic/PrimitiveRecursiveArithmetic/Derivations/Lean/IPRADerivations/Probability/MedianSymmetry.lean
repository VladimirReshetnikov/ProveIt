import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Probability.Lotus

/-!
# The CDF characterization and the symmetry centre of a finite law

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:cdf` and the median and mean
claims of Theorem `thm:symmetry`, for a finite weighted law (weights `w_j`, support values `a_j`,
`j < N`) with the weighted counts `B`, `E`, `A` of `Probability/MedianWeighted`.

* `cdf_of_med`, `med_of_cdf` (`thm:cdf`): `t` is a weighted median iff
  `2B(t) ≤ W ≤ 2(B(t) + E(t))`, i.e. `F(t⁻) ≤ 1/2 ≤ F(t)` cleared of `W`;
* `refl_monus`: `a + b = 2c` gives `c ∸ b = a ∸ c`;
* `sym_counts`, `sym_median`, `sym_mean` (`thm:symmetry`): if an involution `σ` of `[0, N)` has
  `a_j + a_{σ(j)} = 2c` and `w_{σ(j)} = w_j`, then `B(c) = A(c)`, `c` is a weighted median, and
  `∑ w_j a_j = c W`, so the mean is `c`. The involution is a body over the parameter `⟨c, p⟩`,
  and the reindexing is `Totatives.sum_perm`.

The mode statements of `thm:symmetry` and the continuous laws are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianSymmetry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul')
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.Probability.MedianCounts
open LeanProofs.IPRA.Probability.MedianWeighted
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos two_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Reflection of a truncated difference -/

theorem refl_monus₁ {a b c : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ two * c) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] monus c b ≐ monus a c := by
  have hh := natEq h; have f1 := natEq hac; have f2 := natEq (eq_add_of_le hac)
  have hcb : Γ ⊢[PRAAx] le c b := le_of_eq_add (d := monus c a) (by
    apply deriveNat; ipra_simps; linear_combination hh + f2)
  have g1 := natEq hcb
  apply deriveNat; ipra_simps
  linear_combination g1 - f1

theorem refl_monus₂ {a b c : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ two * c) (hca : Γ ⊢[PRAAx] le c a) :
    Γ ⊢[PRAAx] monus c b ≐ monus a c := by
  have hh := natEq h; have f1 := natEq hca; have f2 := natEq (eq_add_of_le hca)
  have hbc : Γ ⊢[PRAAx] c ≐ b + monus a c := by
    apply deriveNat; ipra_simps; linear_combination f2 - hh
  have e := natEq hbc
  have g2 := natEq (eq_add_of_le (le_of_eq_add hbc))
  apply deriveNat; ipra_simps
  linear_combination e - g2

/-- `a + b = 2c` gives `c ∸ b = a ∸ c`. -/
theorem refl_monus {a b c : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ two * c) : Γ ⊢[PRAAx] monus c b ≐ monus a c :=
  .orE (le_total a c) (refl_monus₁ h.wk Prf.hyp0) (refl_monus₂ h.wk Prf.hyp0)

section Law

variable (w X : PTm 2)

/-! ## The CDF characterization -/

/-- `thm:cdf`, forward: a weighted median has `2B(t) ≤ W ≤ 2(B(t) + E(t))`. -/
theorem cdf_of_med {N t p : PTm n} (hm : Γ ⊢[PRAAx] isMedW w X N t p) :
    Γ ⊢[PRAAx] le (two * WB w X N t p) (Wt w N p) ⋏ le (Wt w N p) (two * (WB w X N t p + WE w X N t p)) := by
  refine .andI (Prf.andE₁ hm) ?_
  have part := natEq (w_partition (Γ := Γ) w X N t p)
  have hs := natEq (eq_add_of_le (Prf.andE₂ hm))
  refine le_of_eq_add (d := monus (Wt w N p) (two * WA w X N t p)) ?_
  apply deriveNat; ipra_simps
  linear_combination 2 * part + hs

/-- `thm:cdf`, backward: `2B(t) ≤ W ≤ 2(B(t) + E(t))` makes `t` a weighted median. -/
theorem med_of_cdf {N t p : PTm n} (h₁ : Γ ⊢[PRAAx] le (two * WB w X N t p) (Wt w N p))
    (h₂ : Γ ⊢[PRAAx] le (Wt w N p) (two * (WB w X N t p + WE w X N t p))) : Γ ⊢[PRAAx] isMedW w X N t p := by
  refine .andI h₁ ?_
  have part := natEq (w_partition (Γ := Γ) w X N t p)
  have hk := natEq (eq_add_of_le h₂)
  refine le_of_eq_add (d := monus (two * (WB w X N t p + WE w X N t p)) (Wt w N p)) ?_
  apply deriveNat; ipra_simps
  linear_combination -2 * part + hk

/-! ## Symmetric laws -/

variable (S : PTm 2)

theorem sym_pt {i c p : PTm n}
    (hs : Γ ⊢[PRAAx] inst2 X i p + inst2 X (inst2 S i (pairT c p)) p ≐ two * c)
    (hw : Γ ⊢[PRAAx] inst2 w (inst2 S i (pairT c p)) p ≐ inst2 w i p) :
    Γ ⊢[PRAAx] inst2 (Permutation.FS (wL w * belowB X) S) i (pairT c p) ≐ inst2 (wL w * aboveB X) i (pairT c p) := by
  rw [Permutation.inst2_FS]
  exact (wb_pt w X _ c p).eqTrans ((congrMul hw (congrSg (refl_monus hs))).eqTrans (wa_pt w X i c p).eqSymm)

/-- `a_j + a_{σ(j)} = 2c` for `j < N`. -/
abbrev symAll (N c p : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 X (var 0) (Syn.shift p) +
    inst2 X (inst2 S (var 0) (Syn.shift (pairT c p))) (Syn.shift p) ≐ two * Syn.shift c))

/-- `w_{σ(j)} = w_j` for `j < N`. -/
abbrev wtAll (N c p : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    (inst2 w (inst2 S (var 0) (Syn.shift (pairT c p))) (Syn.shift p) ≐ inst2 w (var 0) (Syn.shift p)))

theorem shift_pairT' (c p : PTm n) : Syn.shift (pairT c p) = pairT (Syn.shift c) (Syn.shift p) := by
  simp [Syn.shift]

/-- `B(c) = A(c)` for a law symmetric about `c`. -/
theorem sym_counts {τ : PTm 2} {N c p : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S N (pairT c p))
    (hinv : Γ ⊢[PRAAx] Permutation.invAll S τ N (pairT c p)) (hret : Γ ⊢[PRAAx] Permutation.retAll S τ N (pairT c p))
    (hsym : Γ ⊢[PRAAx] symAll X S N c p) (hw : Γ ⊢[PRAAx] wtAll w S N c p) :
    Γ ⊢[PRAAx] WB w X N c p ≐ WA w X N c p := by
  refine (AnalyticNumberTheory.Totatives.sum_perm hr hinv hret).eqSymm.eqTrans ?_
  refine sum_congr_bounded _ _ _ _ N (.allI (.impI ?_))
  have h1 := Prf.impE hsym.allOpen.wk Prf.hyp0
  have h2 := Prf.impE hw.allOpen.wk Prf.hyp0
  rw [shift_pairT'] at h1 h2 ⊢
  exact sym_pt w X S h1 h2

/-- `thm:symmetry`: the centre `c` of a symmetric finite law is a weighted median. -/
theorem sym_median {τ : PTm 2} {N c p : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S N (pairT c p))
    (hinv : Γ ⊢[PRAAx] Permutation.invAll S τ N (pairT c p)) (hret : Γ ⊢[PRAAx] Permutation.retAll S τ N (pairT c p))
    (hsym : Γ ⊢[PRAAx] symAll X S N c p) (hw : Γ ⊢[PRAAx] wtAll w S N c p) :
    Γ ⊢[PRAAx] isMedW w X N c p := by
  have BA := natEq (sym_counts w X S hr hinv hret hsym hw)
  have part := natEq (w_partition (Γ := Γ) w X N c p)
  refine .andI (le_of_eq_add (d := WE w X N c p) ?_) (le_of_eq_add (d := WE w X N c p) ?_)
  · apply deriveNat; ipra_simps; linear_combination -part - BA
  · apply deriveNat; ipra_simps; linear_combination -part + BA

theorem g_pt (i c p : PTm n) :
    Γ ⊢[PRAAx] inst2 (wL w * wL X) i (pairT c p) ≐ inst2 w i p * inst2 X i p := by
  refine (wc_pt w (wL X) i c p).eqTrans (congrMul (.eqRefl _) ?_)
  have e : inst2 (wL X) i (pairT c p) = inst2 X i (sndT (pairT c p)) := subst_data i (pairT c p) X
  rw [e]
  exact congrInst2 X (.eqRefl _) (snd_pair _ _)

theorem mean_pt {i c p : PTm n}
    (hs : Γ ⊢[PRAAx] inst2 X i p + inst2 X (inst2 S i (pairT c p)) p ≐ two * c)
    (hw : Γ ⊢[PRAAx] inst2 w (inst2 S i (pairT c p)) p ≐ inst2 w i p) :
    Γ ⊢[PRAAx] inst2 (addBody (Permutation.FS (wL w * wL X) S) (wL w * wL X)) i (pairT c p) ≐
      inst2 (cmB w) i (pairT (two * c) p) := by
  rw [inst2_addBody, Permutation.inst2_FS, inst2_cmB]
  have a := natEq (g_pt (Γ := Γ) w X (inst2 S i (pairT c p)) c p)
  have b := natEq (g_pt (Γ := Γ) w X i c p)
  have k := natEq (congrMul (fst_pair (Γ := Γ) (two * c) p) (congrInst2 w (.eqRefl i) (snd_pair (two * c) p)))
  have s := natEq hs; have v := natEq hw
  apply deriveNat; ipra_simps
  linear_combination a + b - k + 𝔞 (inst2 w i p) * s + 𝔞 (inst2 X (inst2 S i (pairT c p)) p) * v

/-- `thm:symmetry`: the mean of a symmetric finite law is its centre, `∑ w_j a_j = c W`. -/
theorem sym_mean {τ : PTm 2} {N c p : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S N (pairT c p))
    (hinv : Γ ⊢[PRAAx] Permutation.invAll S τ N (pairT c p)) (hret : Γ ⊢[PRAAx] Permutation.retAll S τ N (pairT c p))
    (hsym : Γ ⊢[PRAAx] symAll X S N c p) (hw : Γ ⊢[PRAAx] wtAll w S N c p) :
    Γ ⊢[PRAAx] Ew w X N p ≐ c * Wt w N p := by
  have eS : Γ ⊢[PRAAx] Ew w X N p ≐ ap2 (sumF (wL w * wL X)) N (pairT c p) := by
    refine sum_congr_bounded (w * X) (wL w * wL X) p (pairT c p) N (.allI (.impI ?_))
    rw [inst2_mul', shift_pairT']
    exact (g_pt w X _ _ _).eqSymm
  have eP := AnalyticNumberTheory.Totatives.sum_perm (f := wL w * wL X) hr hinv hret
  have eC : Γ ⊢[PRAAx] ap2 (sumF (addBody (Permutation.FS (wL w * wL X) S) (wL w * wL X))) N (pairT c p) ≐
      ap2 (sumF (cmB w)) N (pairT (two * c) p) := by
    refine sum_congr_bounded _ _ _ _ N (.allI (.impI ?_))
    have h1 := Prf.impE hsym.allOpen.wk Prf.hyp0
    have h2 := Prf.impE hw.allOpen.wk Prf.hyp0
    rw [shift_pairT'] at h1 h2 ⊢
    have e3 : Syn.shift (pairT (two * c) p) = pairT (two * Syn.shift c) (Syn.shift p) := by simp [Syn.shift]
    rw [e3]
    exact mean_pt w X S h1 h2
  have tot := natEq ((sum_add _ _ _ _).eqSymm.eqTrans (eC.eqTrans (sum_const_mul (Γ := Γ) w N (two * c) p)))
  have s1 := natEq eS; have s2 := natEq eP
  have e2 : Γ ⊢[PRAAx] two * Ew w X N p ≐ two * (c * Wt w N p) := by
    apply deriveNat; ipra_simps
    linear_combination tot + 2 * s1 - s2
  exact le_antisymm (le_cancel_pos two_pos (le_congr (.eqRefl _) e2 (le_refl _)))
    (le_cancel_pos two_pos (le_congr (.eqRefl _) e2.eqSymm (le_refl _)))

end Law

end LeanProofs.IPRA.Probability.MedianSymmetry
