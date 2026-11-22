import IPRADerivations.AnalyticNumberTheory.BlockMean
import IPRADerivations.AnalyticNumberTheory.PointDeficit

/-!
# Block sums over divisors (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:deficit`. The
deficit is a sum over a block of divisors `D₁ < d ≤ D₂` (a logarithmic block of `m = ⌊x/d⌋`). Block sums are written
with one parameter layout

  `y = (D₁, (D₂, (w, z)))`,  `w = (A, D)` (the stage level `a = A/D`),  `z = (K, F)` (mesh, `F = L!`),

and the body `[D₁ < d ≤ D₂] h(⌊x/d⌋)` (`SummatoryCompose.hRB h biB`). This module gives

* `biB`, `bi_split`: `[d ≤ D₂] = [d ≤ D₁] + [D₁ < d ≤ D₂]` for `D₁ ≤ D₂`;
* `pzB`, `fzB`: `ψ(m)` and `Fm` read from the layout;
* `block_psi`, `block_f`: the prefix sums `T_Λ`, `T_F` of `BlockMean` split at `D₁`;
* `block_mean_upper`, `block_mean_lower`: `|Σ_{D₁<d≤D₂} (ψ(⌊x/d⌋) − F⌊x/d⌋)| ≤ 24Fx` in the layout.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (psiB inst2_psiB psi_bs)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedSplit (lamW hRB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (inst2_lamW)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB RB_at bS inst2_bS Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock (iB inst2_iB ind_one ind_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFloor (lB fB lB_at fB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockMean (T block_upper block_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.Probability.Variance (sum_const_of)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The layout `(D₁, (D₂, (w, z)))`. -/
abbrev Y (D₁ D₂ w z : PTm n) : PTm n := pairT D₁ (pairT D₂ (pairT w z))

/-- `[D₁ < d ≤ D₂]`. -/
abbrev biB : PTm 2 :=
  monus (monus one (monus (var 0) (fstT (sndT (var 1))))) (monus one (monus (var 0) (fstT (var 1))))
/-- `ψ(m)` at `z`. -/
abbrev pzB : PTm 2 := Syn.subst ![var 0, sndT (sndT (sndT (var 1)))] psiB
/-- `F m` at `z = (K, F)`. -/
abbrev fzB : PTm 2 := sndT (sndT (sndT (sndT (var 1)))) * var 0

theorem bi_at (d D₁ D₂ w z : PTm n) :
    Γ ⊢[PRAAx] inst2 biB d (Y D₁ D₂ w z) ≐ monus (monus one (monus d D₂)) (monus one (monus d D₁)) := by
  rw [show inst2 biB d (Y D₁ D₂ w z) = monus (monus one (monus d (fstT (sndT (Y D₁ D₂ w z)))))
    (monus one (monus d (fstT (Y D₁ D₂ w z)))) by simp [inst2]]
  exact congrMonus (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))))
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _)))

theorem pz_at (m D₁ D₂ w K F : PTm n) :
    Γ ⊢[PRAAx] inst2 pzB m (Y D₁ D₂ w (pairT K F)) ≐ Psi wt m (pairT K F) := by
  rw [show inst2 pzB m (Y D₁ D₂ w (pairT K F)) = inst2 psiB m (sndT (sndT (sndT (Y D₁ D₂ w (pairT K F))))) by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp]
  rw [inst2_psiB]
  exact congrAp2 _ (.eqRefl _) ((congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))

theorem fz_at (m D₁ D₂ w K F : PTm n) : Γ ⊢[PRAAx] inst2 fzB m (Y D₁ D₂ w (pairT K F)) ≐ F * m := by
  rw [show inst2 fzB m (Y D₁ D₂ w (pairT K F)) = sndT (sndT (sndT (sndT (Y D₁ D₂ w (pairT K F))))) * m by simp [inst2]]
  exact congrMul ((congrSnd ((congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _)) (.eqRefl _)

theorem ind1 {d D : PTm n} (h : Γ ⊢[PRAAx] le d D) : Γ ⊢[PRAAx] monus one (monus d D) ≐ one :=
  (congrMonus (.eqRefl one) h).eqTrans (monus_zero _)

theorem ind0 {d D : PTm n} (h : Γ ⊢[PRAAx] lt D d) : Γ ⊢[PRAAx] monus one (monus d D) ≐ zero := by
  have e : Γ ⊢[PRAAx] d ≐ succ (monus d (succ D)) + D := by
    have a := natEq (eq_add_of_le h); apply deriveNat; ipra_simps; linear_combination a
  exact (congrMonus (.eqRefl one) ((congrMonus e (.eqRefl D)).eqTrans (add_monus _ _))).eqTrans
    ((succ_monus_succ _ _).eqTrans (zero_monus _))

theorem ia_at (d D z : PTm n) : Γ ⊢[PRAAx] inst2 iB d (pairT D z) ≐ monus one (monus d D) := by
  rw [inst2_iB]; exact congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _))

/-- `[d ≤ D₂] = [d ≤ D₁] + [D₁ < d ≤ D₂]` for `D₁ ≤ D₂`. -/
theorem bi_split {d D₁ D₂ : PTm n} (h : Γ ⊢[PRAAx] le D₁ D₂) :
    Γ ⊢[PRAAx] monus one (monus d D₂) ≐
      monus one (monus d D₁) + monus (monus one (monus d D₂)) (monus one (monus d D₁)) := by
  refine .orE (lt_or_le D₁ d) ?_ ?_
  · have z1 := ind0 (Prf.hyp0 : ((lt D₁ d) :: Γ) ⊢[PRAAx] lt D₁ d)
    exact ((monus_zero _).eqSymm.eqTrans (zero_add _).eqSymm).eqTrans
      (congrAdd z1.eqSymm (congrMonus (.eqRefl _) z1.eqSymm))
  · have o1 := ind1 (Prf.hyp0 : ((le d D₁) :: Γ) ⊢[PRAAx] le d D₁)
    have o2 := ind1 (le_trans (Prf.hyp0 : ((le d D₁) :: Γ) ⊢[PRAAx] le d D₁) h.wk)
    have r := (congrAdd o1 (congrMonus o2 o1)).eqTrans ((congrAdd (.eqRefl _) (monus_self _)).eqTrans (add_zero _))
    exact o2.eqTrans r.eqSymm

theorem split_alg {s a1 a2 b p : PTm n} (h : Γ ⊢[PRAAx] a2 ≐ a1 + b) :
    Γ ⊢[PRAAx] (s * a2) * p ≐ (s * a1) * p + (s * b) * p := by
  have e := natEq h; apply deriveNat; ipra_simps; linear_combination 𝔞 s * 𝔞 p * e

theorem bs_lam (m D K F : PTm n) : Γ ⊢[PRAAx] Bs lB m (pairT D (pairT K F)) ≐ Psi wt m (pairT K F) := by
  have c : Γ ⊢[PRAAx] Bs lB m (pairT D (pairT K F)) ≐ Bs lamW m (pairT K F) :=
    sum_congr_bounded _ _ _ _ _ (.allI (.impI (by
      rw [inst2_bS, inst2_bS]; simp only [shift_pairT]; rw [inst2_lamW]; exact lB_at _ _ _)))
  have p := (psi_bs (Γ := Γ) m (pairT K F)).eqSymm
  rw [inst2_psiB] at p
  exact c.eqTrans p

theorem bs_f (m D K F : PTm n) : Γ ⊢[PRAAx] Bs fB m (pairT D (pairT K F)) ≐ F * m := by
  refine (sum_const_of (Γ := Γ) (bS fB) m F (pairT D (pairT K F)) (.allI (.impI ?_))).eqTrans (mul_comm _ _)
  rw [inst2_bS]; simp only [shift_pairT]
  exact fB_at _ _ _ _

/-- `T_Λ(D₂) = T_Λ(D₁) + Σ_{D₁<d≤D₂} ψ(⌊x/d⌋)`. -/
theorem block_psi {x D₁ D₂ w K F : PTm n} (h : Γ ⊢[PRAAx] le D₁ D₂) :
    Γ ⊢[PRAAx] T lB x D₂ (pairT K F) ≐
      T lB x D₁ (pairT K F) + ap2 (sumF (hRB pzB biB)) (succ x) (pairT x (Y D₁ D₂ w (pairT K F))) := by
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₁) (Syn.shift D₂) := by simpa [Fm.shift, Syn.shift] using h.shift
  refine sum_add2 _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact ((RB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (ia_at _ _ _)) (bs_lam _ _ _ _))).eqTrans
    ((split_alg (bi_split h'.wk)).eqTrans (congrAdd
      ((RB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (ia_at _ _ _)) (bs_lam _ _ _ _)))
      ((hRB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (bi_at _ _ _ _ _)) (pz_at _ _ _ _ _ _)))).eqSymm)

/-- `T_F(D₂) = T_F(D₁) + Σ_{D₁<d≤D₂} F⌊x/d⌋`. -/
theorem block_f {x D₁ D₂ w K F : PTm n} (h : Γ ⊢[PRAAx] le D₁ D₂) :
    Γ ⊢[PRAAx] T fB x D₂ (pairT K F) ≐
      T fB x D₁ (pairT K F) + ap2 (sumF (hRB fzB biB)) (succ x) (pairT x (Y D₁ D₂ w (pairT K F))) := by
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₁) (Syn.shift D₂) := by simpa [Fm.shift, Syn.shift] using h.shift
  refine sum_add2 _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact ((RB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (ia_at _ _ _)) (bs_f _ _ _ _))).eqTrans
    ((split_alg (bi_split h'.wk)).eqTrans (congrAdd
      ((RB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (ia_at _ _ _)) (bs_f _ _ _ _)))
      ((hRB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (bi_at _ _ _ _ _)) (fz_at _ _ _ _ _ _)))).eqSymm)

section Mean

variable {x D₁ D₂ K L w : PTm n}
  (h1 : Γ ⊢[PRAAx] le one D₁) (h12 : Γ ⊢[PRAAx] le D₁ D₂) (h2x : Γ ⊢[PRAAx] le D₂ x) (hK1 : Γ ⊢[PRAAx] le one K)
  (hPK : Γ ⊢[PRAAx] le (quo x D₁) K) (hPK' : Γ ⊢[PRAAx] le (quo x D₂) K)
  (hNN : Γ ⊢[PRAAx] le (K * pw (quo x D₁) (quo x D₁)) L) (hNN' : Γ ⊢[PRAAx] le (K * pw (quo x D₂) (quo x D₂)) L)
  (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)

include h1 h12 h2x hK1 hPK hPK' hNN hNN' hKx hP

/-- `Σ_{D₁<d≤D₂} ψ(⌊x/d⌋) ≤ Σ_{D₁<d≤D₂} F⌊x/d⌋ + 24Fx`. -/
theorem block_mean_upper :
    Γ ⊢[PRAAx] le (ap2 (sumF (hRB pzB biB)) (succ x) (pairT x (Y D₁ D₂ w (pairT K (fact L)))))
      (ap2 (sumF (hRB fzB biB)) (succ x) (pairT x (Y D₁ D₂ w (pairT K (fact L)))) + num 24 * (fact L * x)) := by
  have u := block_upper h1 h12 h2x hK1 hPK hPK' hNN hNN' hKx hP
  have bp := natEq (block_psi (Γ := Γ) (x := x) (w := w) (K := K) (F := fact L) h12)
  have bf := natEq (block_f (Γ := Γ) (x := x) (w := w) (K := K) (F := fact L) h12)
  ipra_le sl u with bp - bf

/-- `Σ_{D₁<d≤D₂} F⌊x/d⌋ ≤ Σ_{D₁<d≤D₂} ψ(⌊x/d⌋) + 24Fx`. -/
theorem block_mean_lower :
    Γ ⊢[PRAAx] le (ap2 (sumF (hRB fzB biB)) (succ x) (pairT x (Y D₁ D₂ w (pairT K (fact L)))))
      (ap2 (sumF (hRB pzB biB)) (succ x) (pairT x (Y D₁ D₂ w (pairT K (fact L)))) + num 24 * (fact L * x)) := by
  have u := block_lower h1 h12 h2x hK1 hPK hPK' hNN hNN' hKx hP
  have bp := natEq (block_psi (Γ := Γ) (x := x) (w := w) (K := K) (F := fact L) h12)
  have bf := natEq (block_f (Γ := Γ) (x := x) (w := w) (K := K) (F := fact L) h12)
  ipra_le sl u with bf - bp

end Mean

end LeanProofs.IPRA.AnalyticNumberTheory.BlockSums
