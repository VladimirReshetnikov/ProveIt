import IPRADerivations.Probability.DyadicCover
import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums

/-!
# The dyadic strong law: the maximal tail bound

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`, `thm:dyadic-slln`:
for i.i.d. samples with finite variance, `P(∃ n ∈ [2^K, H] : |X̄_n − μ| ≥ 2ε) ≤ 4σ²/(ε² 2^K)` for every finite horizon `H`.

The law is a finite weighted law `(w, X)` on `M` points (total weight `W`, `S = Σ w X`, `Q = Σ w X²`, so
`σ² = (WQ − S²)/W²`), and the threshold is `ε = e/f` for the values scaled by `f`. In iPRA, with the `H`-fold product
weights `P_H(t)` (total mass `T_H = W^H`):

* `badB`, `Pbad`: the cleared probability `Σ_{t<M^H} P_H(t) · [∃ n ≤ H : 2^K ≤ n ∧ (2enW)² ≤ |W S_n(t) − nS|²]`;
* `dyadic_slln`: `e² W² 2^K · Pbad ≤ (WQ ∸ S²) · T_H`, i.e. `P(bad) ≤ σ²/(ε² 2^K)`: the packet's bound with the
  constant `1` instead of `4`.

The proof combines `DyadicCover.cover_pt` (the bad event lies in the union of the block crossings), the finite Fubini
exchange `fubini` (`Σ_t P_H(t) Σ_j C_j(t) = Σ_j P_j`), and `DyadicAssembly.union_bound` (the geometric union bound over
the per-block Kolmogorov inequalities).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.DyadicTheorem

open_ipra
open LeanProofs.IPRA.Probability.ProductPower (Pr Tt wdB)
open LeanProofs.IPRA.Probability.DyadicBlock (pcB Cc inst2_pcB)
open LeanProofs.IPRA.Probability.DyadicSLLN (lw inst2_lw Nm Pblk pr_lift)
open LeanProofs.IPRA.Probability.DyadicAssembly (pjB Yb inst2_pjB union_bound)
open LeanProofs.IPRA.Probability.DyadicCover (bdB Zc Yc cjB inst2_cj Jb cover_pt)
open LeanProofs.IPRA.Analysis.PowerSums (mulParam inst2_mulParam sum_mul_param sum_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Final

variable (w0 X0 : PTm 2)

/-- The parameter `⟨H, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩` of the bad probability. -/
abbrev Ya (H M K e x : PTm n) : PTm n := pairT H (pairT M (pairT (pairT K e) x))

/-! ## The bad probability -/

/-- `P_H(t) · (1 ∸ ∏_{n≤H} (1 ∸ bad_n(t)))` over `(t, ⟨H, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩)`. -/
def badB : PTm 2 :=
  ap2 (prodF (wdB w0)) (fstT (var 1)) (pairT (var 0) (pairT (fstT (sndT (var 1))) (sndT (sndT (sndT (var 1)))))) *
    monus one (ap2 (prodF (monus one (bdB w0 X0))) (succ (fstT (var 1))) (pairT (var 0) (sndT (var 1))))

/-- The cleared probability of `∃ n ∈ [2^K, H] : (2enW)² ≤ |W S_n − nS|²`. -/
abbrev Pbad (H M K e x : PTm n) : PTm n := ap2 (sumF (badB w0 X0)) (pw M H) (Ya H M K e x)

theorem bad_at (t H M K e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (badB w0 X0) t (Ya H M K e x) ≐
      Pr w0 H t M x * monus one (ap2 (prodF (monus one (bdB w0 X0))) (succ H) (Zc t M K e x)) := by
  have h : inst2 (badB w0 X0) t (Ya H M K e x) =
      ap2 (prodF (wdB w0)) (fstT (Ya H M K e x))
          (pairT t (pairT (fstT (sndT (Ya H M K e x))) (sndT (sndT (sndT (Ya H M K e x)))))) *
        monus one (ap2 (prodF (monus one (bdB w0 X0))) (succ (fstT (Ya H M K e x))) (pairT t (sndT (Ya H M K e x)))) := by
    simp [badB, inst2]
  rw [h]
  have s1 : Γ ⊢[PRAAx] sndT (Ya H M K e x) ≐ pairT M (pairT (pairT K e) x) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (Ya H M K e x)) ≐ pairT (pairT K e) x := s1.sndE
  have hH : Γ ⊢[PRAAx] fstT (Ya H M K e x) ≐ H := fst_pair _ _
  have hM : Γ ⊢[PRAAx] fstT (sndT (Ya H M K e x)) ≐ M := s1.fstE
  have hx : Γ ⊢[PRAAx] sndT (sndT (sndT (Ya H M K e x))) ≐ x := s2.sndE
  exact congrMul (congrAp2 _ hH (congrPairT (.eqRefl _) (congrPairT hM hx)))
    (congrMonus (.eqRefl _) (congrAp2 _ (congrSucc hH) (congrPairT (.eqRefl _) s1)))

/-! ## The weighted crossing counts as a three-variable body -/

/-- `P_H(t)` read from the crossing parameter `⟨⟨t, H⟩, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩`. -/
def cP : PTm 1 :=
  ap2 (prodF (wdB w0)) (sndT (fstT (var 0)))
    (pairT (fstT (fstT (var 0))) (pairT (fstT (sndT (var 0))) (sndT (sndT (sndT (var 0))))))

theorem cP_at (t H M K e x : PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![Yc t H M K e x] (cP w0) ≐ Pr w0 H t M x := by
  have h : Syn.subst ![Yc t H M K e x] (cP w0) =
      ap2 (prodF (wdB w0)) (sndT (fstT (Yc t H M K e x)))
        (pairT (fstT (fstT (Yc t H M K e x)))
          (pairT (fstT (sndT (Yc t H M K e x))) (sndT (sndT (sndT (Yc t H M K e x)))))) := by
    simp [cP]
  rw [h]
  have f1 : Γ ⊢[PRAAx] fstT (Yc t H M K e x) ≐ pairT t H := fst_pair _ _
  have s1 : Γ ⊢[PRAAx] sndT (Yc t H M K e x) ≐ pairT M (pairT (pairT K e) x) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (Yc t H M K e x)) ≐ pairT (pairT K e) x := s1.sndE
  exact congrAp2 _ f1.sndE
    (congrPairT f1.fstE
      (congrPairT s1.fstE s2.sndE))

/-- `a(t, j, y) = P_H(t) · C_j(t)` with `y = ⟨H, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩`. -/
def aB : PTm 3 := Syn.subst ![var 1, pairT (pairT (var 0) (fstT (var 2))) (sndT (var 2))] (mulParam (cP w0) (cjB w0 X0))

theorem inst3_aB (t j y : PTm n) :
    inst3 (aB w0 X0) t j y = inst2 (mulParam (cP w0) (cjB w0 X0)) j (pairT (pairT t (fstT y)) (sndT y)) := by
  simp only [inst3, inst2, aB, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem aB_at (t j H M K e x : PTm n) :
    Γ ⊢[PRAAx] inst3 (aB w0 X0) t j (Ya H M K e x) ≐
      inst2 (mulParam (cP w0) (cjB w0 X0)) j (Yc t H M K e x) := by
  rw [inst3_aB]
  exact congrInst2 _ (.eqRefl _) (congrPairT (congrPairT (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

/-! ## The two orders of summation -/

theorem row_pt (j t H M K e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (aB w0 X0)) j (pairT t (Ya H M K e x)) ≐
      inst2 (mulParam (cP w0) (cjB w0 X0)) j (Yc t H M K e x) := by
  rw [inst2_rowB]
  exact (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans (aB_at w0 X0 _ _ _ _ _ _ _)

/-- The row sum over the blocks is the weighted crossing total `P_H(t) Σ_{j<J} C_j(t)`. -/
theorem row_at (t J H M K e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB (aB w0 X0)) t (pairT J (Ya H M K e x)) ≐
      Pr w0 H t M x * ap2 (sumF (cjB w0 X0)) J (Yc t H M K e x) := by
  rw [inst2_oB]
  refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine (sum_congr_bounded (rowB (aB w0 X0)) (mulParam (cP w0) (cjB w0 X0)) (pairT t (Ya H M K e x))
    (Yc t H M K e x) J (.allI (.impI ?_))).eqTrans ?_
  · simpa [Syn.shift] using row_pt (Γ := lt (var 0) (Syn.shift J) :: Γ.map Fm.shift) w0 X0 (var 0) (Syn.shift t)
      (Syn.shift H) (Syn.shift M) (Syn.shift K) (Syn.shift e) (Syn.shift x)
  · exact (sum_mul_param (cP w0) (cjB w0 X0) J (Yc t H M K e x)).eqTrans (congrMul (cP_at w0 t H M K e x) (.eqRefl _))

theorem col_pt (i j H M K e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (aB w0 X0)) i (pairT j (Ya H M K e x)) ≐
      inst2 (pcB (lw w0) (lw X0) (DyadicSLLN.aB w0)) i (pairT (Nm (K + j) H) (pairT H (pairT M (pairT (pairT (K + j) e) x)))) := by
  rw [inst2_colB]
  refine (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ((aB_at w0 X0 _ _ _ _ _ _ _).eqTrans ?_)
  rw [inst2_mulParam]
  refine (congrMul (cP_at w0 _ _ _ _ _ _) (inst2_cj w0 X0 _ _ _ _ _ _ _)).eqTrans ?_
  exact (congrMul (pr_lift w0 _ _ _ _ _ _).eqSymm (.eqRefl _)).eqTrans (inst2_pcB _ _ _ _ _ _ _ _).eqSymm

/-- The column sum over the outcomes is the cleared block probability `P_{K+j}`. -/
theorem col_at (j H M K e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (aB w0 X0)) j (pairT (pw M H) (Ya H M K e x)) ≐ inst2 (pjB w0 X0) j (Yb K e H M x) := by
  rw [inst2_pB]
  refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine (sum_congr_bounded (colB (aB w0 X0)) (pcB (lw w0) (lw X0) (DyadicSLLN.aB w0)) (pairT j (Ya H M K e x))
    (pairT (Nm (K + j) H) (pairT H (pairT M (pairT (pairT (K + j) e) x)))) (pw M H) (.allI (.impI ?_))).eqTrans
    (inst2_pjB w0 X0 j K e H M x).eqSymm
  simpa [Syn.shift] using col_pt (Γ := lt (var 0) (Syn.shift (pw M H)) :: Γ.map Fm.shift) w0 X0 (var 0) (Syn.shift j)
    (Syn.shift H) (Syn.shift M) (Syn.shift K) (Syn.shift e) (Syn.shift x)

theorem lw_pt (i J y : PTm n) : Γ ⊢[PRAAx] inst2 (badB w0 X0) i y ≐ inst2 (lw (badB w0 X0)) i (pairT J y) := by
  rw [inst2_lw]; exact congrInst2 _ (.eqRefl _) (snd_pair _ _).eqSymm

/-- Pointwise: the bad indicator is covered by the block crossings. -/
theorem cover_wt (t H M K e x : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (lw (badB w0 X0)) t (pairT (Jb H K) (Ya H M K e x)))
      (inst2 (oB (aB w0 X0)) t (pairT (Jb H K) (Ya H M K e x))) :=
  le_congr ((bad_at w0 X0 _ _ _ _ _ _).eqSymm.eqTrans (lw_pt w0 X0 _ _ _))
    (row_at w0 X0 _ _ _ _ _ _ _).eqSymm (le_mul_mono (le_refl _) (cover_pt w0 X0 _ _ _ _ _ _))

/-! ## The theorem -/

/-- `thm:dyadic-slln`: `e² W² 2^K · P(∃ n ∈ [2^K, H] : (2enW)² ≤ |W S_n − nS|²) ≤ (WQ ∸ S²) T_H`. -/
theorem dyadic_slln {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w0) M x ≐ succ (pred (ap2 (sumF w0) M x))) (H K e : PTm n) :
    Γ ⊢[PRAAx] le (e * e * (ap2 (sumF w0) M x * ap2 (sumF w0) M x) * pw two K * Pbad w0 X0 H M K e x)
      (monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
        (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x) := by
  -- move the bad probability to the parameter `⟨J, y⟩` of the Fubini sums
  have e0 : Γ ⊢[PRAAx] Pbad w0 X0 H M K e x ≐
      ap2 (sumF (lw (badB w0 X0))) (pw M H) (pairT (Jb H K) (Ya H M K e x)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simpa [Syn.shift] using lw_pt (Γ := lt (var 0) (Syn.shift (pw M H)) :: Γ.map Fm.shift) w0 X0 (var 0)
      (Syn.shift (Jb H K)) (Syn.shift (Ya H M K e x))
  -- pointwise: the bad indicator is covered by the block crossings
  have hL : Γ ⊢[PRAAx] le (ap2 (sumF (lw (badB w0 X0))) (pw M H) (pairT (Jb H K) (Ya H M K e x)))
      (ap2 (sumF (oB (aB w0 X0))) (pw M H) (pairT (Jb H K) (Ya H M K e x))) := by
    refine sum_le _ _ _ _ (.allI (.impI ?_))
    simpa [Syn.shift] using cover_wt (Γ := lt (var 0) (Syn.shift (pw M H)) :: Γ.map Fm.shift) w0 X0 (var 0)
      (Syn.shift H) (Syn.shift M) (Syn.shift K) (Syn.shift e) (Syn.shift x)
  -- exchange the sums and identify the block probabilities
  have hF := fubini (Γ := Γ) (aB w0 X0) (pw M H) (Jb H K) (Ya H M K e x)
  have hR : Γ ⊢[PRAAx] ap2 (sumF (pB (aB w0 X0))) (Jb H K) (pairT (pw M H) (Ya H M K e x)) ≐
      ap2 (sumF (pjB w0 X0)) (Jb H K) (Yb K e H M x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simpa [Syn.shift] using col_at (Γ := lt (var 0) (Syn.shift (Jb H K)) :: Γ.map Fm.shift) w0 X0 (var 0)
      (Syn.shift H) (Syn.shift M) (Syn.shift K) (Syn.shift e) (Syn.shift x)
  have hP : Γ ⊢[PRAAx] le (Pbad w0 X0 H M K e x) (ap2 (sumF (pjB w0 X0)) (Jb H K) (Yb K e H M x)) :=
    le_congr e0.eqSymm (hF.eqTrans hR) hL
  exact le_trans (le_mul_mono (le_refl _) hP) (union_bound w0 X0 hM hW K e (Jb H K))

end Final

end LeanProofs.IPRA.Probability.DyadicTheorem
