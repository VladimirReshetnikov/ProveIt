import IPRADerivations.AnalyticNumberTheory.BlockDeficitMain
import IPRADerivations.AnalyticNumberTheory.ContractionSplit
import IPRADerivations.Core.Header
import IPRADerivations.Core.SumOrder

/-!
# The head of the weighted sum with its deficit (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:one-step`:
"`∫_0^t (t − u)|r(u)| du ≤ at²/2 + 4st − b (t/2)(1/(64q²))`". In the head `d ≤ N` of the weighted sum
(`ContractionSplit`) the stage bound `D|R(m)| ≤ AFm` makes the deficit exact, `g = AFm − D|R(m)|`, so

  `D Σ_{d≤N} 2F u_d |R(⌊x/d⌋)| + 2F Σ_{d≤N} u_d g(⌊x/d⌋) ≤ A F x (u_N² + 2F²)`  (`head_deficit`),

with the weighted deficit sum written in the block layout of `BlockSums` (`wuB = [D₁ < d ≤ D₂] u_d`), so that the
block deficits of `BlockDeficitMain` can be inserted below it.

* `sum_le_three`: summing `a₁ f₁ + a₂ f₂ ≤ c g` with separate parameters;
* `uwL`, `uw_at'`, `wuB`: the weight `u_d` read from the layout;
* `hd_eq`: the head deficit sum as a sum over `j < M` at `d = j + 2`;
* `hd_pt`: the exact pointwise identity `D·body + 2F u g = 2AF·u F m`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.HeadDeficit

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionMain (mtB main_term)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit (wbB Bd body_at mt_at head_eq Stage)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockSums (biB bi_at)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (gzB gz_at bv bv_in bv_above)
open LeanProofs.IPRA.AnalyticNumberTheory.PointDeficit (dg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Summing with separate parameters -/

/-- `a₁ f₁(i, x₁) + a₂ f₂(i, x₂) ≤ c g(i, y)` for `i < N` gives the same for the sums. -/
theorem sum_le_three (f1 f2 g : PTm 2) (a1 a2 c x1 x2 y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a1 * inst2 f1 (var 0) (Syn.shift x1) + Syn.shift a2 * inst2 f2 (var 0) (Syn.shift x2))
        (Syn.shift c * inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] le (a1 * ap2 (sumF f1) N x1 + a2 * ap2 (sumF f2) N x2) (c * ap2 (sumF g) N y) := by
  refine le_congr (.eqRefl _) ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _))
    (sum_weighted_pair_le f1 f2 g g a1 a2 c zero x1 x2 y y N (.allI (.impI ?_)))
  rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
  exact le_congr (.eqRefl _) ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)).eqSymm
    (.impE h.allOpen.wk Prf.hyp0)

/-! ## The weight `u_d` in the block layout -/

abbrev KL : PTm 2 := fstT (sndT (sndT (sndT (var 1))))
abbrev FL : PTm 2 := sndT (sndT (sndT (sndT (var 1))))
/-- `u_d = S(Kd) − S(K)` read from the layout. -/
abbrev uwL : PTm 2 := monus (ap2 (sumF hB) (KL * var 0) FL) (ap2 (sumF hB) KL FL)
/-- `[D₁ < d ≤ D₂] u_d`. -/
abbrev wuB : PTm 2 := biB * uwL

theorem kF_at (D₁ D₂ w K F : PTm n) :
    (Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (BlockSums.Y D₁ D₂ w (pairT K F))))) ≐ K) ∧
      (Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (BlockSums.Y D₁ D₂ w (pairT K F))))) ≐ F) := by
  have z : Γ ⊢[PRAAx] sndT (sndT (sndT (BlockSums.Y D₁ D₂ w (pairT K F)))) ≐ pairT K F :=
    (congrSnd ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
  exact ⟨(congrFst z).eqTrans (fst_pair _ _), (congrSnd z).eqTrans (snd_pair _ _)⟩

theorem uw_at' (d D₁ D₂ w K F : PTm n) :
    Γ ⊢[PRAAx] inst2 uwL d (BlockSums.Y D₁ D₂ w (pairT K F)) ≐ U d K F := by
  rw [show inst2 uwL d (BlockSums.Y D₁ D₂ w (pairT K F)) =
      monus (ap2 (sumF hB) (fstT (sndT (sndT (sndT (BlockSums.Y D₁ D₂ w (pairT K F))))) * d)
          (sndT (sndT (sndT (sndT (BlockSums.Y D₁ D₂ w (pairT K F)))))))
        (ap2 (sumF hB) (fstT (sndT (sndT (sndT (BlockSums.Y D₁ D₂ w (pairT K F))))))
          (sndT (sndT (sndT (sndT (BlockSums.Y D₁ D₂ w (pairT K F))))))) by simp [inst2]]
  have ⟨hk, hf⟩ := kF_at (Γ := Γ) D₁ D₂ w K F
  exact congrMonus (congrAp2 _ (congrMul hk (.eqRefl _)) hf) (congrAp2 _ hk hf)

theorem wu_at (d D₁ D₂ w K F : PTm n) :
    Γ ⊢[PRAAx] inst2 wuB d (BlockSums.Y D₁ D₂ w (pairT K F)) ≐ bv d D₁ D₂ * U d K F := by
  rw [show inst2 wuB d (BlockSums.Y D₁ D₂ w (pairT K F)) =
    inst2 biB d (BlockSums.Y D₁ D₂ w (pairT K F)) * inst2 uwL d (BlockSums.Y D₁ D₂ w (pairT K F)) by simp [inst2]]
  exact congrMul (bi_at _ _ _ _ _) (uw_at' _ _ _ _ _ _)

/-- `[d ≥ 1][D₁ < d ≤ D₂] u_d g(⌊x/d⌋)` in the block layout. -/
abbrev hgB : PTm 2 := hRB gzB wuB

theorem hg_at (d X D₁ D₂ A Ds K F : PTm n) :
    Γ ⊢[PRAAx] inst2 hgB d (pairT X (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K F))) ≐
      (sg d * (bv d D₁ D₂ * U d K F)) * dg A Ds (Psi wt (quo X d) (pairT K F)) (F * quo X d) :=
  (hRB_at _ _ _ _ _).eqTrans (congrMul (congrMul (.eqRefl _) (wu_at _ _ _ _ _ _)) (gz_at _ _ _ _ _ _ _))

/-! ## The head deficit sum at `d = j + 2` -/

section Head

variable {M x A Ds K L : PTm n}

abbrev HP (M x A Ds K L : PTm n) : PTm n := pairT x (BlockSums.Y zero (succ M) (pairT A Ds) (pairT K (fact L)))

/-- `Σ_{d≤x} [0 < d ≤ M + 1] u_d g = Σ_{j<M} u_{j+2} g` (the terms `d = 0, 1` vanish). -/
theorem hd_eq (hMx : Γ ⊢[PRAAx] le (succ M) x) :
    Γ ⊢[PRAAx] ap2 (sumF hgB) (succ x) (HP M x A Ds K L) ≐
      ap2 (sumF (shiftBody (shiftBody hgB))) M (HP M x A Ds K L) := by
  have hS : Γ ⊢[PRAAx] le (succ (succ M)) (succ x) := (succ_monus_succ _ _).eqTrans hMx
  have hM' : (Γ.map Fm.shift) ⊢[PRAAx] le zero (succ (Syn.shift M)) := zero_le _
  refine (sum_trunc hgB hS (.allI (.impI (.impI ?_)))).eqTrans ?_
  · simp only [shift_pairT, shift_fact', show Syn.shift (zero : PTm n) = zero by simp [Syn.shift],
      show Syn.shift (succ M) = succ (Syn.shift M) by simp [Syn.shift]]
    have hv : (le (Syn.shift (succ (succ M))) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (succ (Syn.shift M)) (var 0) := by
      have h0 : (le (Syn.shift (succ (succ M))) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift (succ (succ M))) (var 0) := Prf.hyp0
      have e : Syn.shift (succ (succ M)) = succ (succ (Syn.shift M)) := by simp [Syn.shift]
      rw [e] at h0 ⊢; exact h0
    have z := bv_above hM'.wk.wk hv
    exact (hg_at _ _ _ _ _ _ _ _).eqTrans ((congrMul (congrMul (.eqRefl _) (congrMul z (.eqRefl _))) (.eqRefl _)).eqTrans
      (by ipra_ring))
  · have s1 := sum_shift (Γ := Γ) hgB (succ M) (HP M x A Ds K L)
    have s2 := sum_shift (Γ := Γ) (shiftBody hgB) M (HP M x A Ds K L)
    rw [inst2_shiftBody] at s2
    have z0 : Γ ⊢[PRAAx] inst2 hgB zero (HP M x A Ds K L) ≐ zero :=
      (hg_at _ _ _ _ _ _ _ _).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)
    have z1 : Γ ⊢[PRAAx] inst2 hgB (succ zero) (HP M x A Ds K L) ≐ zero := by
      refine (hg_at _ _ _ _ _ _ _ _).eqTrans (zero_mul_l ?_ _)
      have k1 : Γ ⊢[PRAAx] K * succ zero ≐ K := by ipra_ring
      have u1 : Γ ⊢[PRAAx] U (succ zero) K (fact L) ≐ zero :=
        (congrMonus (congrAp2 (sumF hB) k1 (.eqRefl (fact L))) (.eqRefl _)).eqTrans (le_refl _)
      exact (congrMul (.eqRefl _) (congrMul (.eqRefl _) u1)).eqTrans (by ipra_ring)
    exact s1.eqTrans ((congrAdd z0 (s2.eqTrans ((congrAdd z1 (.eqRefl _)).eqTrans (zero_add _)))).eqTrans (zero_add _))

end Head

/-! ## The exact pointwise identity and the head bound -/

section Main

variable {M x A Ds K L Y : PTm n}

/-- `D · body(j+2) + 2F u g ≤ 2AF · u F⌊x/(j+2)⌋`, from the stage bound at `m = ⌊x/(j+2)⌋`. -/
theorem hd_pt {j : PTm n} (hjM : Γ ⊢[PRAAx] lt j M)
    (hs : Γ ⊢[PRAAx] le (Ds * absd (Psi wt (quo x (succ (succ j))) (pairT K (fact L)))
        (fact L * quo x (succ (succ j)))) (A * (fact L * quo x (succ (succ j))))) :
    Γ ⊢[PRAAx] le (Ds * inst2 wbB (succ (succ j)) (pairT x (pairT K (fact L))) +
        two * fact L * inst2 hgB (succ (succ j)) (HP M x A Ds K L))
      (two * (A * fact L) * inst2 mtB j (pairT x (pairT K (fact L)))) := by
  have b := natEq (body_at (Γ := Γ) j x K L)
  have m := natEq (mt_at (Γ := Γ) j x K L)
  have hb1 : Γ ⊢[PRAAx] lt zero (succ (succ j)) := (succ_monus_succ _ _).eqTrans (zero_le _)
  have hb2 : Γ ⊢[PRAAx] le (succ (succ j)) (succ M) := (succ_monus_succ _ _).eqTrans hjM
  have hv : Γ ⊢[PRAAx] inst2 hgB (succ (succ j)) (HP M x A Ds K L) ≐
      U (succ (succ j)) K (fact L) *
        dg A Ds (Psi wt (quo x (succ (succ j))) (pairT K (fact L))) (fact L * quo x (succ (succ j))) :=
    (hg_at _ _ _ _ _ _ _ _).eqTrans ((congrMul (congrMul (sg_succ _) (congrMul (bv_in hb1 hb2) (.eqRefl _)))
      (.eqRefl _)).eqTrans (by ipra_ring))
  have h := natEq hv
  have eg := natEq (eq_add_of_le hs)
  ipra_le 0 with 2 * 𝔞 A * 𝔞 (fact L) * m - 𝔞 Ds * b - 2 * 𝔞 (fact L) * h +
    2 * 𝔞 (fact L) * 𝔞 (U (succ (succ j)) K (fact L)) * eg

/-- The head with its deficit: `D Σ_{d≤N} 2F u_d|R| + 2F Σ_{d≤N} u_d g ≤ A F x (u_N² + 2F²)`, `N = M + 1`. -/
theorem head_deficit (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * succ M) L)
    (hY : Γ ⊢[PRAAx] le (succ M * Y) x) (hMx : Γ ⊢[PRAAx] le (succ M) x) (hst : Γ ⊢[PRAAx] Stage x Y Ds A K L) :
    Γ ⊢[PRAAx] le (Ds * ap2 (sumF wbB) (succ (succ M)) (pairT x (pairT K (fact L))) +
        two * fact L * ap2 (sumF hgB) (succ x) (HP M x A Ds K L))
      (A * (fact L * (x * (U (succ M) K (fact L) * U (succ M) K (fact L) + two * (fact L * fact L))))) := by
  have hY' : (Γ.map Fm.shift) ⊢[PRAAx] le (succ (Syn.shift M) * Syn.shift Y) (Syn.shift x) := by
    simpa [Fm.shift, Syn.shift] using hY.shift
  have p := sum_le_three (Γ := Γ) (shiftBody (shiftBody wbB)) (shiftBody (shiftBody hgB)) mtB Ds (two * fact L)
    (two * (A * fact L)) (pairT x (pairT K (fact L))) (HP M x A Ds K L) (pairT x (pairT K (fact L))) M
    (.allI (.impI (by
      simp only [shift_pairT, shift_fact', inst2_shiftBody,
        show Syn.shift (zero : PTm n) = zero by simp [Syn.shift],
        show Syn.shift (succ M) = succ (Syn.shift M) by simp [Syn.shift]]
      rw [show Syn.shift (two * (A * fact L)) = two * (Syn.shift A * fact (Syn.shift L)) by simp [Syn.shift],
        show Syn.shift (two * fact L) = two * fact (Syn.shift L) by simp [Syn.shift]]
      have hv : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift M) := Prf.hyp0
      have a := Prf.allE (quo (Syn.shift x) (succ (succ (var 0)))) hst.shift
      simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, PTm.subst_mul, PTm.subst_add, PTm.subst_monus,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.up_zero, Syn.inst_zero,
        subst_up_shift_pal, Syn.subst_inst_shift] at a
      have h1 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
          lt (quo (Syn.shift x) (succ (succ (var 0)))) (succ (Syn.shift x)) :=
        (succ_monus_succ _ _).eqTrans (LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola.quo_le_self
          (succ (var 0)) (Syn.shift x))
      have hvM : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (succ (var 0))) (succ (Syn.shift M)) :=
        (succ_monus_succ _ _).eqTrans hv
      have hk : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
          succ (succ (var 0)) ≐ succ (pred (succ (succ (var 0)))) := congrSucc (pred_succ _).eqSymm
      have h2 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift Y) (quo (Syn.shift x) (succ (succ (var 0)))) :=
        LeanProofs.IPRA.AnalyticNumberTheory.SumReindex.le_quo_of_mul_le hk
          (le_trans (mul_le_mul_right (Syn.shift Y) hvM) hY'.wk)
      have a' : (Γ.map Fm.shift) ⊢[PRAAx] lt (quo (Syn.shift x) (succ (succ (var 0)))) (succ (Syn.shift x)) ⟶
          (le (Syn.shift Y) (quo (Syn.shift x) (succ (succ (var 0)))) ⟶
            le (Syn.shift Ds * absd (Psi wt (quo (Syn.shift x) (succ (succ (var 0))))
                (pairT (Syn.shift K) (fact (Syn.shift L)))) (fact (Syn.shift L) * quo (Syn.shift x) (succ (succ (var 0)))))
              (Syn.shift A * (fact (Syn.shift L) * quo (Syn.shift x) (succ (succ (var 0)))))) := by
        simpa [Syn.shift] using a
      exact hd_pt hv (Prf.impE (Prf.impE a'.wk h1) h2))))
  have he := natEq (head_eq (Γ := Γ) M x K L)
  have hd := natEq (hd_eq (Γ := Γ) (A := A) (Ds := Ds) (K := K) (L := L) hMx)
  have mt := main_term (Γ := Γ) (x := x) hK hL
  ipra_le sl p + 𝔞 A * 𝔞 (fact L) * sl mt with 𝔞 Ds * he + 2 * 𝔞 (fact L) * hd

end Main

end LeanProofs.IPRA.AnalyticNumberTheory.HeadDeficit

export_ipra AnalyticNumberTheory.HeadDeficit (hgB)
