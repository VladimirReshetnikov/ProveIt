import IPRADerivations.Foundations.IntervalPacking
import IPRADerivations.AnalyticNumberTheory.EulerDomination
import IPRADerivations.Core.Header

/-!
# The intersection of two grid intervals

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K9): "A radius-`r_ℓ`
interval meeting `I` …"; reusable for any overlap estimate between finite unions of grid intervals).

For two half-open grid intervals `I = [lo, hi)` and `J = [lo', hi')`, write
`meet(I, J) = [lo < hi][lo' < hi][lo < hi']` for "the intervals meet" (an empty `I` meets nothing, so
inactive members of a family contribute nothing to overlap sums). Then:

* `pt_meet`: `[c ∈ I][c ∈ J] ≤ meet(I, J) [c ∈ J]` for every cell `c`;
* `meet_bit`: `meet(I, J)` is `0` or `1`;
* `inter_cells`: the cells `c < T` of `I ∩ J` number at most `meet(I, J) · |J|`, `|J| = hi' ∸ lo'`.

`inter_cells` splits on `meet`: when the intervals do not meet every cell term vanishes (`pt_meet`);
when they do, the count is at most the cells of `J` (`IntervalCover.count_le`).
-/

namespace LeanProofs.IPRA.Foundations.IntervalIntersection

open_ipra
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt indB inst3_indB count_le colSum)
open LeanProofs.IPRA.Foundations.IntervalAdditive (cnt_bit)
open LeanProofs.IPRA.Foundations.IntervalPacking (cnt_one sg_one_of_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `meet(I, J) = [lo < hi][lo' < hi][lo < hi']`. -/
abbrev meet (lo hi lo' hi' : PTm n) : PTm n := sg (monus hi lo) * sg (monus hi lo') * sg (monus hi' lo)

theorem congrCnt {lo lo' hi hi' c c' : PTm n} (h1 : Γ ⊢[PRAAx] lo ≐ lo') (h2 : Γ ⊢[PRAAx] hi ≐ hi')
    (h3 : Γ ⊢[PRAAx] c ≐ c') : Γ ⊢[PRAAx] cnt lo hi c ≐ cnt lo' hi' c' :=
  congrMul (congrMonus (.eqRefl _) (congrMonus h1 h3)) (congrSg (congrMonus h2 h3))

theorem cnt_le_one (lo hi c : PTm n) : Γ ⊢[PRAAx] le (cnt lo hi c) one :=
  le_congr (cnt_bit _ _ _) (.eqRefl _) (sg_le_one _)

theorem one_one : Γ ⊢[PRAAx] (one : PTm n) * one ≐ one := by
  apply deriveNat; ipra_simps; try ring

/-- `meet` is a bit. -/
theorem meet_bit (lo hi lo' hi' : PTm n) :
    Γ ⊢[PRAAx] (meet lo hi lo' hi' ≐ zero) ⋎ (meet lo hi lo' hi' ≐ one) := by
  refine .orE (sg_bit (Γ := Γ) (monus hi lo)) ?_ ?_
  · exact .orI₁ ((congrMul (congrMul Prf.hyp0 (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _)))
  · let Δ0 : List (Fm PTm n) := (sg (monus hi lo) ≐ one) :: Γ
    refine .orE (sg_bit (Γ := Δ0) (monus hi lo')) ?_ ?_
    · exact .orI₁ ((congrMul (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans
        ((congrMul (mul_zero _) (.eqRefl _)).eqTrans (zero_mul _)))
    · refine .orE (sg_bit (Γ := (sg (monus hi lo') ≐ one) :: Δ0) (monus hi' lo)) ?_ ?_
      · exact .orI₁ ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
      · exact .orI₂ ((congrMul ((congrMul hyp2 Prf.hyp1).eqTrans one_one) Prf.hyp0).eqTrans one_one)

/-- `[c ∈ I][c ∈ J] ≤ meet(I, J) [c ∈ J]`. -/
theorem pt_meet (lo hi lo' hi' c : PTm n) :
    Γ ⊢[PRAAx] le (cnt lo hi c * cnt lo' hi' c) (meet lo hi lo' hi' * cnt lo' hi' c) := by
  refine .orE (sg_bit (Γ := Γ) (cnt lo hi c)) ?_ ?_
  · have z : ((sg (cnt lo hi c) ≐ zero) :: Γ) ⊢[PRAAx] cnt lo hi c * cnt lo' hi' c ≐ zero :=
      (congrMul ((cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)
    exact le_congr z.eqSymm (.eqRefl _) (zero_le _)
  · let Δ : List (Fm PTm n) := (sg (cnt lo hi c) ≐ one) :: Γ
    have c1 : Δ ⊢[PRAAx] cnt lo hi c ≐ one := (cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0
    refine .orE (sg_bit (Γ := Δ) (cnt lo' hi' c)) ?_ ?_
    · have z : ((sg (cnt lo' hi' c) ≐ zero) :: Δ) ⊢[PRAAx] cnt lo hi c * cnt lo' hi' c ≐ zero :=
        (congrMul (.eqRefl _) ((cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0)).eqTrans (mul_zero _)
      exact le_congr z.eqSymm (.eqRefl _) (zero_le _)
    · let Δ' : List (Fm PTm n) := (sg (cnt lo' hi' c) ≐ one) :: Δ
      have c2 : Δ' ⊢[PRAAx] cnt lo' hi' c ≐ one := (cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0
      have c1' : Δ' ⊢[PRAAx] cnt lo hi c ≐ one := c1.wk
      have f1 := cnt_one c1'
      have f2 := cnt_one c2
      have l1 : Δ' ⊢[PRAAx] le lo' c := Prf.andE₁ f2
      have l2 : Δ' ⊢[PRAAx] lt c hi := Prf.andE₂ f1
      have l3 : Δ' ⊢[PRAAx] le lo c := Prf.andE₁ f1
      have l4 : Δ' ⊢[PRAAx] lt c hi' := Prf.andE₂ f2
      have g1 : Δ' ⊢[PRAAx] lt lo' hi := by ipra_le sl l1 + sl l2
      have g2 : Δ' ⊢[PRAAx] lt lo hi' := by ipra_le sl l3 + sl l4
      have g0 : Δ' ⊢[PRAAx] lt lo hi := by ipra_le sl l3 + sl l2
      have eL : Δ' ⊢[PRAAx] cnt lo hi c * cnt lo' hi' c ≐ one := (congrMul c1' c2).eqTrans one_one
      have eR : Δ' ⊢[PRAAx] meet lo hi lo' hi' * cnt lo' hi' c ≐ one :=
        (congrMul ((congrMul ((congrMul (sg_one_of_lt g0) (sg_one_of_lt g1)).eqTrans one_one)
          (sg_one_of_lt g2)).eqTrans one_one) c2).eqTrans one_one
      exact le_congr eL.eqSymm eR.eqSymm (le_refl _)

/-! ## Counting the cells -/

/-- `[c ∈ I][c ∈ J]` over `0 = c`, `1 = ⟨lo, ⟨hi, ⟨lo', hi'⟩⟩⟩`. -/
def ccB : PTm 2 :=
  cnt (fstT (var 1)) (fstT (sndT (var 1))) (var 0) * cnt (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)

/-- `⟨lo, ⟨hi, ⟨lo', hi'⟩⟩⟩`. -/
abbrev quad (lo hi lo' hi' : PTm n) : PTm n := pairT lo (pairT hi (pairT lo' hi'))

theorem inst2_ccB (c z : PTm n) : inst2 ccB c z =
    cnt (fstT z) (fstT (sndT z)) c * cnt (fstT (sndT (sndT z))) (sndT (sndT (sndT z))) c := by
  simp [ccB, inst2, cnt, Signum.sg]

theorem cc_at (c lo hi lo' hi' : PTm n) :
    Γ ⊢[PRAAx] inst2 ccB c (quad lo hi lo' hi') ≐ cnt lo hi c * cnt lo' hi' c := by
  rw [inst2_ccB]
  have s1 : Γ ⊢[PRAAx] sndT (quad lo hi lo' hi') ≐ pairT hi (pairT lo' hi') := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (quad lo hi lo' hi')) ≐ pairT lo' hi' := (congrSnd s1).eqTrans (snd_pair _ _)
  exact congrMul (congrCnt (fst_pair _ _) ((congrFst s1).eqTrans (fst_pair _ _)) (.eqRefl _))
    (congrCnt ((congrFst s2).eqTrans (fst_pair _ _)) ((congrSnd s2).eqTrans (snd_pair _ _)) (.eqRefl _))

/-- `[c ∈ J]` for `J = [fst y, snd y)`, `y = snd z`, as a column of `IntervalCover.indB`. -/
abbrev jB : PTm 2 := colB (indB (fstT (var 1)) (sndT (var 1)))

theorem jB_at (c j lo' hi' : PTm n) : Γ ⊢[PRAAx] inst2 jB c (pairT j (pairT lo' hi')) ≐ cnt lo' hi' c := by
  rw [inst2_colB, inst3_indB]
  have e1 : inst2 (fstT (var 1) : PTm 2) (fstT (pairT j (pairT lo' hi'))) (sndT (pairT j (pairT lo' hi'))) =
      fstT (sndT (pairT j (pairT lo' hi'))) := by simp [inst2]
  have e2 : inst2 (sndT (var 1) : PTm 2) (fstT (pairT j (pairT lo' hi'))) (sndT (pairT j (pairT lo' hi'))) =
      sndT (sndT (pairT j (pairT lo' hi'))) := by simp [inst2]
  rw [e1, e2]
  exact congrCnt ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
    (.eqRefl _)

/-- The cells `c < T` of `[lo, hi) ∩ [lo', hi')` number at most `meet · (hi' ∸ lo')`. -/
theorem inter_cells (lo hi lo' hi' T : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF ccB) T (quad lo hi lo' hi')) (meet lo hi lo' hi' * monus hi' lo') := by
  have hq : Syn.shift (quad lo hi lo' hi') =
      quad (Syn.shift lo) (Syn.shift hi) (Syn.shift lo') (Syn.shift hi') := by simp [Syn.shift]
  refine .orE (meet_bit lo hi lo' hi') ?_ ?_
  · let Θ : List (Fm PTm n) := (meet lo hi lo' hi' ≐ zero) :: Γ
    have hm : Θ ⊢[PRAAx] meet lo hi lo' hi' ≐ zero := Prf.hyp0
    have hm1 : Θ.map Fm.shift ⊢[PRAAx] meet (Syn.shift lo) (Syn.shift hi) (Syn.shift lo') (Syn.shift hi') ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hm.shift
    have z : Θ ⊢[PRAAx] ap2 (sumF ccB) T (quad lo hi lo' hi') ≐ zero := by
      refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
      rw [hq]
      let Θ' : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift T) :: Θ.map Fm.shift
      have hm2 : Θ' ⊢[PRAAx] meet (Syn.shift lo) (Syn.shift hi) (Syn.shift lo') (Syn.shift hi') ≐ zero := hm1.wk
      have p := pt_meet (Γ := Θ') (Syn.shift lo) (Syn.shift hi) (Syn.shift lo') (Syn.shift hi') (var 0)
      have r0 : Θ' ⊢[PRAAx] meet (Syn.shift lo) (Syn.shift hi) (Syn.shift lo') (Syn.shift hi') *
          cnt (Syn.shift lo') (Syn.shift hi') (var 0) ≐ zero := (congrMul hm2 (.eqRefl _)).eqTrans (zero_mul _)
      exact (cc_at _ _ _ _ _).eqTrans (le_antisymm (le_congr (.eqRefl _) r0 p) (zero_le _))
    exact le_congr z.eqSymm (.eqRefl _) (zero_le _)
  · let Θ : List (Fm PTm n) := (meet lo hi lo' hi' ≐ one) :: Γ
    have s1 : Θ ⊢[PRAAx] le (ap2 (sumF ccB) T (quad lo hi lo' hi')) (ap2 (sumF jB) T (pairT zero (pairT lo' hi'))) := by
      refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
      rw [hq, show Syn.shift (pairT (zero : PTm n) (pairT lo' hi')) = pairT zero (pairT (Syn.shift lo') (Syn.shift hi')) by
        simp [Syn.shift]]
      let Θ' : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift T) :: Θ.map Fm.shift
      have h1 : Θ' ⊢[PRAAx] le (cnt (Syn.shift lo) (Syn.shift hi) (var 0)) one := cnt_le_one _ _ _
      have core : Θ' ⊢[PRAAx] le (cnt (Syn.shift lo) (Syn.shift hi) (var 0) * cnt (Syn.shift lo') (Syn.shift hi') (var 0))
          (cnt (Syn.shift lo') (Syn.shift hi') (var 0)) := by
        ipra_le 𝔞 (cnt (Syn.shift lo') (Syn.shift hi') (var 0)) * sl h1
      exact le_congr (cc_at _ _ _ _ _).eqSymm (jB_at _ _ _ _).eqSymm core
    have s2 := count_le (fstT (var 1) : PTm 2) (sndT (var 1)) (Γ := Θ) T (pairT zero (pairT lo' hi'))
    have e1 : inst2 (sndT (var 1) : PTm 2) (fstT (pairT (zero : PTm n) (pairT lo' hi'))) (sndT (pairT zero (pairT lo' hi'))) =
        sndT (sndT (pairT zero (pairT lo' hi'))) := by simp [inst2]
    have e2 : inst2 (fstT (var 1) : PTm 2) (fstT (pairT (zero : PTm n) (pairT lo' hi'))) (sndT (pairT zero (pairT lo' hi'))) =
        fstT (sndT (pairT zero (pairT lo' hi'))) := by simp [inst2]
    rw [e1, e2] at s2
    have hl : Θ ⊢[PRAAx] monus (sndT (sndT (pairT (zero : PTm n) (pairT lo' hi')))) (fstT (sndT (pairT zero (pairT lo' hi')))) ≐
        meet lo hi lo' hi' * monus hi' lo' :=
      (congrMonus ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans
        ((one_mul _).eqSymm.eqTrans (congrMul Prf.hyp0.eqSymm (.eqRefl _)))
    exact le_trans s1 (le_congr (.eqRefl _) hl s2)

end LeanProofs.IPRA.Foundations.IntervalIntersection
