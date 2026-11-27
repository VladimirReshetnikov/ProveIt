import IPRADerivations.Foundations.IntervalIntersection

/-!
# Overlaps of two finite unions of grid intervals

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K9): "Fix `k < ℓ` and
one interval `I` of `E_k(J)`. A radius-`r_ℓ` interval meeting `I` … Sum this over the disjoint intervals of
`E_k(J)`"; reusable for any second-moment estimate of finite unions).

For two families of grid intervals `I_j = [lo₁(j), hi₁(j))`, `j < K₁`, and `J_{j'} = [lo₂(j'), hi₂(j'))`,
`j' < K₂`, with unions `E₁`, `E₂`:

* `local_le`: for one interval `I = [lo, hi)`, `|I ∩ E₂| ≤ Σ_{j'} meet(I, J_{j'}) |J_{j'}|`;
* `overlap_split`: `|E₁ ∩ E₂| ≤ Σ_j Σ_{j'} meet(I_j, J_{j'}) |J_{j'}|`, as `Σ_j |I_j ∩ E₂|` bounded by
  `local_le`.

Both proofs bound a covering bit by the number of covering members (`IntervalCover.sg_le_self`), pull the
other factor through the sum (`Probability/Independence.sum_scale`), exchange the double sum
(`Core/Fubini`) and finish with `IntervalIntersection.inter_cells`.
-/

namespace LeanProofs.IPRA.Foundations.IntervalOverlap

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt indB inst3_indB covB sg_le_self)
open LeanProofs.IPRA.Foundations.IntervalIntersection (meet congrCnt ccB quad cc_at inter_cells)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (shift_inst2')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## One interval against a family -/

section Fam

variable (lo2 hi2 : PTm 2)

theorem cov_at (c K x : PTm n) :
    Γ ⊢[PRAAx] inst2 (covB lo2 hi2) c (pairT K x) ≐ sg (ap2 (sumF (rowB (indB lo2 hi2))) K (pairT c x)) := by
  rw [show inst2 (covB lo2 hi2) c (pairT K x) = sg (inst2 (oB (indB lo2 hi2)) c (pairT K x)) by
    simp [covB, inst2, Signum.sg]]
  exact congrSg (oB_at _ _ _ _)

theorem rowI_at (j c x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (indB lo2 hi2)) j (pairT c x) ≐ cnt (inst2 lo2 j x) (inst2 hi2 j x) c := by
  rw [inst2_rowB, inst3_indB]
  exact congrCnt (congrInst2 lo2 (.eqRefl _) (snd_pair _ _)) (congrInst2 hi2 (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)

/-- `[lo ≤ c < hi][lo₂(j) ≤ c < hi₂(j)]` over `0 = c`, `1 = j`, `2 = ⟨lo, ⟨hi, x₂⟩⟩`. -/
def bB : PTm 3 :=
  cnt (fstT (var 2)) (fstT (sndT (var 2))) (var 0) * Syn.subst ![var 0, var 1, sndT (sndT (var 2))] (indB lo2 hi2)

theorem inst3_bB (c j w : PTm n) : inst3 (bB lo2 hi2) c j w =
    cnt (fstT w) (fstT (sndT w)) c * cnt (inst2 lo2 j (sndT (sndT w))) (inst2 hi2 j (sndT (sndT w))) c := by
  have e : Syn.subst ![c, j, w] (Syn.subst ![var 0, var 1, sndT (sndT (var 2))] (indB lo2 hi2)) =
      inst3 (indB lo2 hi2) c j (sndT (sndT w)) := by
    simp only [inst3, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have e2 : inst3 (bB lo2 hi2) c j w = Syn.subst ![c, j, w] (cnt (fstT (var 2)) (fstT (sndT (var 2))) (var 0)) *
      Syn.subst ![c, j, w] (Syn.subst ![var 0, var 1, sndT (sndT (var 2))] (indB lo2 hi2)) := by
    simp only [bB, inst3, PTm.subst_mul]
  rw [e2, e, inst3_indB]
  simp [cnt, Signum.sg]

/-- `[lo ≤ c < hi] · cov₂(c)` over `0 = c`, `1 = ⟨lo, ⟨hi, ⟨K₂, x₂⟩⟩⟩`. -/
def lcB : PTm 2 :=
  cnt (fstT (var 1)) (fstT (sndT (var 1))) (var 0) * Syn.subst ![var 0, sndT (sndT (var 1))] (covB lo2 hi2)

theorem inst2_lcB (c z : PTm n) : inst2 (lcB lo2 hi2) c z =
    cnt (fstT z) (fstT (sndT z)) c * inst2 (covB lo2 hi2) c (sndT (sndT z)) := by
  have e : Syn.subst ![c, z] (Syn.subst ![var 0, sndT (sndT (var 1))] (covB lo2 hi2)) =
      inst2 (covB lo2 hi2) c (sndT (sndT z)) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have e2 : inst2 (lcB lo2 hi2) c z = Syn.subst ![c, z] (cnt (fstT (var 1)) (fstT (sndT (var 1))) (var 0)) *
      Syn.subst ![c, z] (Syn.subst ![var 0, sndT (sndT (var 1))] (covB lo2 hi2)) := by
    simp only [lcB, inst2, PTm.subst_mul]
  rw [e2, e]
  simp [cnt, Signum.sg]

/-- `meet(I, J_j) |J_j|` over `0 = j`, `1 = ⟨lo, ⟨hi, x₂⟩⟩`. -/
def mtB : PTm 2 :=
  meet (fstT (var 1)) (fstT (sndT (var 1))) (Syn.subst ![var 0, sndT (sndT (var 1))] lo2)
      (Syn.subst ![var 0, sndT (sndT (var 1))] hi2) *
    monus (Syn.subst ![var 0, sndT (sndT (var 1))] hi2) (Syn.subst ![var 0, sndT (sndT (var 1))] lo2)

theorem sub_ss (f : PTm 2) (j w : PTm n) :
    Syn.subst ![j, w] (Syn.subst ![var 0, sndT (sndT (var 1))] f) = inst2 f j (sndT (sndT w)) := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem inst2_mtB (j w : PTm n) : inst2 (mtB lo2 hi2) j w =
    meet (fstT w) (fstT (sndT w)) (inst2 lo2 j (sndT (sndT w))) (inst2 hi2 j (sndT (sndT w))) *
      monus (inst2 hi2 j (sndT (sndT w))) (inst2 lo2 j (sndT (sndT w))) := by
  simp only [mtB, inst2, PTm.subst_mul, PTm.subst_monus, Signum.sg]
  rw [show Syn.subst ![j, w] (Syn.subst ![var 0, sndT (sndT (var 1))] lo2) = Syn.subst ![j, sndT (sndT w)] lo2 from
      sub_ss lo2 j w,
    show Syn.subst ![j, w] (Syn.subst ![var 0, sndT (sndT (var 1))] hi2) = Syn.subst ![j, sndT (sndT w)] hi2 from
      sub_ss hi2 j w]
  simp

theorem row_b_at (j c lo hi x2 : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (bB lo2 hi2)) j (pairT c (pairT lo (pairT hi x2))) ≐
      cnt lo hi c * cnt (inst2 lo2 j x2) (inst2 hi2 j x2) c := by
  rw [inst2_rowB, inst3_bB]
  have hW : Γ ⊢[PRAAx] sndT (pairT c (pairT lo (pairT hi x2))) ≐ pairT lo (pairT hi x2) := snd_pair _ _
  have hc : Γ ⊢[PRAAx] fstT (pairT c (pairT lo (pairT hi x2))) ≐ c := fst_pair _ _
  have hlo : Γ ⊢[PRAAx] fstT (sndT (pairT c (pairT lo (pairT hi x2)))) ≐ lo := (congrFst hW).eqTrans (fst_pair _ _)
  have h2 : Γ ⊢[PRAAx] sndT (sndT (pairT c (pairT lo (pairT hi x2)))) ≐ pairT hi x2 := (congrSnd hW).eqTrans (snd_pair _ _)
  have hhi : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT c (pairT lo (pairT hi x2))))) ≐ hi := (congrFst h2).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (sndT (pairT c (pairT lo (pairT hi x2))))) ≐ x2 := (congrSnd h2).eqTrans (snd_pair _ _)
  exact congrMul (congrCnt hlo hhi hc) (congrCnt (congrInst2 lo2 (.eqRefl _) hx) (congrInst2 hi2 (.eqRefl _) hx) hc)

theorem col_b_at (c j lo hi x2 : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (bB lo2 hi2)) c (pairT j (pairT lo (pairT hi x2))) ≐
      inst2 ccB c (quad lo hi (inst2 lo2 j x2) (inst2 hi2 j x2)) := by
  rw [inst2_colB, inst3_bB]
  have hW : Γ ⊢[PRAAx] sndT (pairT j (pairT lo (pairT hi x2))) ≐ pairT lo (pairT hi x2) := snd_pair _ _
  have hj : Γ ⊢[PRAAx] fstT (pairT j (pairT lo (pairT hi x2))) ≐ j := fst_pair _ _
  have hlo : Γ ⊢[PRAAx] fstT (sndT (pairT j (pairT lo (pairT hi x2)))) ≐ lo := (congrFst hW).eqTrans (fst_pair _ _)
  have h2 : Γ ⊢[PRAAx] sndT (sndT (pairT j (pairT lo (pairT hi x2)))) ≐ pairT hi x2 := (congrSnd hW).eqTrans (snd_pair _ _)
  have hhi : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT j (pairT lo (pairT hi x2))))) ≐ hi := (congrFst h2).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (sndT (pairT j (pairT lo (pairT hi x2))))) ≐ x2 := (congrSnd h2).eqTrans (snd_pair _ _)
  exact (congrMul (congrCnt hlo hhi (.eqRefl _))
    (congrCnt (congrInst2 lo2 hj hx) (congrInst2 hi2 hj hx) (.eqRefl _))).eqTrans (cc_at _ _ _ _ _).eqSymm

theorem mt_at (j lo hi x2 : PTm n) :
    Γ ⊢[PRAAx] inst2 (mtB lo2 hi2) j (pairT lo (pairT hi x2)) ≐
      meet lo hi (inst2 lo2 j x2) (inst2 hi2 j x2) * monus (inst2 hi2 j x2) (inst2 lo2 j x2) := by
  rw [inst2_mtB]
  have hW : Γ ⊢[PRAAx] sndT (pairT lo (pairT hi x2)) ≐ pairT hi x2 := snd_pair _ _
  have hlo : Γ ⊢[PRAAx] fstT (pairT lo (pairT hi x2)) ≐ lo := fst_pair _ _
  have hhi : Γ ⊢[PRAAx] fstT (sndT (pairT lo (pairT hi x2))) ≐ hi := (congrFst hW).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT lo (pairT hi x2))) ≐ x2 := (congrSnd hW).eqTrans (snd_pair _ _)
  have el := congrInst2 lo2 (.eqRefl j) hx
  have eh := congrInst2 hi2 (.eqRefl j) hx
  exact congrMul (congrMul (congrMul (congrSg (congrMonus hhi hlo)) (congrSg (congrMonus hhi el)))
    (congrSg (congrMonus eh hlo))) (congrMonus eh el)

/-- The covering bit of `E₂` is at most the number of covering members, times `[c ∈ I]`. -/
theorem pt1 (c lo hi K2 x2 : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (lcB lo2 hi2) c (pairT lo (pairT hi (pairT K2 x2))))
      (inst2 (oB (bB lo2 hi2)) c (pairT K2 (pairT lo (pairT hi x2)))) := by
  rw [inst2_lcB]
  have s1 : Γ ⊢[PRAAx] sndT (pairT lo (pairT hi (pairT K2 x2))) ≐ pairT hi (pairT K2 x2) := snd_pair _ _
  have hlo : Γ ⊢[PRAAx] fstT (pairT lo (pairT hi (pairT K2 x2))) ≐ lo := fst_pair _ _
  have hhi : Γ ⊢[PRAAx] fstT (sndT (pairT lo (pairT hi (pairT K2 x2)))) ≐ hi := (congrFst s1).eqTrans (fst_pair _ _)
  have hy : Γ ⊢[PRAAx] sndT (sndT (pairT lo (pairT hi (pairT K2 x2)))) ≐ pairT K2 x2 :=
    (congrSnd s1).eqTrans (snd_pair _ _)
  have eL : Γ ⊢[PRAAx] cnt (fstT (pairT lo (pairT hi (pairT K2 x2)))) (fstT (sndT (pairT lo (pairT hi (pairT K2 x2))))) c *
      inst2 (covB lo2 hi2) c (sndT (sndT (pairT lo (pairT hi (pairT K2 x2))))) ≐
      cnt lo hi c * sg (ap2 (sumF (rowB (indB lo2 hi2))) K2 (pairT c x2)) :=
    congrMul (congrCnt hlo hhi (.eqRefl _)) ((congrInst2 (covB lo2 hi2) (.eqRefl _) hy).eqTrans (cov_at lo2 hi2 c K2 x2))
  have eR : Γ ⊢[PRAAx] inst2 (oB (bB lo2 hi2)) c (pairT K2 (pairT lo (pairT hi x2))) ≐
      cnt lo hi c * ap2 (sumF (rowB (indB lo2 hi2))) K2 (pairT c x2) := by
    refine (oB_at _ _ _ _).eqTrans ?_
    refine sum_scale (rowB (bB lo2 hi2)) (rowB (indB lo2 hi2)) K2 (cnt lo hi c) (pairT c x2)
      (pairT c (pairT lo (pairT hi x2))) (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [show Syn.shift (cnt lo hi c) = cnt (Syn.shift lo) (Syn.shift hi) (Syn.shift c) by simp [Syn.shift]]
    exact (row_b_at lo2 hi2 _ _ _ _ _).eqTrans (congrMul (.eqRefl _) (rowI_at lo2 hi2 _ _ _).eqSymm)
  have h := sg_le_self (Γ := Γ) (ap2 (sumF (rowB (indB lo2 hi2))) K2 (pairT c x2))
  have core : Γ ⊢[PRAAx] le (cnt lo hi c * sg (ap2 (sumF (rowB (indB lo2 hi2))) K2 (pairT c x2)))
      (cnt lo hi c * ap2 (sumF (rowB (indB lo2 hi2))) K2 (pairT c x2)) := by
    ipra_le 𝔞 (cnt lo hi c) * sl h
  exact le_congr eL.eqSymm eR.eqSymm core

/-- One column of the exchanged double sum is an intersection count. -/
theorem pt3 (j T lo hi x2 : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (pB (bB lo2 hi2)) j (pairT T (pairT lo (pairT hi x2))))
      (inst2 (mtB lo2 hi2) j (pairT lo (pairT hi x2))) := by
  rw [inst2_pB]
  refine le_congr ?_ (mt_at lo2 hi2 j lo hi x2).eqSymm (inter_cells lo hi (inst2 lo2 j x2) (inst2 hi2 j x2) T)
  refine .eqTrans ?_ (congrAp2 (sumF (colB (bB lo2 hi2))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [quad, shift_pairT, shift_inst2']
  exact (col_b_at lo2 hi2 _ _ _ _ _).eqSymm

/-- `|I ∩ E₂| ≤ Σ_{j'<K₂} meet(I, J_{j'}) |J_{j'}|` for `I = [lo, hi)`. -/
theorem local_le (lo hi T K2 x2 : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (lcB lo2 hi2)) T (pairT lo (pairT hi (pairT K2 x2))))
      (ap2 (sumF (mtB lo2 hi2)) K2 (pairT lo (pairT hi x2))) := by
  have s1 : Γ ⊢[PRAAx] le (ap2 (sumF (lcB lo2 hi2)) T (pairT lo (pairT hi (pairT K2 x2))))
      (ap2 (sumF (oB (bB lo2 hi2))) T (pairT K2 (pairT lo (pairT hi x2)))) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact pt1 lo2 hi2 _ _ _ _ _
  have s2 := fubini (Γ := Γ) (bB lo2 hi2) T K2 (pairT lo (pairT hi x2))
  have s3 : Γ ⊢[PRAAx] le (ap2 (sumF (pB (bB lo2 hi2))) K2 (pairT T (pairT lo (pairT hi x2))))
      (ap2 (sumF (mtB lo2 hi2)) K2 (pairT lo (pairT hi x2))) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact pt3 lo2 hi2 _ _ _ _ _
  exact le_trans s1 (le_congr s2.eqSymm (.eqRefl _) s3)

end Fam

/-! ## Two families -/

section Two

variable (lo1 hi1 lo2 hi2 : PTm 2)

/-- `cov₁(c) cov₂(c)` over `0 = c`, `1 = ⟨⟨K₁, x₁⟩, ⟨K₂, x₂⟩⟩`. -/
def ovB : PTm 2 := Syn.subst ![var 0, fstT (var 1)] (covB lo1 hi1) * Syn.subst ![var 0, sndT (var 1)] (covB lo2 hi2)

/-- `|E₁ ∩ E₂|`: the cells `c < T` covered by both families. -/
def inter (T K1 x1 K2 x2 : PTm n) : PTm n :=
  ap2 (sumF (ovB lo1 hi1 lo2 hi2)) T (pairT (pairT K1 x1) (pairT K2 x2))

theorem sub_f (f : PTm 2) (c z : PTm n) : Syn.subst ![c, z] (Syn.subst ![var 0, fstT (var 1)] f) = inst2 f c (fstT z) := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem sub_s (f : PTm 2) (c z : PTm n) : Syn.subst ![c, z] (Syn.subst ![var 0, sndT (var 1)] f) = inst2 f c (sndT z) := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

theorem inst2_ovB (c z : PTm n) :
    inst2 (ovB lo1 hi1 lo2 hi2) c z = inst2 (covB lo1 hi1) c (fstT z) * inst2 (covB lo2 hi2) c (sndT z) := by
  have e2 : inst2 (ovB lo1 hi1 lo2 hi2) c z = Syn.subst ![c, z] (Syn.subst ![var 0, fstT (var 1)] (covB lo1 hi1)) *
      Syn.subst ![c, z] (Syn.subst ![var 0, sndT (var 1)] (covB lo2 hi2)) := by
    simp only [ovB, inst2, PTm.subst_mul]
  rw [e2, sub_f, sub_s]

/-- `[lo₁(j) ≤ c < hi₁(j)] cov₂(c)` over `0 = c`, `1 = j`, `2 = ⟨x₁, ⟨K₂, x₂⟩⟩`. -/
def aB : PTm 3 :=
  Syn.subst ![var 0, sndT (var 2)] (covB lo2 hi2) *
    cnt (Syn.subst ![var 1, fstT (var 2)] lo1) (Syn.subst ![var 1, fstT (var 2)] hi1) (var 0)

theorem inst3_aB (c j z : PTm n) : inst3 (aB lo1 hi1 lo2 hi2) c j z =
    inst2 (covB lo2 hi2) c (sndT z) * cnt (inst2 lo1 j (fstT z)) (inst2 hi1 j (fstT z)) c := by
  have e1 : Syn.subst ![c, j, z] (Syn.subst ![var 0, sndT (var 2)] (covB lo2 hi2)) = inst2 (covB lo2 hi2) c (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have e3 : ∀ f : PTm 2, Syn.subst ![c, j, z] (Syn.subst ![var 1, fstT (var 2)] f) = inst2 f j (fstT z) := fun f => by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [aB, inst3, PTm.subst_mul, PTm.subst_monus, Signum.sg]
  rw [e1, e3, e3]
  simp

/-- `Σ_{j'<K₂} meet(I_j, J_{j'}) |J_{j'}|` over `0 = j`, `1 = ⟨K₂, ⟨x₁, x₂⟩⟩`. -/
def locB : PTm 2 :=
  ap2 (sumF (mtB lo2 hi2)) (fstT (var 1))
    (pairT (Syn.subst ![var 0, fstT (sndT (var 1))] lo1)
      (pairT (Syn.subst ![var 0, fstT (sndT (var 1))] hi1) (sndT (sndT (var 1)))))

theorem inst2_locB (j z : PTm n) : inst2 (locB lo1 hi1 lo2 hi2) j z =
    ap2 (sumF (mtB lo2 hi2)) (fstT z)
      (pairT (inst2 lo1 j (fstT (sndT z))) (pairT (inst2 hi1 j (fstT (sndT z))) (sndT (sndT z)))) := by
  have e : ∀ f : PTm 2, Syn.subst ![j, z] (Syn.subst ![var 0, fstT (sndT (var 1))] f) = inst2 f j (fstT (sndT z)) :=
    fun f => by simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [locB, inst2, subst_ap2, subst_pairT, subst_fstT, subst_sndT]
  rw [show Syn.subst ![j, z] (Syn.subst ![var 0, fstT (sndT (var 1))] lo1) = Syn.subst ![j, fstT (sndT z)] lo1 from e lo1,
    show Syn.subst ![j, z] (Syn.subst ![var 0, fstT (sndT (var 1))] hi1) = Syn.subst ![j, fstT (sndT z)] hi1 from e hi1]
  simp

theorem row_a_at (j c x1 K2 x2 : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (aB lo1 hi1 lo2 hi2)) j (pairT c (pairT x1 (pairT K2 x2))) ≐
      inst2 (covB lo2 hi2) c (pairT K2 x2) * inst2 (rowB (indB lo1 hi1)) j (pairT c x1) := by
  rw [inst2_rowB, inst3_aB]
  have hz : Γ ⊢[PRAAx] sndT (pairT c (pairT x1 (pairT K2 x2))) ≐ pairT x1 (pairT K2 x2) := snd_pair _ _
  have hc : Γ ⊢[PRAAx] fstT (pairT c (pairT x1 (pairT K2 x2))) ≐ c := fst_pair _ _
  have hy : Γ ⊢[PRAAx] sndT (sndT (pairT c (pairT x1 (pairT K2 x2)))) ≐ pairT K2 x2 := (congrSnd hz).eqTrans (snd_pair _ _)
  have hx : Γ ⊢[PRAAx] fstT (sndT (pairT c (pairT x1 (pairT K2 x2)))) ≐ x1 := (congrFst hz).eqTrans (fst_pair _ _)
  exact congrMul (congrInst2 (covB lo2 hi2) hc hy)
    ((congrCnt (congrInst2 lo1 (.eqRefl _) hx) (congrInst2 hi1 (.eqRefl _) hx) hc).eqTrans
      (rowI_at lo1 hi1 _ _ _).eqSymm)

theorem col_a_at (c j x1 K2 x2 : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (aB lo1 hi1 lo2 hi2)) c (pairT j (pairT x1 (pairT K2 x2))) ≐
      inst2 (lcB lo2 hi2) c (pairT (inst2 lo1 j x1) (pairT (inst2 hi1 j x1) (pairT K2 x2))) := by
  rw [inst2_colB, inst3_aB, inst2_lcB]
  have hz : Γ ⊢[PRAAx] sndT (pairT j (pairT x1 (pairT K2 x2))) ≐ pairT x1 (pairT K2 x2) := snd_pair _ _
  have hj : Γ ⊢[PRAAx] fstT (pairT j (pairT x1 (pairT K2 x2))) ≐ j := fst_pair _ _
  have hy : Γ ⊢[PRAAx] sndT (sndT (pairT j (pairT x1 (pairT K2 x2)))) ≐ pairT K2 x2 := (congrSnd hz).eqTrans (snd_pair _ _)
  have hx : Γ ⊢[PRAAx] fstT (sndT (pairT j (pairT x1 (pairT K2 x2)))) ≐ x1 := (congrFst hz).eqTrans (fst_pair _ _)
  have q1 : Γ ⊢[PRAAx] sndT (pairT (inst2 lo1 j x1) (pairT (inst2 hi1 j x1) (pairT K2 x2))) ≐
      pairT (inst2 hi1 j x1) (pairT K2 x2) := snd_pair _ _
  have qlo : Γ ⊢[PRAAx] fstT (pairT (inst2 lo1 j x1) (pairT (inst2 hi1 j x1) (pairT K2 x2))) ≐ inst2 lo1 j x1 :=
    fst_pair _ _
  have qhi : Γ ⊢[PRAAx] fstT (sndT (pairT (inst2 lo1 j x1) (pairT (inst2 hi1 j x1) (pairT K2 x2)))) ≐ inst2 hi1 j x1 :=
    (congrFst q1).eqTrans (fst_pair _ _)
  have qy : Γ ⊢[PRAAx] sndT (sndT (pairT (inst2 lo1 j x1) (pairT (inst2 hi1 j x1) (pairT K2 x2)))) ≐ pairT K2 x2 :=
    (congrSnd q1).eqTrans (snd_pair _ _)
  refine (mul_comm _ _).eqTrans ?_
  exact congrMul (congrCnt ((congrInst2 lo1 hj hx).eqTrans qlo.eqSymm) ((congrInst2 hi1 hj hx).eqTrans qhi.eqSymm)
    (.eqRefl _)) (congrInst2 (covB lo2 hi2) (.eqRefl _) (hy.eqTrans qy.eqSymm))

/-- A doubly covered cell is counted by the members of `E₁` covering it. -/
theorem q1 (c K1 x1 K2 x2 : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (ovB lo1 hi1 lo2 hi2) c (pairT (pairT K1 x1) (pairT K2 x2)))
      (inst2 (oB (aB lo1 hi1 lo2 hi2)) c (pairT K1 (pairT x1 (pairT K2 x2)))) := by
  rw [inst2_ovB]
  have eL : Γ ⊢[PRAAx] inst2 (covB lo1 hi1) c (fstT (pairT (pairT K1 x1) (pairT K2 x2))) *
      inst2 (covB lo2 hi2) c (sndT (pairT (pairT K1 x1) (pairT K2 x2))) ≐
      sg (ap2 (sumF (rowB (indB lo1 hi1))) K1 (pairT c x1)) * inst2 (covB lo2 hi2) c (pairT K2 x2) :=
    congrMul ((congrInst2 (covB lo1 hi1) (.eqRefl _) (fst_pair _ _)).eqTrans (cov_at lo1 hi1 c K1 x1))
      (congrInst2 (covB lo2 hi2) (.eqRefl _) (snd_pair _ _))
  have eR : Γ ⊢[PRAAx] inst2 (oB (aB lo1 hi1 lo2 hi2)) c (pairT K1 (pairT x1 (pairT K2 x2))) ≐
      inst2 (covB lo2 hi2) c (pairT K2 x2) * ap2 (sumF (rowB (indB lo1 hi1))) K1 (pairT c x1) := by
    refine (oB_at _ _ _ _).eqTrans ?_
    refine sum_scale (rowB (aB lo1 hi1 lo2 hi2)) (rowB (indB lo1 hi1)) K1 (inst2 (covB lo2 hi2) c (pairT K2 x2))
      (pairT c x1) (pairT c (pairT x1 (pairT K2 x2))) (.allI (.impI ?_))
    simp only [shift_pairT, shift_inst2']
    exact row_a_at lo1 hi1 lo2 hi2 _ _ _ _ _
  have h := sg_le_self (Γ := Γ) (ap2 (sumF (rowB (indB lo1 hi1))) K1 (pairT c x1))
  have core : Γ ⊢[PRAAx] le (sg (ap2 (sumF (rowB (indB lo1 hi1))) K1 (pairT c x1)) * inst2 (covB lo2 hi2) c (pairT K2 x2))
      (inst2 (covB lo2 hi2) c (pairT K2 x2) * ap2 (sumF (rowB (indB lo1 hi1))) K1 (pairT c x1)) := by
    ipra_le 𝔞 (inst2 (covB lo2 hi2) c (pairT K2 x2)) * sl h
  exact le_congr eL.eqSymm eR.eqSymm core

/-- One member of `E₁` against `E₂`. -/
theorem q3 (j T x1 K2 x2 : PTm n) :
    Γ ⊢[PRAAx] le (inst2 (pB (aB lo1 hi1 lo2 hi2)) j (pairT T (pairT x1 (pairT K2 x2))))
      (inst2 (locB lo1 hi1 lo2 hi2) j (pairT K2 (pairT x1 x2))) := by
  rw [inst2_pB, inst2_locB]
  have hz : Γ ⊢[PRAAx] sndT (pairT K2 (pairT x1 x2)) ≐ pairT x1 x2 := snd_pair _ _
  have hK : Γ ⊢[PRAAx] fstT (pairT K2 (pairT x1 x2)) ≐ K2 := fst_pair _ _
  have hx1 : Γ ⊢[PRAAx] fstT (sndT (pairT K2 (pairT x1 x2))) ≐ x1 := (congrFst hz).eqTrans (fst_pair _ _)
  have hx2 : Γ ⊢[PRAAx] sndT (sndT (pairT K2 (pairT x1 x2))) ≐ x2 := (congrSnd hz).eqTrans (snd_pair _ _)
  have eR : Γ ⊢[PRAAx] ap2 (sumF (mtB lo2 hi2)) K2 (pairT (inst2 lo1 j x1) (pairT (inst2 hi1 j x1) x2)) ≐
      ap2 (sumF (mtB lo2 hi2)) (fstT (pairT K2 (pairT x1 x2)))
        (pairT (inst2 lo1 j (fstT (sndT (pairT K2 (pairT x1 x2)))))
          (pairT (inst2 hi1 j (fstT (sndT (pairT K2 (pairT x1 x2))))) (sndT (sndT (pairT K2 (pairT x1 x2)))))) :=
    (congrAp2 (sumF (mtB lo2 hi2)) hK (congrPairT (congrInst2 lo1 (.eqRefl _) hx1)
      (congrPairT (congrInst2 hi1 (.eqRefl _) hx1) hx2))).eqSymm
  refine le_congr ?_ eR (local_le lo2 hi2 (inst2 lo1 j x1) (inst2 hi1 j x1) T K2 x2)
  refine .eqTrans ?_ (congrAp2 (sumF (colB (aB lo1 hi1 lo2 hi2))) (fst_pair _ _)
    (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_inst2']
  exact (col_a_at lo1 hi1 lo2 hi2 _ _ _ _ _).eqSymm

/-- `|E₁ ∩ E₂| ≤ Σ_{j<K₁} Σ_{j'<K₂} meet(I_j, J_{j'}) |J_{j'}|`. -/
theorem overlap_split (T K1 x1 K2 x2 : PTm n) :
    Γ ⊢[PRAAx] le (inter lo1 hi1 lo2 hi2 T K1 x1 K2 x2) (ap2 (sumF (locB lo1 hi1 lo2 hi2)) K1 (pairT K2 (pairT x1 x2))) := by
  have s1 : Γ ⊢[PRAAx] le (inter lo1 hi1 lo2 hi2 T K1 x1 K2 x2)
      (ap2 (sumF (oB (aB lo1 hi1 lo2 hi2))) T (pairT K1 (pairT x1 (pairT K2 x2)))) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact q1 lo1 hi1 lo2 hi2 _ _ _ _ _
  have s2 := fubini (Γ := Γ) (aB lo1 hi1 lo2 hi2) T K1 (pairT x1 (pairT K2 x2))
  have s3 : Γ ⊢[PRAAx] le (ap2 (sumF (pB (aB lo1 hi1 lo2 hi2))) K1 (pairT T (pairT x1 (pairT K2 x2))))
      (ap2 (sumF (locB lo1 hi1 lo2 hi2)) K1 (pairT K2 (pairT x1 x2))) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    exact q3 lo1 hi1 lo2 hi2 _ _ _ _ _
  exact le_trans s1 (le_congr s2.eqSymm (.eqRefl _) s3)

end Two

end LeanProofs.IPRA.Foundations.IntervalOverlap
