import IPRADerivations.Foundations.IntervalAdditive

/-!
# Packings of separated equal intervals

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K8): "let `E_k(J)` be
the union of the intervals of radius `r_k` centered at the fractions in `𝓡_k(J)` … They are pairwise
disjoint at each fixed scale, by the separation just proved").

On the grid of `Foundations/IntervalCover`, the members `j < K` of a family are the intervals
`[A_j, A_j + [act_j] w)` (empty when `act_j = 0`). If the active members are `w`-separated — no pair
`j' < j` of active members has `A_{j'} < A_j + w` and `A_j < A_{j'} + w` — and all lie inside the grid,
the union has length `w · #{j : act_j}` (`packing`):

  `measure = w Σ_{j<K} [act_j]`.

The hypotheses are closed equations (`hT`: `Σ_j (A_j + [act_j] w ∸ T) = 0`; `hS`: the separation sum
vanishes). The cell-overlap hypothesis of `IntervalAdditive.additive` follows pointwise (`pt_zero`): a cell
in two members forces both to be active and within `w` of each other.
-/

namespace LeanProofs.IPRA.Foundations.IntervalPacking

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt measure lenB)
open LeanProofs.IPRA.Foundations.IntervalAdditive (prB inst2_prB rwB inst2_rwB ajB inst2_ajB ovlB inst2_ovlB
  outB inst2_outB cnt_bit additive sg_one_eq)
open LeanProofs.IPRA.Foundations.InjectionCount (term_zero)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Bits -/

theorem absurd_one_zero' {φ : Fm PTm n} (h : Γ ⊢[PRAAx] one ≐ zero) : Γ ⊢[PRAAx] φ := .botE _ (succ_ne_zero h)

/-- `sg t = 1` gives `t ≥ 1`. -/
theorem pos_of_sg_one {t : PTm n} (h : Γ ⊢[PRAAx] sg t ≐ one) : Γ ⊢[PRAAx] le one t := by
  refine .orE (zero_or_succ t) ?_ ?_
  · exact absurd_one_zero' (h.wk.eqSymm.eqTrans ((congrSg Prf.hyp0).eqTrans sg_zero))
  · have e := natEq (Prf.hyp0 : ((t ≐ succ (pred t)) :: Γ) ⊢[PRAAx] t ≐ succ (pred t))
    ipra_le 𝔞 (pred t) with e

/-- `1 ∸ t = 1` gives `t = 0`. -/
theorem zero_of_one_monus {t : PTm n} (h : Γ ⊢[PRAAx] monus one t ≐ one) : Γ ⊢[PRAAx] t ≐ zero := by
  refine .orE (zero_or_succ t) Prf.hyp0 ?_
  exact absurd_one_zero' (h.wk.eqSymm.eqTrans ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans
    ((succ_monus_succ _ _).eqTrans (zero_monus _))))

/-- `b ∸ a ≥ 1` gives `a < b`. -/
theorem lt_of_monus_pos {a b : PTm n} (h : Γ ⊢[PRAAx] le one (monus b a)) : Γ ⊢[PRAAx] lt a b := by
  refine .orE (lt_or_le a b) Prf.hyp0 ?_
  have z : (le b a :: Γ) ⊢[PRAAx] monus b a ≐ zero := Prf.hyp0
  exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans ((congrMonus (.eqRefl _) z).eqSymm.eqTrans h.wk))

/-- `a < b` gives `sg (b ∸ a) = 1`. -/
theorem sg_one_of_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] sg (monus b a) ≐ one := by
  have e := natEq (eq_add_of_le (le_trans (le_succ_self a) h))
  have hp : Γ ⊢[PRAAx] le one (monus b a) := by ipra_le sl h with e
  refine (congrSg ((eq_add_of_le hp).eqTrans (?_ : Γ ⊢[PRAAx] one + monus (monus b a) one ≐ succ (monus (monus b a) one)))).eqTrans
    (sg_succ _)
  ipra_ring

/-- A cell indicator `cnt lo hi c = 1` gives `lo ≤ c < hi`. -/
theorem cnt_one {lo hi c : PTm n} (h : Γ ⊢[PRAAx] cnt lo hi c ≐ one) : Γ ⊢[PRAAx] le lo c ⋏ lt c hi := by
  refine .orE (sg_bit (Γ := Γ) (monus hi c)) ?_ ?_
  · exact absurd_one_zero' (h.wk.eqSymm.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))
  · let Δ : List (Fm PTm n) := (sg (monus hi c) ≐ one) :: Γ
    have s1 : Δ ⊢[PRAAx] sg (monus hi c) ≐ one := Prf.hyp0
    have m1 : Δ ⊢[PRAAx] monus one (monus lo c) ≐ one :=
      (one_mul _).eqSymm.eqTrans ((mul_comm _ _).eqTrans ((congrMul (.eqRefl _) s1.eqSymm).eqTrans h.wk))
    exact .andI (zero_of_one_monus m1) (lt_of_monus_pos (pos_of_sg_one s1))

/-! ## The pointwise exclusion -/

/-- Two members sharing a cell `c` violate the separation. -/
theorem pt_zero {c A' A act' act w : PTm n}
    (hsep : Γ ⊢[PRAAx] sg act' * sg act * sg (monus (A + w) A') * sg (monus (A' + w) A) ≐ zero) :
    Γ ⊢[PRAAx] sg (cnt A' (A' + sg act' * w) c) * sg (cnt A (A + sg act * w) c) ≐ zero := by
  refine (congrMul (cnt_bit _ _ _) (cnt_bit _ _ _)).eqTrans ?_
  refine .orE (sg_bit (Γ := Γ) (cnt A' (A' + sg act' * w) c)) ?_ ?_
  · exact (congrMul ((cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)
  · let Δ : List (Fm PTm n) := (sg (cnt A' (A' + sg act' * w) c) ≐ one) :: Γ
    have c1 : Δ ⊢[PRAAx] cnt A' (A' + sg act' * w) c ≐ one := (cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0
    refine .orE (sg_bit (Γ := Δ) (cnt A (A + sg act * w) c)) ?_ ?_
    · exact (congrMul (.eqRefl _) ((cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0)).eqTrans (mul_zero _)
    · let Δ' : List (Fm PTm n) := (sg (cnt A (A + sg act * w) c) ≐ one) :: Δ
      have c2 : Δ' ⊢[PRAAx] cnt A (A + sg act * w) c ≐ one := (cnt_bit _ _ _).eqSymm.eqTrans Prf.hyp0
      have f1 := cnt_one (c1.wk : Δ' ⊢[PRAAx] _ ≐ one)
      have f2 := cnt_one c2
      refine .botE _ (succ_ne_zero (a := zero) ?_)
      -- both members are active
      have act1 : Δ' ⊢[PRAAx] sg act' ≐ one := by
        refine .orE (sg_bit (Γ := Δ') act') ?_ Prf.hyp0
        let Θ : List (Fm PTm n) := (sg act' ≐ zero) :: Δ'
        have a0 : Θ ⊢[PRAAx] sg act' ≐ zero := Prf.hyp0
        have l1 : Θ ⊢[PRAAx] le A' c := (Prf.andE₁ f1).wk
        have l2 : Θ ⊢[PRAAx] lt c (A' + sg act' * w) := (Prf.andE₂ f1).wk
        have e := natEq a0
        have hz : Θ ⊢[PRAAx] le one zero := by ipra_le sl l2 + sl l1 with 𝔞 w * e
        exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)
      have act2 : Δ' ⊢[PRAAx] sg act ≐ one := by
        refine .orE (sg_bit (Γ := Δ') act) ?_ Prf.hyp0
        let Θ : List (Fm PTm n) := (sg act ≐ zero) :: Δ'
        have a0 : Θ ⊢[PRAAx] sg act ≐ zero := Prf.hyp0
        have l1 : Θ ⊢[PRAAx] le A c := (Prf.andE₁ f2).wk
        have l2 : Θ ⊢[PRAAx] lt c (A + sg act * w) := (Prf.andE₂ f2).wk
        have e := natEq a0
        have hz : Θ ⊢[PRAAx] le one zero := by ipra_le sl l2 + sl l1 with 𝔞 w * e
        exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)
      -- and within `w` of each other
      have ea1 := natEq act1
      have ea2 := natEq act2
      have l1 : Δ' ⊢[PRAAx] le A' c := Prf.andE₁ f1
      have l2 : Δ' ⊢[PRAAx] lt c (A' + sg act' * w) := Prf.andE₂ f1
      have l3 : Δ' ⊢[PRAAx] le A c := Prf.andE₁ f2
      have l4 : Δ' ⊢[PRAAx] lt c (A + sg act * w) := Prf.andE₂ f2
      have g1 : Δ' ⊢[PRAAx] lt A' (A + w) := by ipra_le sl l1 + sl l4 with 𝔞 w * ea2
      have g2 : Δ' ⊢[PRAAx] lt A (A' + w) := by ipra_le sl l3 + sl l2 with 𝔞 w * ea1
      have one1 := sg_one_of_lt g1
      have one2 := sg_one_of_lt g2
      refine .eqTrans ?_ hsep.wk.wk
      refine .eqTrans ?_ (congrMul (congrMul (congrMul act1 act2) one1) one2).eqSymm
      ipra_ring

/-! ## Bodies -/

/-- A sum over ordered pairs vanishes if each term vanishes under the two index bounds. -/
theorem sum_zero_of_ordered_pairs (f : PTm 2) (K x : PTm n)
    (pointwise : ∀ (Δ : List (Fm PTm (n + 1 + 1))) (i j : PTm (n + 1 + 1)),
      (Γ.map Fm.shift).map Fm.shift ⊆ Δ → (Δ ⊢[PRAAx] lt i j) →
        (Δ ⊢[PRAAx] lt j (Syn.shift (Syn.shift K))) →
        (Δ ⊢[PRAAx] inst2 f i (pairT j (Syn.shift (Syn.shift x))) ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF (ap2 (sumF f) (var 0) (pairT (var 0) (var 1)))) K x ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  have hj : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift K) := Prf.hyp0
  simp only [inst2, subst_ap2, subst_pairT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [shift_pairT]
  exact pointwise _ (var 0) (var 1)
    (List.subset_cons_of_subset _ (List.subset_cons_of_subset _ (List.Subset.refl _)))
    Prf.hyp0 (Order.shift_lt hj).wk

section Pack

variable (A act : PTm 2)

/-- `A_j` over `0 = j`, `1 = ⟨w, y⟩`. -/
def loB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] A
/-- `A_j + [act_j] w` over `0 = j`, `1 = ⟨w, y⟩`. -/
def hiB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] A + sg (Syn.subst ![var 0, sndT (var 1)] act) * fstT (var 1)

theorem sub2 (f : PTm 2) (j x : PTm n) : Syn.subst ![j, x] (Syn.subst ![var 0, sndT (var 1)] f) = inst2 f j (sndT x) := by
  simp [subst_reindex2]

theorem inst2_loB (j x : PTm n) : inst2 (loB A) j x = inst2 A j (sndT x) := by
  simp only [inst2, loB] at *; exact sub2 A j x

theorem inst2_hiB (j x : PTm n) : inst2 (hiB A act) j x = inst2 A j (sndT x) + sg (inst2 act j (sndT x)) * fstT x := by
  simp only [hiB, inst2, PTm.subst_add, PTm.subst_mul, Signum.sg, PTm.subst_monus]
  rw [show Syn.subst ![j, x] (Syn.subst ![var 0, sndT (var 1)] A) = inst2 A j (sndT x) from sub2 A j x,
    show Syn.subst ![j, x] (Syn.subst ![var 0, sndT (var 1)] act) = inst2 act j (sndT x) from sub2 act j x]
  simp [inst2]

/-- The separation term of `j' < j` over `0 = j'`, `1 = ⟨j, ⟨w, y⟩⟩`. -/
def spB : PTm 2 :=
  sg (Syn.subst ![var 0, sndT (sndT (var 1))] act) * sg (Syn.subst ![fstT (var 1), sndT (sndT (var 1))] act) *
    sg (monus (Syn.subst ![fstT (var 1), sndT (sndT (var 1))] A + fstT (sndT (var 1)))
      (Syn.subst ![var 0, sndT (sndT (var 1))] A)) *
    sg (monus (Syn.subst ![var 0, sndT (sndT (var 1))] A + fstT (sndT (var 1)))
      (Syn.subst ![fstT (var 1), sndT (sndT (var 1))] A))

theorem sub3 (f : PTm 2) (j' z : PTm n) :
    Syn.subst ![j', z] (Syn.subst ![var 0, sndT (sndT (var 1))] f) = inst2 f j' (sndT (sndT z)) := by
  simp [subst_reindex2]

theorem sub4 (f : PTm 2) (j' z : PTm n) :
    Syn.subst ![j', z] (Syn.subst ![fstT (var 1), sndT (sndT (var 1))] f) = inst2 f (fstT z) (sndT (sndT z)) := by
  simp [subst_reindex2]

theorem inst2_spB (j' z : PTm n) : inst2 (spB A act) j' z =
    sg (inst2 act j' (sndT (sndT z))) * sg (inst2 act (fstT z) (sndT (sndT z))) *
      sg (monus (inst2 A (fstT z) (sndT (sndT z)) + fstT (sndT z)) (inst2 A j' (sndT (sndT z)))) *
      sg (monus (inst2 A j' (sndT (sndT z)) + fstT (sndT z)) (inst2 A (fstT z) (sndT (sndT z)))) := by
  simp only [spB, inst2, PTm.subst_add, PTm.subst_mul, Signum.sg, PTm.subst_monus]
  rw [sub3 A j' z, sub3 act j' z, sub4 A j' z, sub4 act j' z]
  simp [inst2]

/-- The separations below `j`, over `0 = j`, `1 = ⟨w, y⟩`. -/
abbrev srB : PTm 2 := ap2 (sumF (spB A act)) (var 0) (pairT (var 0) (var 1))

theorem inst2_srB (j x : PTm n) : inst2 (srB A act) j x = ap2 (sumF (spB A act)) j (pairT j x) := by
  simp [inst2, subst_ap2]

/-- `[act_j]` over `0 = j`, `1 = y`. -/
abbrev acB : PTm 2 := sg act

/-- A doubly-covered term of the overlap sum vanishes, given the separation sum. -/
theorem ovl_pt {j' j c K w y : PTm n} (hjK : Γ ⊢[PRAAx] lt j K) (hj' : Γ ⊢[PRAAx] lt j' j)
    (hS : Γ ⊢[PRAAx] ap2 (sumF (srB A act)) K (pairT w y) ≐ zero) :
    Γ ⊢[PRAAx] inst2 (prB (ajB (loB A) (hiB A act))) j' (pairT j (pairT c (pairT w y))) ≐ zero := by
  have t1 := term_zero (srB A act) hjK hS
  rw [inst2_srB] at t1
  have t2 := term_zero (spB A act) hj' t1
  rw [inst2_spB] at t2
  have fj : Γ ⊢[PRAAx] fstT (pairT j (pairT w y)) ≐ j := fst_pair _ _
  have sw : Γ ⊢[PRAAx] fstT (sndT (pairT j (pairT w y))) ≐ w := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have sy : Γ ⊢[PRAAx] sndT (sndT (pairT j (pairT w y))) ≐ y := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  have hsep : Γ ⊢[PRAAx] sg (inst2 act j' y) * sg (inst2 act j y) *
      sg (monus (inst2 A j y + w) (inst2 A j' y)) * sg (monus (inst2 A j' y + w) (inst2 A j y)) ≐ zero := by
    refine .eqTrans ?_ t2
    exact (congrMul (congrMul (congrMul (congrSg (congrInst2 act (.eqRefl _) sy))
      (congrSg (congrInst2 act fj sy)))
      (congrSg (congrMonus (congrAdd (congrInst2 A fj sy) sw) (congrInst2 A (.eqRefl _) sy))))
      (congrSg (congrMonus (congrAdd (congrInst2 A (.eqRefl _) sy) sw) (congrInst2 A fj sy)))).eqSymm
  refine .eqTrans ?_ (pt_zero (c := c) hsep)
  rw [inst2_prB, inst2_ajB, inst2_ajB, inst2_loB, inst2_loB, inst2_hiB, inst2_hiB]
  have s1 : Γ ⊢[PRAAx] sndT (pairT j (pairT c (pairT w y))) ≐ pairT c (pairT w y) := snd_pair _ _
  have f1 : Γ ⊢[PRAAx] fstT (pairT j (pairT c (pairT w y))) ≐ j := fst_pair _ _
  have xc : Γ ⊢[PRAAx] fstT (sndT (pairT j (pairT c (pairT w y)))) ≐ c := (congrFst s1).eqTrans (fst_pair _ _)
  have xx : Γ ⊢[PRAAx] sndT (sndT (pairT j (pairT c (pairT w y)))) ≐ pairT w y := (congrSnd s1).eqTrans (snd_pair _ _)
  have xy : Γ ⊢[PRAAx] sndT (sndT (sndT (pairT j (pairT c (pairT w y))))) ≐ y := (congrSnd xx).eqTrans (snd_pair _ _)
  have xw : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT j (pairT c (pairT w y))))) ≐ w := (congrFst xx).eqTrans (fst_pair _ _)
  have cn : ∀ {i i' : PTm n}, (Γ ⊢[PRAAx] i ≐ i') →
      (Γ ⊢[PRAAx] cnt (inst2 A i (sndT (sndT (sndT (pairT j (pairT c (pairT w y)))))))
        (inst2 A i (sndT (sndT (sndT (pairT j (pairT c (pairT w y)))))) +
          sg (inst2 act i (sndT (sndT (sndT (pairT j (pairT c (pairT w y))))))) *
            fstT (sndT (sndT (pairT j (pairT c (pairT w y))))))
        (fstT (sndT (pairT j (pairT c (pairT w y))))) ≐
      cnt (inst2 A i' y) (inst2 A i' y + sg (inst2 act i' y) * w) c) := fun hi =>
    congrMul (congrMonus (.eqRefl _) (congrMonus (congrInst2 A hi xy) xc))
      (congrSg (congrMonus (congrAdd (congrInst2 A hi xy) (congrMul (congrSg (congrInst2 act hi xy)) xw)) xc))
  exact congrMul (congrSg (cn (.eqRefl _))) (congrSg (cn f1))

/-- Packing: `w`-separated active intervals of width `w` inside the grid have union length
`w Σ_j [act_j]`. -/
theorem packing {T K w y : PTm n}
    (hT : Γ ⊢[PRAAx] ap2 (sumF (outB (hiB A act))) K (pairT T (pairT w y)) ≐ zero)
    (hS : Γ ⊢[PRAAx] ap2 (sumF (srB A act)) K (pairT w y) ≐ zero) :
    Γ ⊢[PRAAx] measure (loB A) (hiB A act) T K (pairT w y) ≐ w * ap2 (sumF (acB act)) K y := by
  refine (additive (loB A) (hiB A act) hT ?_).eqTrans ?_
  · -- no cell is covered twice
    refine (sum_congr_bounded _ (zero : PTm 2) _ (pairT K (pairT w y)) T (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (pairT K (pairT w y))) = zero by simp [inst2],
      inst2_ovlB, show Syn.shift (pairT K (pairT w y)) = pairT (Syn.shift K) (pairT (Syn.shift w) (Syn.shift y)) by
        simp [Syn.shift]]
    let Θ₁ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift T) :: Γ.map Fm.shift
    have hS1 : Θ₁ ⊢[PRAAx] ap2 (sumF (srB A act)) (Syn.shift K) (pairT (Syn.shift w) (Syn.shift y)) ≐ zero := by
      have s0 : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF (srB A act)) (Syn.shift K) (pairT (Syn.shift w) (Syn.shift y)) ≐ zero := by
        simpa [Fm.shift, Syn.shift, subst_ap2] using hS.shift
      exact s0.wk
    refine (congrAp2 (sumF (rwB (ajB (loB A) (hiB A act)))) (fst_pair _ _)
      (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
    refine (sum_congr_bounded _ (zero : PTm 2) _ (pairT (var 0) (pairT (Syn.shift w) (Syn.shift y))) _
      (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1 + 1)) _ = zero by simp [inst2], inst2_rwB,
      show Syn.shift (pairT (var 0 : PTm (n + 1)) (pairT (Syn.shift w) (Syn.shift y))) =
        pairT (var 1) (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y))) by simp [Syn.shift]]
    let Θ₂ : List (Fm PTm (n + 1 + 1)) := lt (var 0) (Syn.shift (Syn.shift K)) :: Θ₁.map Fm.shift
    have hS2 : Θ₂ ⊢[PRAAx] ap2 (sumF (srB A act)) (Syn.shift (Syn.shift K))
        (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y))) ≐ zero := by
      have s0 : Θ₁.map Fm.shift ⊢[PRAAx] ap2 (sumF (srB A act)) (Syn.shift (Syn.shift K))
          (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y))) ≐ zero := by
        simpa [Fm.shift, Syn.shift, subst_ap2] using hS1.shift
      exact s0.wk
    have hK2 : Θ₂ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift K)) := Prf.hyp0
    refine (sum_congr_bounded _ (zero : PTm 2) _ (pairT (var 0) (pairT (var 1) (pairT (Syn.shift (Syn.shift w))
      (Syn.shift (Syn.shift y))))) _ (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1 + 1 + 1)) _ = zero by simp [inst2],
      show Syn.shift (pairT (var 0 : PTm (n + 1 + 1)) (pairT (var 1) (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y))))) =
        pairT (var 1) (pairT (var 2) (pairT (Syn.shift (Syn.shift (Syn.shift w))) (Syn.shift (Syn.shift (Syn.shift y))))) by
        simp [Syn.shift]]
    let Θ₃ : List (Fm PTm (n + 1 + 1 + 1)) := lt (var 0) (Syn.shift (var 0)) :: Θ₂.map Fm.shift
    have hS3 : Θ₃ ⊢[PRAAx] ap2 (sumF (srB A act)) (Syn.shift (Syn.shift (Syn.shift K)))
        (pairT (Syn.shift (Syn.shift (Syn.shift w))) (Syn.shift (Syn.shift (Syn.shift y)))) ≐ zero := by
      have s0 : Θ₂.map Fm.shift ⊢[PRAAx] ap2 (sumF (srB A act)) (Syn.shift (Syn.shift (Syn.shift K)))
          (pairT (Syn.shift (Syn.shift (Syn.shift w))) (Syn.shift (Syn.shift (Syn.shift y)))) ≐ zero := by
        simpa [Fm.shift, Syn.shift, subst_ap2] using hS2.shift
      exact s0.wk
    have hK3 : Θ₃ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift (Syn.shift K))) := by
      have s0 : Θ₂.map Fm.shift ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift (Syn.shift K))) := by
        simpa [Fm.shift, Syn.shift] using hK2.shift
      exact s0.wk
    have hj : Θ₃ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
    exact ovl_pt A act hK3 hj hS3
  · -- the total length is `w Σ_j [act_j]`
    refine sum_scale (lenB (loB A) (hiB A act)) (acB act) K w y (pairT w y) (.allI (.impI ?_))
    rw [show inst2 (lenB (loB A) (hiB A act)) (var 0 : PTm (n + 1)) (Syn.shift (pairT w y)) =
        monus (inst2 (hiB A act) (var 0) (Syn.shift (pairT w y))) (inst2 (loB A) (var 0) (Syn.shift (pairT w y))) by
        simp [lenB, inst2],
      inst2_hiB, inst2_loB, show inst2 (acB act) (var 0 : PTm (n + 1)) (Syn.shift y) = sg (inst2 act (var 0) (Syn.shift y)) by
        simp [inst2, Signum.sg],
      show Syn.shift (pairT w y) = pairT (Syn.shift w) (Syn.shift y) by simp [Syn.shift]]
    refine (add_monus' _ _).eqTrans ?_
    exact (congrMul (congrSg (congrInst2 act (.eqRefl _) (snd_pair _ _))) (fst_pair _ _)).eqTrans (mul_comm _ _)

end Pack

end LeanProofs.IPRA.Foundations.IntervalPacking

export_ipra Foundations.IntervalPacking (absurd_one_zero' acB inst2_hiB)
