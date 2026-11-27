import IPRADerivations.Foundations.IntervalCover
import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Core.OrderCertificates

/-!
# Localization of an interval cover (`hurwitz_khinchin_ipra`, (K2))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "All added intervals are inside the gap
in which they were constructed." On the grid of `Foundations/IntervalCover`, the cover bit of a cell `c` is
`sg(Σ_{j<K} [lo_j ≤ c][c < hi_j])`. If every member `[lo_j, hi_j)` is empty (`hi_j ≤ lo_j`) or lies inside
`[L, H)`, no cell outside `[L, H)` is covered:

* `cnt_below`, `cnt_above`: `[lo ≤ c][c < hi] = 0` when `c < lo` or `hi ≤ c`;
* `cnt_out`: the same for a member that is empty or inside `[L, H)`, at a cell `c < L` or `c ≥ H`;
* `cover_out`: the cover bit vanishes at every cell outside `[L, H)`.

So the measure of the union counts only cells of the gap `[L, H)` — the cells a (K11) block constructed inside a
gap can contribute to the gap's newly covered count in `KhinchinGridRound`.
-/

namespace LeanProofs.IPRA.Foundations.CoverLocal

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt indB inst3_indB covB)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias congrSg' := Common.congrSg

/-- `c < lo` gives `[lo ≤ c][c < hi] = 0`. -/
theorem cnt_below {lo hi c : PTm n} (h : Γ ⊢[PRAAx] lt c lo) : Γ ⊢[PRAAx] cnt lo hi c ≐ zero := by
  have e1 := natEq (eq_add_of_le h)
  have e2 := natEq (eq_add_of_le (le_of_lt h))
  have h1 : Γ ⊢[PRAAx] le one (monus lo c) := by ipra_le 𝔞 (monus lo (succ c)) with e1 - e2
  exact (congrMul h1 (.eqRefl _)).eqTrans (zero_mul _)

/-- `hi ≤ c` gives `[lo ≤ c][c < hi] = 0`. -/
theorem cnt_above {lo hi c : PTm n} (h : Γ ⊢[PRAAx] le hi c) : Γ ⊢[PRAAx] cnt lo hi c ≐ zero :=
  (congrMul (.eqRefl _) ((congrSg' h).eqTrans sg_zero)).eqTrans (mul_zero _)

/-- A member that is empty or inside `[L, H)` does not meet a cell outside `[L, H)`. -/
theorem cnt_out {lo hi c L H : PTm n}
    (hm : Γ ⊢[PRAAx] le hi lo ⋎ (le L lo ⋏ le hi H)) (hc : Γ ⊢[PRAAx] lt c L ⋎ le H c) :
    Γ ⊢[PRAAx] cnt lo hi c ≐ zero := by
  refine .orE hm ?_ ?_
  · refine .orE (lt_or_le c lo) (cnt_below Prf.hyp0) ?_
    exact cnt_above (le_trans Prf.hyp1 Prf.hyp0)
  · refine .orE hc.wk ?_ ?_
    · exact cnt_below (le_trans Prf.hyp0 (Prf.andE₁ Prf.hyp1))
    · exact cnt_above (le_trans (Prf.andE₂ Prf.hyp1) Prf.hyp0)

/-- The cover bit vanishes at every cell outside `[L, H)` when every member is empty or inside `[L, H)`. -/
theorem cover_out (lo hi : PTm 2) {c K x L H : PTm n}
    (hm : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      le (inst2 hi (var 0) (Syn.shift x)) (inst2 lo (var 0) (Syn.shift x)) ⋎
        (le (Syn.shift L) (inst2 lo (var 0) (Syn.shift x)) ⋏ le (inst2 hi (var 0) (Syn.shift x)) (Syn.shift H))))
    (hc : Γ ⊢[PRAAx] lt c L ⋎ le H c) :
    Γ ⊢[PRAAx] inst2 (covB lo hi) c (pairT K x) ≐ zero := by
  have hs : Γ ⊢[PRAAx] le (ap2 (sumF (rowB (indB lo hi))) K (pairT c x)) (K * zero) := by
    refine sum_le_const (rowB (indB lo hi)) (.allI (.impI ?_))
    have p := Prf.impE (hm.allOpen.wk (ψ := lt (var 0) (Syn.shift K))) Prf.hyp0
    have hc' : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift c) (Syn.shift L) ⋎
        le (Syn.shift H) (Syn.shift c) := by
      have s := (hc.shift).wk (ψ := lt (var 0) (Syn.shift K))
      simpa [Fm.shift, Syn.shift] using s
    rw [show Syn.shift (pairT c x) = pairT (Syn.shift c) (Syn.shift x) by simp [Syn.shift], inst2_rowB,
      show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
    have z := cnt_out p hc'
    rw [inst3_indB]
    have es := snd_pair (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) (Syn.shift c) (Syn.shift x)
    have ef := fst_pair (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) (Syn.shift c) (Syn.shift x)
    have ec : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx]
        cnt (inst2 lo (var 0) (sndT (pairT (Syn.shift c) (Syn.shift x))))
            (inst2 hi (var 0) (sndT (pairT (Syn.shift c) (Syn.shift x)))) (fstT (pairT (Syn.shift c) (Syn.shift x))) ≐
          cnt (inst2 lo (var 0) (Syn.shift x)) (inst2 hi (var 0) (Syn.shift x)) (Syn.shift c) :=
      congrMul (congrMonus (.eqRefl _) (congrMonus (congrInst2 lo (.eqRefl _) es) ef))
        (congrSg' (congrMonus (congrInst2 hi (.eqRefl _) es) ef))
    exact (monus_zero _).eqTrans (ec.eqTrans z)
  have h0 : Γ ⊢[PRAAx] le (K * zero) zero := by ipra_le 0
  have hz : Γ ⊢[PRAAx] ap2 (sumF (rowB (indB lo hi))) K (pairT c x) ≐ zero :=
    (monus_zero _).eqSymm.eqTrans (le_trans hs h0)
  have e1 : Γ ⊢[PRAAx] inst2 (oB (indB lo hi)) c (pairT K x) ≐ ap2 (sumF (rowB (indB lo hi))) K (pairT c x) := by
    rw [inst2_oB]
    exact congrAp2 (sumF (rowB (indB lo hi))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  rw [show inst2 (covB lo hi) c (pairT K x) = sg (inst2 (oB (indB lo hi)) c (pairT K x)) by simp [covB, inst2]]
  exact (congrSg' (e1.eqTrans hz)).eqTrans sg_zero

end LeanProofs.IPRA.Foundations.CoverLocal
