import IPRADerivations.Foundations.IntervalPacking

/-!
# Packings from pointwise hypotheses

Framework companion of `Foundations/IntervalPacking` (packet `diophantine-number-theory/hurwitz_khinchin_ipra`,
`khinchin.tex`, (K8)–(K9)). `IntervalPacking.packing` takes its two hypotheses as vanishing sums. In
applications they are proved one member (resp. one pair of members) at a time, so `packing_pt` accepts
them pointwise, schematically in every context extending the shifted context (the style of
`AnalyticNumberTheory/MobiusBounds.sum_ext`):

* `hT`: for every `a < K`, `A_a + [act_a] w ≤ T` (the member lies in the grid);
* `hS`: for every `a < b < K`, `[act_a][act_b][A_a < A_b + w][A_b < A_a + w] = 0` (separation).

The conclusion is the packing identity `measure = w Σ_{j<K} [act_j]`.
-/

namespace LeanProofs.IPRA.Foundations.PackingPointwise

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt measure lenB)
open LeanProofs.IPRA.Foundations.IntervalAdditive (outB inst2_outB)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB inst2_hiB spB inst2_spB srB inst2_srB acB packing)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Pack

variable (A act : PTm 2)

/-- The grid hypothesis of `packing`, from the members. -/
theorem out_zero {T K w y : PTm n}
    (hT : ∀ (Δ : List (Fm PTm (n + 1))) (a : PTm (n + 1)), Γ.map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt a (Syn.shift K)) →
      (Δ ⊢[PRAAx] le (inst2 A a (Syn.shift y) + sg (inst2 act a (Syn.shift y)) * Syn.shift w) (Syn.shift T))) :
    Γ ⊢[PRAAx] ap2 (sumF (outB (hiB A act))) K (pairT T (pairT w y)) ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [inst2_outB, inst2_hiB, show Syn.shift (pairT T (pairT w y)) =
    pairT (Syn.shift T) (pairT (Syn.shift w) (Syn.shift y)) by simp [Syn.shift]]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  have h := hT Θ (var 0) (List.subset_cons_of_subset _ (List.Subset.refl _)) Prf.hyp0
  have s1 : Θ ⊢[PRAAx] sndT (pairT (Syn.shift T) (pairT (Syn.shift w) (Syn.shift y))) ≐
      pairT (Syn.shift w) (Syn.shift y) := snd_pair _ _
  have yy : Θ ⊢[PRAAx] sndT (sndT (pairT (Syn.shift T) (pairT (Syn.shift w) (Syn.shift y)))) ≐ Syn.shift y :=
    (congrSnd s1).eqTrans (snd_pair _ _)
  have ww : Θ ⊢[PRAAx] fstT (sndT (pairT (Syn.shift T) (pairT (Syn.shift w) (Syn.shift y)))) ≐ Syn.shift w :=
    (congrFst s1).eqTrans (fst_pair _ _)
  have tt : Θ ⊢[PRAAx] fstT (pairT (Syn.shift T) (pairT (Syn.shift w) (Syn.shift y))) ≐ Syn.shift T := fst_pair _ _
  exact (congrMonus (congrAdd (congrInst2 A (.eqRefl _) yy)
    (congrMul (congrSg (congrInst2 act (.eqRefl _) yy)) ww)) tt).eqTrans h

/-- The separation hypothesis of `packing`, from the pairs. -/
theorem sep_zero {K w y : PTm n}
    (hS : ∀ (Δ : List (Fm PTm (n + 1 + 1))) (a b : PTm (n + 1 + 1)), (Γ.map Fm.shift).map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt a b) → (Δ ⊢[PRAAx] lt b (Syn.shift (Syn.shift K))) →
      (Δ ⊢[PRAAx] sg (inst2 act a (Syn.shift (Syn.shift y))) * sg (inst2 act b (Syn.shift (Syn.shift y))) *
        sg (monus (inst2 A b (Syn.shift (Syn.shift y)) + Syn.shift (Syn.shift w)) (inst2 A a (Syn.shift (Syn.shift y)))) *
        sg (monus (inst2 A a (Syn.shift (Syn.shift y)) + Syn.shift (Syn.shift w)) (inst2 A b (Syn.shift (Syn.shift y))))
        ≐ zero)) :
    Γ ⊢[PRAAx] ap2 (sumF (srB A act)) K (pairT w y) ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [inst2_srB, show Syn.shift (pairT w y) = pairT (Syn.shift w) (Syn.shift y) by simp [Syn.shift]]
  let Θ₁ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  have hK1 : Θ₁ ⊢[PRAAx] lt (var 0) (Syn.shift K) := Prf.hyp0
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [inst2_spB, show Syn.shift (pairT (var 0 : PTm (n + 1)) (pairT (Syn.shift w) (Syn.shift y))) =
    pairT (var 1) (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y))) by simp [Syn.shift]]
  let Θ₂ : List (Fm PTm (n + 1 + 1)) := lt (var 0) (Syn.shift (var 0)) :: Θ₁.map Fm.shift
  have hab : Θ₂ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
  have hbK : Θ₂ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift K)) := by
    have s0 : Θ₁.map Fm.shift ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift K)) := by
      simpa [Fm.shift, Syn.shift] using hK1.shift
    exact s0.wk
  have hs : (Γ.map Fm.shift).map Fm.shift ⊆ Θ₂ :=
    List.subset_cons_of_subset _ (List.subset_cons_of_subset _ (List.Subset.refl _))
  have h := hS Θ₂ (var 0) (var 1) hs hab hbK
  have s1 : Θ₂ ⊢[PRAAx] sndT (pairT (var 1) (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y)))) ≐
      pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y)) := snd_pair _ _
  have fj : Θ₂ ⊢[PRAAx] fstT (pairT (var 1) (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y)))) ≐ var 1 :=
    fst_pair _ _
  have sw : Θ₂ ⊢[PRAAx] fstT (sndT (pairT (var 1) (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y))))) ≐
      Syn.shift (Syn.shift w) := (congrFst s1).eqTrans (fst_pair _ _)
  have sy : Θ₂ ⊢[PRAAx] sndT (sndT (pairT (var 1) (pairT (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift y))))) ≐
      Syn.shift (Syn.shift y) := (congrSnd s1).eqTrans (snd_pair _ _)
  refine .eqTrans ?_ h
  exact congrMul (congrMul (congrMul (congrSg (congrInst2 act (.eqRefl _) sy)) (congrSg (congrInst2 act fj sy)))
      (congrSg (congrMonus (congrAdd (congrInst2 A fj sy) sw) (congrInst2 A (.eqRefl _) sy))))
    (congrSg (congrMonus (congrAdd (congrInst2 A (.eqRefl _) sy) sw) (congrInst2 A fj sy)))

/-- Packing from pointwise hypotheses: members inside the grid, active pairs `w`-separated. -/
theorem packing_pt {T K w y : PTm n}
    (hT : ∀ (Δ : List (Fm PTm (n + 1))) (a : PTm (n + 1)), Γ.map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt a (Syn.shift K)) →
      (Δ ⊢[PRAAx] le (inst2 A a (Syn.shift y) + sg (inst2 act a (Syn.shift y)) * Syn.shift w) (Syn.shift T)))
    (hS : ∀ (Δ : List (Fm PTm (n + 1 + 1))) (a b : PTm (n + 1 + 1)), (Γ.map Fm.shift).map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt a b) → (Δ ⊢[PRAAx] lt b (Syn.shift (Syn.shift K))) →
      (Δ ⊢[PRAAx] sg (inst2 act a (Syn.shift (Syn.shift y))) * sg (inst2 act b (Syn.shift (Syn.shift y))) *
        sg (monus (inst2 A b (Syn.shift (Syn.shift y)) + Syn.shift (Syn.shift w)) (inst2 A a (Syn.shift (Syn.shift y)))) *
        sg (monus (inst2 A a (Syn.shift (Syn.shift y)) + Syn.shift (Syn.shift w)) (inst2 A b (Syn.shift (Syn.shift y))))
        ≐ zero)) :
    Γ ⊢[PRAAx] measure (loB A) (hiB A act) T K (pairT w y) ≐ w * ap2 (sumF (acB act)) K y :=
  packing A act (out_zero A act hT) (sep_zero A act hS)

end Pack

end LeanProofs.IPRA.Foundations.PackingPointwise
