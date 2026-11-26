import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesVignerasIntegerPeriod
import IPRADerivations.Analysis.Logarithm.DyadicComplexLogarithm

/-!
# Reduce the positive rational Barnes quotient to the unit interval starting at one

Use the actual quotient and remainder of the rational numerator by its
positive denominator. When the integer part is zero, advance once.
Otherwise compare with the forward integer shift of the base chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasBaseInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasIntegerPeriod (advance data nameF source period_at)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def baseNumerator (a b : PTm n) : PTm n := b+rem a b

@[simp] theorem subst_baseNumerator {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (baseNumerator a b) = baseNumerator (Syn.subst σ a) (Syn.subst σ b) := by simp [baseNumerator]

theorem interval (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le b (baseNumerator a b) ⋏ lt (baseNumerator a b) (two*b) := by
  have bound := (DyadicComplexLogarithm.positive_division a b hb).andE₂
  exact .andI (le_add_right b (rem a b))
    (le_congr (add_succ b (rem a b)) (by ipra_ring) (add_le_add₂ (le_refl b) bound))

private theorem data_equal (t : PTm 2) (a c b : PTm n) (e : Γ ⊢[PRAAx] a ≐ c) :
    Γ ⊢[PRAAx] data t a b ≐ data t c b := by
  ipra_congr (data t (var 0) (var 1) : PTm 2) with [e,.eqRefl b]

theorem reduction (f : PR 2) (t : PTm 2) (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (ha : Γ ⊢[PRAAx] source f t a b) (hbase : Γ ⊢[PRAAx] source f t (baseNumerator a b) b) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data t a b) (data t (baseNumerator a b) b) := by
  let q := quo a b
  let r := rem a b
  let c := baseNumerator a b
  have div : Γ ⊢[PRAAx] a ≐ b*q+r := (DyadicComplexLogarithm.positive_division a b hb).andE₁
  refine .orE (zero_or_succ q) ?_ ?_
  · have eq : (q ≐ zero) :: Γ ⊢[PRAAx] a ≐ r := div.wk.eqTrans
      ((congrAdd (congrMul (.eqRefl b) Prf.hyp0) (.eqRefl r)).eqTrans (by ipra_ring))
    have next : (q ≐ zero) :: Γ ⊢[PRAAx] advance a b one ≐ c :=
      (congrAdd eq (.eqRefl (one*b))).eqTrans (by dsimp only [c,baseNumerator,r]; ipra_ring)
    have p := period_at (Γ := (q ≐ zero) :: Γ) f t a b one ha.wk
    exact cross_symm _ _ _ _ (cross_data_congr _ _ _ _ _ _ (data_equal t _ _ _ next) (.eqRefl _) p)
  · have eq : (q ≐ succ (pred q)) :: Γ ⊢[PRAAx] a ≐ advance c b (pred q) :=
      div.wk.eqTrans ((congrAdd (congrMul (.eqRefl b) Prf.hyp0) (.eqRefl r)).eqTrans
       (by dsimp only [advance,c,baseNumerator,r]; ipra_ring))
    have p := period_at (Γ := (q ≐ succ (pred q)) :: Γ) f t c b (pred q) hbase.wk
    exact cross_data_congr _ _ _ _ _ _ (data_equal t _ _ _ eq.eqSymm) (.eqRefl _) p

theorem actual_Barnes_candidate_log_quotient_base_interval_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let a := var 0
       let b := var 1
       let c := baseNumerator a b
       (le one b ⋏ (source f t a b ⋏ source f t c b)) ⟶
       le b c ⋏ (lt c (two*b) ⋏ crossEquivalent (nameF f) (nameF f) (data t a b) (data t c b))) :=
  closeUniv 2 (.impI (.andI (interval _ _ Prf.hyp0.andE₁).andE₁
    (.andI (interval _ _ Prf.hyp0.andE₁).andE₂ (reduction f t _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasBaseInterval
