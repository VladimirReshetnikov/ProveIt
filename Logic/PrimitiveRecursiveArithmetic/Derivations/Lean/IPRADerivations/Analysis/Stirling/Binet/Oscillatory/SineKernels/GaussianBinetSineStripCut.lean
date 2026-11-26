import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName

/-!
# Numerical cut of the actual sine grid near zero

The floor cut selects a prefix of physical length at most one over E.
On a sufficiently fine positive mesh, every surviving point has
frequency at least one over twice E.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineStripCut

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCompactRiemannName (positive_as_successor)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cutoff (N T E : PTm n) : PTm n := quo N (T*E)

ipra_subst cutoff

theorem prefix_admission (N T E : PTm n) (hT : Γ ⊢[PRAAx] le one T) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] le (cutoff N T E) N ⋏ le ((T*cutoff N T E)*E) N := by
  let d := T*E
  let Q := cutoff N T E
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hT hE
  have qr := div_mod_at (x := N) (positive_as_successor d hd)
  have upper : Γ ⊢[PRAAx] le (d*Q) N := le_congr (.eqRefl _) qr.andE₁.eqSymm (le_add_right _ _)
  have first : Γ ⊢[PRAAx] le Q (d*Q) := le_congr (one_mul Q) (.eqRefl _) (mul_le_mul_right Q hd)
  exact .andI (le_trans first upper) (le_congr (by dsimp only [d]; ipra_ring) (.eqRefl _) upper)

theorem remaining_margin (j N T E : PTm n) (hT : Γ ⊢[PRAAx] le one T) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le (two*(T*E)) N) (hj : Γ ⊢[PRAAx] le (cutoff N T E) j) :
    Γ ⊢[PRAAx] le one j ⋏ le N ((T*j)*(two*E)) := by
  let d := T*E
  let Q := cutoff N T E
  let r := rem N d
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hT hE
  have qr := div_mod_at (x := N) (positive_as_successor d hd)
  have hQ : Γ ⊢[PRAAx] le one Q := by
    refine .orE (zero_or_succ Q) ?_ ?_
    · let Δ := (Q ≐ zero) :: Γ
      have y : Δ ⊢[PRAAx] N ≐ r := qr.andE₁.wk.eqTrans
        ((congrAdd (congrMul (.eqRefl d) Prf.hyp0) (.eqRefl _)).eqTrans (by ipra_ring))
      have grow : Δ ⊢[PRAAx] le d (two*d) := le_of_eq_add (d := d) (by ipra_ring)
      have leq : Δ ⊢[PRAAx] le d r := le_congr (.eqRefl _) y (le_trans grow hN.wk)
      exact le_lt_absurd _ leq qr.andE₂.wk
    · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
  have rsmall : Γ ⊢[PRAAx] le r (d*Q) :=
    le_trans (le_of_lt qr.andE₂) (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right d hQ))
  have mid : Γ ⊢[PRAAx] le N (two*(d*Q)) :=
    le_congr qr.andE₁.eqSymm (by ipra_ring) (add_le_add₂ (le_refl (d*Q)) rsmall)
  have last : Γ ⊢[PRAAx] le (two*(d*Q)) ((T*j)*(two*E)) :=
    le_congr (by ipra_ring) (by dsimp only [d]; ipra_ring) (mul_le_mul_right (two*d) hj)
  exact .andI (le_trans hQ hj) (le_trans mid last)

end LeanProofs.IPRA.Analysis.GaussianBinetSineStripCut
