import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeZero
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeDiskIndependence
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalTaylorDerivativeRadius
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalTaylorFirstDerivativeAnchor

/-!
# Radius independence at every retained Barnes Taylor order

At degree zero the name is the canonical Barnes value. At degree one it
is the original first derivative. Higher retained degrees use the
normalized forward grid and truncation-order independence.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorAllOrderRadius

open_ipra
open ComplexLogarithmRemainder (bounded_mono)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "G" => GaussianBarnesCanonicalValueDerivative.nameF
local notation "gd" => GaussianBarnesCanonicalValueDerivative.data

private theorem first_data_radius (z R B : PTm n) :
    Γ ⊢[PRAAx] gd z (succ R) B ≐ gd z (R+one) B := by
  simpa only [GaussianBarnesCanonicalDerivativeDiskIndependence.subst_data,
    Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
    Prf.eqCongr1 (gd (Syn.shift z) (var 0) (Syn.shift B)) (succ_eq_add_one (Γ := Γ) R)

private theorem degree_data_congr (z R B M e j : PTm n) (h : Γ ⊢[PRAAx] e ≐ j) :
    Γ ⊢[PRAAx] fd z R B M e ≐ fd z R B M j := by
  ipra_congr (fd (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl z, .eqRefl R, .eqRefl B, .eqRefl M, h] using
    [GaussianBarnesCanonicalTaylorProductDerivativeName.data,GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData]

private theorem widen_source (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI h.andE₁ (bounded_mono h.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

theorem first_cross (z R S B M : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z (R+one) B M one) (fd z (S+one) B M one) := by
  have older := GaussianBarnesCanonicalDerivativeDiskIndependence.independent_radii z R S B hR hS
  have middle : Γ ⊢[PRAAx] crossEquivalent G G (gd z (R+one) B) (gd z (S+one) B) :=
    cross_data_congr G G _ _ _ _ (first_data_radius z R B) (first_data_radius z S B) older
  have left := GaussianBarnesCanonicalTaylorFirstDerivativeAnchor.cross z R B M hR
  have right := GaussianBarnesCanonicalTaylorFirstDerivativeAnchor.cross z S B M hS
  exact cross_trans F G F _ _ _ left (cross_trans G G F _ _ _ middle (cross_symm F G _ _ right))

theorem retained_cross (z R S B M e : PTm n) (hR : Γ ⊢[PRAAx] source z R B)
    (hS : Γ ⊢[PRAAx] source z S B) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z (R+one) B M e) (fd z (S+one) B M e) := by
  refine .orE (lt_or_le e one) ?_ ?_
  · have eq : lt e one :: Γ ⊢[PRAAx] e ≐ zero :=
      le_antisymm (Common.le_of_lt_succ Prf.hyp0) (zero_le e)
    exact cross_data_congr F F _ _ _ _
      (degree_data_congr z (R+one) B M zero e eq.eqSymm) (degree_data_congr z (S+one) B M zero e eq.eqSymm)
      (GaussianBarnesCanonicalTaylorDerivativeZero.radius_cross z (R+one) (S+one) B M
        (widen_source z R B hR.wk) (widen_source z S B hS.wk))
  · refine .orE (lt_or_le e two) ?_ ?_
    · have eq : lt e two :: le one e :: Γ ⊢[PRAAx] e ≐ one :=
        le_antisymm (Common.le_of_lt_succ Prf.hyp0) Prf.hyp1
      exact cross_data_congr F F _ _ _ _
        (degree_data_congr z (R+one) B M one e eq.eqSymm) (degree_data_congr z (S+one) B M one e eq.eqSymm)
        (first_cross z R S B M hR.wk.wk hS.wk.wk)
    · exact GaussianBarnesCanonicalTaylorDerivativeRadius.retained_cross z R S B M e
        hR.wk.wk hS.wk.wk Prf.hyp0 he.wk.wk

theorem actual_Barnes_all_retained_factorial_Taylor_disk_overlap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let R := var 1
       let S := var 2
       let B := var 3
       let M := var 4
       let e := var 5
       (source z R B ⋏ source z S B ⋏ le e (previous M)) ⟶
         crossEquivalent F F (fd z (R+one) B M e) (fd z (S+one) B M e)) :=
  closeUniv 6 (.impI (retained_cross _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorAllOrderRadius
