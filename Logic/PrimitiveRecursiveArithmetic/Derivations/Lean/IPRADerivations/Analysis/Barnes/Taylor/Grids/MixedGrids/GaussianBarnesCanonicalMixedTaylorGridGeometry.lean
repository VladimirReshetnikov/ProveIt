import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorGridObservations
import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalFiniteTaylorEvenGridComparison

/-!
# Center both mixed Barnes grids at the original numerator

The backward grid starting at the shifted center uses the native
displacement (h+j(-h)). Its code and its exact rational grid point
agree with those used by the original Barnes observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalMixedTaylorGridGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded bounded_add bounded_mono bounded_neg bounded_scale code im re scale)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinalData)
open GaussianBarnesCanonicalFiniteTaylorEvenGridComparison (native_negative)
open GaussianBarnesCanonicalFiniteTaylorGrid (scale_step displacement_point)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianPolynomialForwardDifferenceGrid (point)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents qadd_canonical qadd_represents qzero)
open GaussianRationalMetric (qnegative)
open GaussianRationalNaturalScale (natScale_congr)
open GaussianRationalSyntheticDivision (qadd_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "gneg" => ComplexLogarithmRemainder.neg

def backwardDisplacement (h j : PTm n) : PTm n := add h (scale j (gneg h))

@[simp] theorem subst_backwardDisplacement {l : ℕ} (σ : Fin n → PTm l) (h j : PTm n) :
    Syn.subst σ (backwardDisplacement h j) = backwardDisplacement (Syn.subst σ h) (Syn.subst σ j) :=
  by simp [backwardDisplacement]

private theorem coordinates (x y : ZT n) :
    (Γ ⊢[PRAAx] (re (code x y)).pos ≐ x.pos) ∧ (Γ ⊢[PRAAx] (re (code x y)).neg ≐ x.neg) ∧
      (Γ ⊢[PRAAx] (im (code x y)).pos ≐ y.pos) ∧ (Γ ⊢[PRAAx] (im (code x y)).neg ≐ y.neg) :=
  ⟨(congrFst (fst_pair _ _)).eqTrans (fst_pair _ _), (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _),
    (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _), (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)⟩

theorem native_associative (a b c : PTm n) : Γ ⊢[PRAAx] add (add a b) c ≐ add a (add b c) := by
  have x := coordinates (Γ := Γ) (re a+re b) (im a+im b)
  have y := coordinates (Γ := Γ) (re b+re c) (im b+im c)
  refine Common.congrPairT (Common.congrPairT ?_ ?_) (Common.congrPairT ?_ ?_)
  · exact (congrAdd x.1 (.eqRefl _)).eqTrans
      ((add_assoc _ _ _).eqTrans (congrAdd (.eqRefl _) y.1.eqSymm))
  · exact (congrAdd x.2.1 (.eqRefl _)).eqTrans
      ((add_assoc _ _ _).eqTrans (congrAdd (.eqRefl _) y.2.1.eqSymm))
  · exact (congrAdd x.2.2.1 (.eqRefl _)).eqTrans
      ((add_assoc _ _ _).eqTrans (congrAdd (.eqRefl _) y.2.2.1.eqSymm))
  · exact (congrAdd x.2.2.2 (.eqRefl _)).eqTrans
      ((add_assoc _ _ _).eqTrans (congrAdd (.eqRefl _) y.2.2.2.eqSymm))

theorem fraction_add (a b B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (add a b) B ≐ GaussianRationalHorner.qadd (ofGaussian a B) (ofGaussian b B) :=
  canonical_unique _ _ (add a b) B (ofGaussian_canonical _ _ hB) (qadd_canonical _ _) hB
    (ofGaussian_represents _ _ hB)
    (qadd_represents _ _ _ _ B hB (ofGaussian_represents a B hB) (ofGaussian_represents b B hB))

theorem forward_point (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (scale j h) B ≐ point qzero (ofGaussian h B) j :=
  displacement_point h B j hB

theorem backward_point (h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (backwardDisplacement h j) B ≐ point (ofGaussian h B) (qnegative (ofGaussian h B)) j :=
  (fraction_add h (scale j (gneg h)) B hB).eqTrans
    (qadd_congr (.eqRefl _)
      ((scale_step (gneg h) B j hB).eqTrans (natScale_congr (.eqRefl _) (native_negative h B hB))))

theorem backward_data (z h R B j : PTm n) :
    Γ ⊢[PRAAx] cofinalData (add z h) (gneg h) R B j ≐
      GaussianBarnesCanonicalValue.data (add z (backwardDisplacement h j)) (R+one) B := by
  ipra_congr (GaussianBarnesCanonicalValue.data (var 0) (var 1) (var 2) : PTm 3)
    with [native_associative z h (scale j (gneg h)), .eqRefl (R+one), .eqRefl B] using [cofinalData,backwardDisplacement]

theorem forward_bound (h H N j : PTm n) (hh : Γ ⊢[PRAAx] bounded h H) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] bounded (scale j h) (N*(two*H)) := by
  have widen : Γ ⊢[PRAAx] le H (two*H) := le_of_eq_add (d := H) (by ipra_ring)
  exact GaussianBarnesCanonicalFiniteTaylorGrid.step_bound h (two*H) N j (bounded_mono hh widen) hj

theorem backward_bound (h H N j : PTm n) (hh : Γ ⊢[PRAAx] bounded h H)
    (hn : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] bounded (backwardDisplacement h j) (N*(two*H)) := by
  have widen : Γ ⊢[PRAAx] le (H+j*H) (N*(two*H)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (Common.add_le_add (mul_le_mul_right H hn) (mul_le_mul_right H hj))
  exact bounded_mono (bounded_add hh (bounded_scale j (bounded_neg hh))) widen

theorem admitted_node (z δ R B H : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hδ : Γ ⊢[PRAAx] bounded δ H) (hs : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] source (add z δ) (R+one) B :=
  .andI hz.andE₁ (bounded_mono (bounded_add hz.andE₂ (bounded_mono hδ hs)) (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)))

theorem actual_Barnes_mixed_grid_rational_nodes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let j := var 4
     le one B ⟶
       (ofGaussian (backwardDisplacement h j) B ≐ point (ofGaussian h B) (qnegative (ofGaussian h B)) j) ⋏
       (cofinalData (add z h) (gneg h) R B j ≐ GaussianBarnesCanonicalValue.data (add z (backwardDisplacement h j)) (R+one) B)) :=
  closeUniv 5 (.impI (.andI (backward_point _ _ _ Prf.hyp0) (backward_data _ _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalMixedTaylorGridGeometry
