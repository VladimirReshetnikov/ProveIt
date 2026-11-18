import IPRADerivations.Analysis.GaussianGeneralPolynomialSamples
import IPRADerivations.Analysis.GaussianCoefficientNormOrder

/-!
# Exact constant names for a numerical Gaussian-rational polynomial

A single fixed PR3 program reads the original descending coefficient list
from numerical persistent data and ignores the query precision. Its general
coefficient-name contract is proved, including zero leading coefficients
and raw noncanonical entries. A nonzero coefficient supplies its own
computed dyadic apartness precision; neither coherence nor an apartness
test is an input to the resulting general FTA source contract.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianConstantCoefficientNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (coefficient numerator)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN apart)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded qnormSq squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (C N : PTm n) : PTm n := pairT N C
def coefficientBody : PTm 3 := entry (sndT (var 2)) (PTm.monus (fstT (var 2)) (var 0))
def coefficientF : PR 3 := PTm.toPR coefficientBody
def apartPrecision (C N k : PTm n) : PTm n :=
  GaussianRootSchedule.binaryLength (rawDen (coefficient C N k))

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (data C N) = data (Syn.subst σ C) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_apartPrecision {m : ℕ} (σ : Fin n → PTm m) (C N k : PTm n) :
    Syn.subst σ (apartPrecision C N k) =
      apartPrecision (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ k) := by simp [apartPrecision]

theorem coefficient_at (C N k s : PTm n) : Γ ⊢[PRAAx]
    ap3 coefficientF k s (data C N) ≐ coefficient C N k := by
  have h := toPR_eq (Γ := Γ) coefficientBody ![k,s,data C N]
  have e : Syn.subst ![k,s,data C N] coefficientBody =
      entry (sndT (data C N)) (PTm.monus (fstT (data C N)) k) := by simp [coefficientBody]
  rw [e] at h
  exact h.eqTrans (Foundations.SequenceComposition.entry_congr (snd_pair _ _)
    (congrMonus (fst_pair _ _) (.eqRefl _)))

theorem coefficient_coherence (C N k s t : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap3 coefficientF k s (data C N)) (ap3 coefficientF k t (data C N))
      (unit s+unit t) (unit s*unit t) := by
  have h := GaussianRationalReciprocal.bound_congr (Γ := Γ)
    (GaussianCoefficientNormOrder.qsub_self (coefficient C N k)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded (unit s+unit t) (unit s*unit t)
      (positive_product _ _ (unit_positive s) (unit_positive t)))
  exact distance_congr (coefficient_at C N k s).eqSymm (coefficient_at C N k t).eqSymm
    (.eqRefl _) (.eqRefl _) h

theorem constant_names (C N : PTm n) : Γ ⊢[PRAAx] generalCN coefficientF N (data C N) := by
  refine .allI (.impI (.allI (.allI ?_)))
  simpa [generalCN,GaussianCoefficientNameBounds.CN,GaussianCoefficientNameBounds.regularCoefficient,
    Syn.shift] using
    (coefficient_coherence (Γ := ((Γ.map Fm.shift).map Fm.shift).map Fm.shift)
      (Syn.shift (Syn.shift (Syn.shift C))) (Syn.shift (Syn.shift (Syn.shift N)))
      (var 2) (var 1) (var 0)).wk

theorem denominator_budget (C N k : PTm n) : Γ ⊢[PRAAx]
    le (rawDen (coefficient C N k)) (unit (apartPrecision C N k)) :=
  Prf.andE₁ (GaussianRootSchedule.binary_length_correct _)

theorem coefficient_apart (C N k : PTm n) (hNorm : Γ ⊢[PRAAx] le one (numerator C N k)) : Γ ⊢[PRAAx]
    apart coefficientF k (apartPrecision C N k) (data C N) := by
  have hD := raw_den_positive (Γ := Γ) (coefficient C N k)
  have hU := unit_positive (Γ := Γ) (apartPrecision C N k)
  have first := le_mul_mono (denominator_budget (Γ := Γ) C N k) (denominator_budget (Γ := Γ) C N k)
  have second := le_congr (one_mul _) (.eqRefl _)
    (le_mul_mono hNorm (le_refl (unit (apartPrecision C N k)*unit (apartPrecision C N k))))
  have lower := le_trans first second
  have bound := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ hU hU) (positive_product _ _ hD hD)
    (GaussianRationalMetric.squared_tolerance_represents one (unit (apartPrecision C N k)) hU)
    (GaussianRationalMetric.qnormSq_represents (coefficient C N k) (rawGaussian (coefficient C N k))
      (rawDen (coefficient C N k)) hD (raw_represents _))
    (le_congr (by ipra_ring) (.eqRefl _) lower)
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (GaussianRationalProductWitness.qnormSq_congr
      (coefficient_at C N k (GaussianGeneralCoefficientNames.referencePrecision (apartPrecision C N k))).eqSymm) bound

theorem source_input (C N k : PTm n) (hk1 : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) (hNorm : Γ ⊢[PRAAx] le one (numerator C N k)) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialSamples.sourceInput coefficientF N k (apartPrecision C N k) (data C N) :=
  .andI (constant_names C N) (.andI hk1 (.andI hkN (coefficient_apart C N k hNorm)))

theorem exact_constant_coefficient_names_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (generalCN coefficientF (var 1) (data (var 0) (var 1))) := closeUniv 2 (constant_names _ _)

theorem actual_constant_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap3 coefficientF (var 2) (var 3) (data (var 0) (var 1)) ≐ coefficient (var 0) (var 1) (var 2)) :=
  closeUniv 4 (coefficient_at _ _ _ _)

theorem constant_polynomial_source_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (var 2) (var 1) ⟶ le one (numerator (var 0) (var 1) (var 2)) ⟶
      GaussianGeneralPolynomialSamples.sourceInput coefficientF (var 1) (var 2)
        (apartPrecision (var 0) (var 1) (var 2)) (data (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (.impI (source_input _ _ _ (Prf.wk Prf.hyp1) Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianConstantCoefficientNames
