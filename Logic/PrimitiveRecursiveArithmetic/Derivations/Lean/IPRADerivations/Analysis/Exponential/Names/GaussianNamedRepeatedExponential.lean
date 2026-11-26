import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedRepeatedProduct
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponentialSample
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# The exponential of a natural multiple as a named product

The checked bounded integer-exponential recurrence identifies the
actual finite product of repeated exponential observations with
the exponential of the scaled input. Both sides retain their own
primitive recursive sampling programs and query clocks.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRepeatedExponential

open_ipra
open GaussianBoundedIntegerExponentialStages (expF expData point majorant)
open GaussianBoundedIntegerExponentialSample (stage_input point_bound prefix_error sampleBudget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (cross_of_diagonal_rate diagonalRate)
open GaussianNamedFiniteProductName (nameF data modulus rawF rawData raw_at raw_regular name_regular)
open GaussianNamedRepeatedProduct (repeatF bounds sample_power repeated_row_bounds repeated_row_regular)
open GaussianRadiusExponentialName (input)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def repeatedData (N E R x : PTm n) : PTm n := data N (majorant E R) one (expData E one R x)

ipra_subst repeatedData [one]

def budget (N E R : PTm n) : PTm n :=
  sampleBudget E N R (majorant E R) zero+(modulus N (majorant E R) one+one)

ipra_subst budget [one]

theorem exponential_bounds (f : PR 2) (E R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] bounds (expF f) (majorant E R) (expData E one R x) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh := fun t : PTm n => Syn.shift t
  have hF : Δ ⊢[PRAAx] input f (sh R) (sh x) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hf.shift
  have he : Δ ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hE.shift
  simpa [bounds,point,Syn.shift,Δ,sh,one] using point_bound f (var 0) (sh E) one (sh R) (sh x) hF he

theorem repeated_at (f : PR 2) (p N E R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le N E) : Γ ⊢[PRAAx]
    distanceBounded (point f p E N R x) (ap2 (nameF (repeatF (expF f))) p (repeatedData N E R x))
      (budget N E R) (unit p) := by
  let g := expF f
  let c := expData E one R x
  let F := repeatF g
  let S := majorant E R
  let A := sampleBudget E N R S zero
  let L := modulus N S one
  let D := rawData N c
  let hp := unit_positive (Γ := Γ) p
  have hg := GaussianRadiusExponentialName.name_regular _ _ _ (stage_input f E one R x hf hE)
  have hb := repeated_row_bounds g N S c (exponential_bounds f E R x hf hE)
  have hr := repeated_row_regular g N c hg
  have e := prefix_error f p E N R x (point f p E one R x) S zero hf
    (point_bound f p E one R x hf hE) (distance_refl_zero _ _ hp) hN
  have folded := (raw_at (Γ := Γ) F p N c).eqTrans (sample_power g p N c)
  have near : Γ ⊢[PRAAx] distanceBounded (point f p E N R x) (ap2 (rawF F) p D) A (unit p) :=
    distance_congr (.eqRefl _) folded.eqSymm (.eqRefl _) (.eqRefl _) e
  have fin := GaussianNameRingLaws.normalized_to_sample (rawF F) L D p (raw_regular F N S one c hb hr)
  exact distance_triangle_same _ _ _ _ _ _ hp near (distance_symmetric _ _ _ _ hp fin)

theorem repeated_exponential (f : PR 2) (N E R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le N E) :
    Γ ⊢[PRAAx] crossEquivalent (expF f) (nameF (repeatF (expF f))) (expData E N R x) (repeatedData N E R x) := by
  have h0 := GaussianRadiusExponentialName.name_regular _ _ _ (stage_input f E N R x hf hN)
  have g0 := GaussianRadiusExponentialName.name_regular _ _ _ (stage_input f E one R x hf hE)
  have h1 := name_regular (repeatF (expF f)) N (majorant E R) one (expData E one R x)
    (repeated_row_bounds _ _ _ _ (exponential_bounds f E R x hf hE)) (repeated_row_regular _ _ _ g0)
  apply cross_of_diagonal_rate _ _ _ _ (budget N E R) h0 h1
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh := fun t : PTm n => Syn.shift t
  have hf' : Δ ⊢[PRAAx] input f (sh R) (sh x) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hf.shift
  have hE' : Δ ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hE.shift
  have hN' : Δ ⊢[PRAAx] le (sh N) (sh E) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hN.shift
  simpa [diagonalRate,point,expF,expData,repeatedData,Syn.shift,Δ,sh,one] using
    repeated_at f (var 0) (sh N) (sh E) (sh R) (sh x) hf' hE' hN'

theorem actual_repeated_exponential_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 2) (var 3) ⟶ le one (var 1) ⟶ le (var 0) (var 1) ⟶
      crossEquivalent (expF f) (nameF (repeatF (expF f))) (expData (var 1) (var 0) (var 2) (var 3))
        (repeatedData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (repeated_exponential f _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedRepeatedExponential
