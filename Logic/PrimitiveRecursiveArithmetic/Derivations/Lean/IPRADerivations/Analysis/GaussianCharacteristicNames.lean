import IPRADerivations.Analysis.GaussianMatrixNames
import IPRADerivations.Analysis.GaussianCharacteristicPrecisionShift
import IPRADerivations.Core.CongruenceTactic

/-!
# Regular names for the actual characteristic coefficients

The degree is packed with the original matrix data for the PR3 coefficient
interface. Each sample reads the actual characteristic-polynomial buffer at
the shifted entry precision. The numerical exponent is translated to its
descending coefficient slot. Source matrix regularity proves the precise
Euclidean coefficient-name contract.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianMatrixNames (sample B)
open GaussianCharacteristicPrecisionShift (clock characteristic_shifted_distance)
open GaussianCoefficientNameBounds (unit regularCoefficient)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def samplePolynomial (a : PR 4) (N s x : PTm n) : PTm n :=
  GaussianRationalCharacteristicPolynomial.run (sample a N (s+clock N (B a N x)) x) N

def coefficient (a : PR 4) (N k s x : PTm n) : PTm n := entry (samplePolynomial a N s x) (monus N k)

def coefficientBody (a : PR 4) : PTm 3 := coefficient a (fstT (var 2)) (var 0) (var 1) (sndT (var 2))
def coefficientF (a : PR 4) : PR 3 := PTm.toPR (coefficientBody a)

@[simp] theorem subst_samplePolynomial {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N s x : PTm n) :
    Syn.subst σ (samplePolynomial a N s x) =
      samplePolynomial a (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ x) := by simp [samplePolynomial]

@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N k s x : PTm n) :
    Syn.subst σ (coefficient a N k s x) =
      coefficient a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ s) (Syn.subst σ x) := by simp [coefficient]

theorem coefficient_congr (a : PR 4) {N N' k k' s s' x x' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hk : Γ ⊢[PRAAx] k ≐ k')
    (hs : Γ ⊢[PRAAx] s ≐ s') (hx : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] coefficient a N k s x ≐ coefficient a N' k' s' x' := by
  ipra_congr (coefficient a (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hN, hk, hs, hx]

theorem coefficient_at (a : PR 4) (N k s x : PTm n) : Γ ⊢[PRAAx]
    ap3 (coefficientF a) k s (pairT N x) ≐ coefficient a N k s x := by
  have eq : Γ ⊢[PRAAx] ap3 (coefficientF a) k s (pairT N x) ≐
      coefficient a (fstT (pairT N x)) k s (sndT (pairT N x)) := by
    simpa [coefficientF,coefficientBody,ap3] using toPR_eq (Γ := Γ) (coefficientBody a) ![k,s,pairT N x]
  exact eq.eqTrans (coefficient_congr a (fst_pair _ _) (.eqRefl _) (.eqRefl _) (snd_pair _ _))

theorem original_coefficient_regular (a : PR 4) (N k s t x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] distanceBounded (coefficient a N k s x) (coefficient a N k t x) (unit s+unit t) (unit s*unit t) := by
  let c := clock N (B a N x)
  have matrix := GaussianMatrixNames.sample_pair_input a N (s+c) (t+c) x h
  have slot := GaussianMonicResidualRadius.monus_le_left (Γ := Γ) N k
  have error := GaussianCharacteristicSensitivity.returned_coefficient_error _ _ _ _ _ _ (monus N k) matrix slot
  exact characteristic_shifted_distance _ _ N (B a N x) s t error

theorem program_coefficient_regular (a : PR 4) (N k s t x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] distanceBounded (ap3 (coefficientF a) k s (pairT N x)) (ap3 (coefficientF a) k t (pairT N x))
      (unit s+unit t) (unit s*unit t) :=
  distance_congr (coefficient_at a N k s x).eqSymm (coefficient_at a N k t x).eqSymm
    (.eqRefl _) (.eqRefl _) (original_coefficient_regular a N k s t x h)

theorem coefficient_regular (a : PR 4) (N k x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] regularCoefficient (coefficientF a) k (pairT N x) := by
  refine .allI (.allI ?_)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianMatrixNames.CN a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa [regularCoefficient,Syn.shift] using
    program_coefficient_regular a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift k)) (var 1) (var 0)
      (Syn.shift (Syn.shift x)) h'

theorem coefficient_name (a : PR 4) (N x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] GaussianCoefficientNameBounds.CN (coefficientF a) N (pairT N x) := by
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] GaussianMatrixNames.CN a (Syn.shift N) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [Syn.shift] using coefficient_regular a (Syn.shift N) (var 0) (Syn.shift x) h'.wk

theorem leading_coefficient (a : PR 4) (N s x : PTm n) : Γ ⊢[PRAAx]
    coefficient a N N s x ≐ GaussianRationalSyntheticDivision.qone :=
  (Foundations.SequenceComposition.entry_congr (.eqRefl _) (monus_self N)).eqTrans
    (GaussianRationalCharacteristicPolynomial.returned_monic _ _)

theorem actual_characteristic_coefficient_program_closed (a : PR 4) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (ap3 (coefficientF a) (var 1) (var 2) (pairT (var 0) (var 3)) ≐ coefficient a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (coefficient_at a _ _ _ _)

theorem actual_characteristic_name_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianMatrixNames.CN a (var 0) (var 1) ⟶ GaussianCoefficientNameBounds.CN
      (coefficientF a) (var 0) (pairT (var 0) (var 1))) :=
  closeUniv 2 (.impI (coefficient_name a _ _ Prf.hyp0))

theorem actual_shifted_leading_coefficient_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (coefficient a (var 0) (var 0) (var 1) (var 2) ≐ GaussianRationalSyntheticDivision.qone) :=
  closeUniv 3 (leading_coefficient a _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCharacteristicNames
