import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorRetainedCoefficient
import IPRADerivations.Analysis.Polynomials.GaussianCoefficientUniformNorm
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalL1Algebra

/-!
# Coefficient mass of two retained Barnes exponent buffers

At a common degree the original descending slots have the same exponent.
The uniform Cauchy estimate bounds the coefficient-L1 norm of their actual
buffer difference, as required for finite exponential coefficient variation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorCoefficientMassGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer subst_buffer)
open GaussianBarnesCanonicalExponentTaylorCoefficientCauchy (stored)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (late_entry_gap prefactorGain cutoff)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientL1 (coefficientNorm subCoefficients sub_lookup qL1_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCoefficientUniformNorm (entryBounds coefficient_uniform)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalL1 (qL1)
open GaussianRationalL1Algebra (qL1_of_bounded)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticBounds (natCode)
open GaussianRationalSyntheticDivision (qsub_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def difference (q t z R B r s M : PTm n) : PTm n :=
  subCoefficients (buffer q z R B r M) (buffer t z R B s M) (succ (previous M))

def entryError (p : PTm n) : PTm n := fraction (num 8) (unit p)
def massError (p M : PTm n) : PTm n := fraction (num 8*succ (previous M)) (unit p)

@[simp] theorem subst_difference {l : ℕ} (σ : Fin n → PTm l) (q t z R B r s M : PTm n) :
    Syn.subst σ (difference q t z R B r s M) = difference (Syn.subst σ q) (Syn.subst σ t)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ M) :=
  by simp [difference]

@[simp] theorem subst_entryError {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (entryError p) = entryError (Syn.subst σ p) := by simp [entryError]

private theorem late_slot (p q t z R B r s M i : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hi : Γ ⊢[PRAAx] lt i (succ (previous M)))
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] rationalLE (qL1 (entry (difference q t z R B r s M) i)) (entryError p) := by
  let N := previous M
  let e := monus N i
  let C := buffer q z R B r M
  let D := buffer t z R B s M
  have hi' : Γ ⊢[PRAAx] le i N := (succ_monus_succ i N).eqSymm.eqTrans hi
  have he : Γ ⊢[PRAAx] le e N := GaussianRationalMonicReconstruction.monus_le_left _ _
  have a : Γ ⊢[PRAAx] stored q z R B r M e ≐ entry C i :=
    entry_congr (.eqRefl _) (GaussianRationalMonicReconstruction.complement N i hi')
  have b : Γ ⊢[PRAAx] stored t z R B s M e ≐ entry D i :=
    entry_congr (.eqRefl _) (GaussianRationalMonicReconstruction.complement N i hi')
  have code := (sub_lookup C D (succ N) i hi).eqTrans (qsub_congr a.eqSymm b.eqSymm)
  have near := late_entry_gap p q t z R B r s M M e h he he hq ht hr hs
  have norm := qL1_of_bounded _ (num 4) (unit p) (unit_positive p) near
  exact rationalLE_congr (qL1_congr code).eqSymm
    (RationalNonnegativePowers.fraction_congr (by ipra_ring) (.eqRefl _)) norm

theorem late_mass_gap (p q t z R B r s M : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (difference q t z R B r s M)) (massError p M) := by
  let N := succ (previous M)
  let D := difference q t z R B r s M
  have len : Γ ⊢[PRAAx] length D ≐ N :=
    GaussianRationalMonicCompanion.sub_length _ _ _
  have rows : Γ ⊢[PRAAx] entryBounds D N (entryError p) := by
    refine .allI (.impI ?_)
    let a (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (a N) :: Γ.map Fm.shift
    have hz : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using h.shift.wk
    have hq' : Δ ⊢[PRAAx] le (prefactorGain (a R)*unit (a p)) (unit (a q)) :=
      by simpa [Δ,a,Fm.shift,Syn.shift,prefactorGain,GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,
        GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using hq.shift.wk
    have ht' : Δ ⊢[PRAAx] le (prefactorGain (a R)*unit (a p)) (unit (a t)) :=
      by simpa [Δ,a,Fm.shift,Syn.shift,prefactorGain,GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,
        GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using ht.shift.wk
    have hr' : Δ ⊢[PRAAx] le (cutoff (a p) (a R) (a M)) (a r) :=
      by simpa [Δ,a,Fm.shift,Syn.shift,cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.tailGain,two] using hr.shift.wk
    have hs' : Δ ⊢[PRAAx] le (cutoff (a p) (a R) (a M)) (a s) :=
      by simpa [Δ,a,Fm.shift,Syn.shift,cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.tailGain,two] using hs.shift.wk
    simpa only [Δ,a,D,N,Syn.shift,entryBounds,subst_difference,subst_entryError,
      GaussianBarnesCanonicalHigherRows.subst_previous,ConciseIPRA.PTm.subst_succ] using
      late_slot (a p) (a q) (a t) (a z) (a R) (a B) (a r) (a s) (a M) (var 0) hz Prf.hyp0 hq' ht' hr' hs'
  have norm := coefficient_uniform D N (entryError p) len rows
  have same : Γ ⊢[PRAAx] RationalArithmetic.multiply (natCode N) (entryError p) ≐ massError p M :=
    (RationalNonnegativePowers.fraction_multiply N one (num 8) (unit p) (le_refl one) (unit_positive p)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by dsimp only [N]; ipra_ring) (one_mul _))
  exact rationalLE_congr (.eqRefl _) same norm

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorCoefficientMassGap
