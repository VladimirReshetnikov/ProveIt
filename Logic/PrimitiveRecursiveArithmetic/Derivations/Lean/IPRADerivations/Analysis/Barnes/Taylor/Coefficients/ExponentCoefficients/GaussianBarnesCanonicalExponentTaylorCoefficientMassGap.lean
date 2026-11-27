import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorRetainedCoefficient
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientUniformNorm

/-!
# Coefficient mass of two retained Barnes exponent buffers

At a common degree the original descending slots have the same exponent.
The uniform Cauchy estimate bounds the coefficient-L1 norm of their actual
buffer difference, as required for finite exponential coefficient variation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorCoefficientMassGap

open_ipra
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (late_entry_gap prefactorGain cutoff)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientL1 (coefficientNorm subCoefficients)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCoefficientUniformNorm (difference_uniform_of_degree_bounds)
open GaussianEuclideanDistanceName (fraction)
open RationalArgmin (rationalLE rationalLE_congr)

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

theorem late_mass_gap (p q t z R B r s M : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hq : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit q))
    (ht : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit t))
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (hs : Γ ⊢[PRAAx] le (cutoff p R M) s) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (difference q t z R B r s M)) (massError p M) := by
  have raw : Γ ⊢[PRAAx] rationalLE (coefficientNorm (difference q t z R B r s M))
      (fraction (succ (previous M)*(two*num 4)) (unit p)) := by
    refine difference_uniform_of_degree_bounds (buffer q z R B r M) (buffer t z R B s M)
      (previous M) (num 4) (unit p) (unit_positive p) ?_
    intro sh Δ e he
    have hz : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
    have shift_clock {w : PTm n} (hw : Γ ⊢[PRAAx] le (prefactorGain R*unit p) (unit w)) :
        Δ ⊢[PRAAx] le (prefactorGain (sh R)*unit (sh p)) (unit (sh w)) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,prefactorGain,GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.linearGain,
        GaussianBarnesCanonicalPrefactorLipschitz.halfGain,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two] using hw.shift.wk
    have shift_cutoff {w : PTm n} (hw : Γ ⊢[PRAAx] le (cutoff p R M) w) :
        Δ ⊢[PRAAx] le (cutoff (sh p) (sh R) (sh M)) (sh w) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,cutoff,GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.tailGain,two] using hw.shift.wk
    simpa only [Δ,sh,Syn.shift,GaussianBarnesCanonicalExponentTaylorCoefficientCauchy.stored,
      GaussianBarnesCanonicalExponentTaylorBuffer.subst_buffer,GaussianBarnesCanonicalHigherRows.subst_previous,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_num] using
      late_entry_gap (sh p) (sh q) (sh t) (sh z) (sh R) (sh B) (sh r) (sh s) (sh M) (sh M) e
        hz he he (shift_clock hq) (shift_clock ht) (shift_cutoff hr) (shift_cutoff hs)
  exact rationalLE_congr (.eqRefl _)
    (RationalNonnegativePowers.fraction_congr (by ipra_ring) (.eqRefl _)) raw

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorCoefficientMassGap
