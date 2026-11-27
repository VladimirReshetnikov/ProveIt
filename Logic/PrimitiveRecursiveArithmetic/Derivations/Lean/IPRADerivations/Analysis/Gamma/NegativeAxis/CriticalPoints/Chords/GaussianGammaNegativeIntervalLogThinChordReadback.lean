import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.Chords.GaussianGammaNegativeIntervalLogThinChord
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScaleOrder

/-!
# Finite observations of the negative thin chord

A common original observation clock gives the chord in differences from
the base. The finite error accounts for the actual addition and scaling
programs and has a numerator fixed before the clock is chosen.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogThinChordReadback

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData name_regular name_real)
open GaussianGammaNegativeIntervalLogThinChord (centerData margin center_regular strong_chord)
open GaussianNamedNaturalScaleOrder (cost weighted_chord_difference_at)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (qsub)
open GaussianRationalNaturalScale (natScale)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => nameF

def budget (a c b N W : PTm n) : PTm n :=
  cost G W (centerData a c b N W)+cost G (pred W) (nameData a b N)+num 8

ipra_subst budget

theorem difference_at (p a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hW : Γ ⊢[PRAAx] le two W) :
    Γ ⊢[PRAAx] upper
      (fstT (qadd (margin a c b) (natScale W (qsub (ap2 G p (centerData a c b N W)) (ap2 G p (nameData a b N))))))
      (fstT (qsub (ap2 G p (nameData c b N)) (ap2 G p (nameData a b N)))) (budget a c b N W) (unit p) := by
  have canX := (GaussianSignedNameExponentialOrder.real_sample_at G (nameData a b N) p
    (name_real (Γ := Γ) a b N)).andE₁
  have canY := (GaussianSignedNameExponentialOrder.real_sample_at G (nameData c b N) p
    (name_real (Γ := Γ) c b N)).andE₁
  exact weighted_chord_difference_at G p (margin a c b) W (nameData a b N) (nameData c b N)
    (centerData a c b N W) (le_trans RationalAlgebra.two_positive hW)
    (name_regular a b N ha) (name_regular c b N hc) (center_regular a c b N W ha hc hW)
    canX canY (strong_chord a c b N W ha hc hW)

theorem actual_negative_interval_log_absolute_thin_chord_difference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 1) (var 3) ⋏ (guard (var 2) (var 3) ⋏ le two (var 5))) ⟶
        upper
          (fstT (qadd (margin (var 1) (var 2) (var 3)) (natScale (var 5)
            (qsub (ap2 G (var 0) (centerData (var 1) (var 2) (var 3) (var 4) (var 5)))
              (ap2 G (var 0) (nameData (var 1) (var 3) (var 4)))))))
          (fstT (qsub (ap2 G (var 0) (nameData (var 2) (var 3) (var 4)))
            (ap2 G (var 0) (nameData (var 1) (var 3) (var 4)))))
          (budget (var 1) (var 2) (var 3) (var 4) (var 5)) (unit (var 0))) :=
  closeUniv 6 (.impI (difference_at _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogThinChordReadback
