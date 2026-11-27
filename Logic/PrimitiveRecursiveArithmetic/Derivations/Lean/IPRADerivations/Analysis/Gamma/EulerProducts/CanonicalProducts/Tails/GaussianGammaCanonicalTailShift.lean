import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalTailMetric

/-!
# The actual named first-factor shift of the canonical Gamma tail

The local name uses the ORIGINAL GammaLocalFactorName observations. The
successor tail uses the ORIGINAL GammaCanonicalNames observations, and the
sum is the actual verified Gaussian name-addition program with its own
retiming and normalization. The source half-disk guard derives regularity
of each name and their genuine independent-precision equivalence.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailShift

open_ipra
open GaussianRationalHorner (ofGaussian qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalTailMetric (localValue ofGaussian_congr)
open GaussianGammaCanonicalTailName (source)
open GaussianNameEquivalence (diagonalEquivalent crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def localData (z R D : PTm n) : PTm n := pairT z (pairT R D)
def localTerm (p x : PTm n) : PTm n := localValue p (fstT x) (fstT (sndT x)) (sndT (sndT x))
def localF : PR 2 := PTm.toPR (localTerm (var 0) (var 1))
def localPoint (p z R D : PTm n) : PTm n := ap2 localF p (localData z R D)
ipra_subst localData
ipra_subst localTerm
ipra_subst localPoint

theorem local_at (p z R D : PTm n) : Γ ⊢[PRAAx] localPoint p z R D ≐ localValue p z R D := by
  simpa [localPoint, localF, localTerm, localData, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (localValue (var 0) (var 1) (var 2) (var 3)) p ![z, R, D])

/-- The original independently rounded local-factor observations already
have the correct two-precision Gaussian regularity. -/
theorem local_regularity (s t z R D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R)
    (hHalf : Γ ⊢[PRAAx] le (two*R) D) : Γ ⊢[PRAAx]
    distanceBounded (localPoint s z R D) (localPoint t z R D)
      (unit s+unit t) (unit s*unit t) := by
  have raw := GammaLocalFactorName.regular_pair t s z R D hD hz hHalf
  have metric := GaussianGammaCanonicalTailMetric.distance_of_cross _ _ _ _
    (unit t+unit s) (unit t*unit s)
    (GaussianLocalLogarithmName.unit_positive t) (GaussianLocalLogarithmName.unit_positive s)
    (positive_product _ _ (unit_positive t) (unit_positive s))
    (le_congr (.eqRefl _) (by unfold unit; ipra_ring) raw)
  exact distance_congr (local_at s z R D).eqSymm (local_at t z R D).eqSymm
    (by ipra_ring) (by ipra_ring) metric

theorem local_name_regular (z R D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R)
    (hHalf : Γ ⊢[PRAAx] le (two*R) D) : Γ ⊢[PRAAx] pointCN localF (localData z R D) := by
  refine .allI (.allI ?_)
  have hd : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift D)) := by
    simpa [Fm.shift,Syn.shift] using hD.shift.shift
  have hz' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      ComplexLogarithmRemainder.bounded (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) := by
    simpa [Fm.shift,Syn.shift] using hz.shift.shift
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      le (two*Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift D)) := by
    simpa [Fm.shift,Syn.shift] using hHalf.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,localPoint,Syn.shift,subst_localData] using
    local_regularity (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift D)) hd hz' hh

def shiftF : PR 2 := GaussianNameArithmetic.addF localF GaussianGammaCanonicalTailName.pointF
def shiftData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.addData
  (localData z (R*B) (B*succ N)) (GaussianGammaCanonicalTailName.data z R B (succ N))
def shifted (p z R B N : PTm n) : PTm n := ap2 shiftF p (shiftData z R B N)
ipra_subst shiftData
ipra_subst shifted

/-- Literal observation of the actual add-name program, including its
normalization; the summed Gaussian code is canonical by construction. -/
theorem shifted_at (p z R B N : PTm n) : Γ ⊢[PRAAx] shifted p z R B N ≐
    qadd (localValue (GaussianFastValueCut.exponent two p) z (R*B) (B*succ N))
      (GaussianGammaCanonicalTailName.point (GaussianFastValueCut.exponent two p) z R B (succ N)) := by
  have e := GaussianNameArithmetic.add_at (Γ := Γ) localF GaussianGammaCanonicalTailName.pointF
    (localData z (R*B) (B*succ N)) (GaussianGammaCanonicalTailName.data z R B (succ N)) p
  let q := qadd (localValue (GaussianFastValueCut.exponent two p) z (R*B) (B*succ N))
    (GaussianGammaCanonicalTailName.point (GaussianFastValueCut.exponent two p) z R B (succ N))
  have normalized : Γ ⊢[PRAAx] GaussianFastValueCut.recode q ≐ q :=
    GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical q)
      (GaussianRationalHorner.qadd_canonical _ _) (GaussianRationalL1.raw_den_positive q)
      (GaussianFastValueCut.recode_represents q) (GaussianRationalL1.raw_represents q)
  exact e.eqTrans ((GaussianNameArithmetic.recode_congr
    (GaussianRationalSyntheticDivision.qadd_congr (local_at _ _ _ _) (.eqRefl _))).eqTrans normalized)

theorem shift_name_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN shiftF (shiftData z R B N) :=
  GaussianNameArithmetic.add_fast _ _ _ _
    (local_name_regular z (R*B) (B*succ N) (positive_product _ _ h.andE₁ (zero_lt_succ N))
      h.andE₂.andE₂.andE₁ (GaussianGammaCanonicalTailMetric.source_local_half z R B N h))
    (GaussianGammaCanonicalTailName.name_regular z R B (succ N)
      (GaussianGammaCanonicalTailMetric.source_successor z R B N h))

/-- The actual add-name retiming preserves the error budget required for
diagonal equivalence to the ORIGINAL tail name. -/
theorem shifted_distance (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (GaussianGammaCanonicalTailName.point p z R B N)
      (shifted p z R B N) two (unit p) := by
  let s := GaussianFastValueCut.exponent two p
  have hp : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have regular : Γ ⊢[PRAAx] distanceBounded (GaussianGammaCanonicalTailName.point p z R B N)
      (GaussianGammaCanonicalTailName.point s z R B N) one (unit p) :=
    distance_congr (GaussianGammaCanonicalTailName.point_at p z R B N).eqSymm
      (GaussianGammaCanonicalTailName.point_at s z R B N).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_symmetric _ _ _ _ (unit_positive p)
        (GaussianGammaCanonicalTailName.later_distance p s z R B N h hp))
  have growth := GaussianFactorBudget.power_monotone_length two p s (le_succ_self one) hp
  have budget : Γ ⊢[PRAAx] le (num 8*unit p) (one*DyadicComplexLogarithm.unit s) := by
    have weak : Γ ⊢[PRAAx] le (num 8*unit p) (num 16*unit s) :=
      le_trans (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (num 8)) growth)
        (le_of_eq_add (d := num 8*unit s) (by unfold unit; ipra_ring))
    exact le_congr (.eqRefl _)
      ((show Γ ⊢[PRAAx] num 16*unit s ≐ unit s*num 16 by ipra_ring).eqTrans
        ((GaussianLocalLogarithmName.unit_factor s).eqSymm.eqTrans (by ipra_ring))) weak
  have shiftedError := distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive s)
    (unit_positive p) budget (GaussianGammaCanonicalTailMetric.same_query_shift s z R B N h)
  exact distance_congr (.eqRefl _) (shifted_at p z R B N).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) regular shiftedError)

theorem tail_shift_diagonal (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] diagonalEquivalent GaussianGammaCanonicalTailName.pointF shiftF
      (GaussianGammaCanonicalTailName.data z R B N) (shiftData z R B N) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [diagonalEquivalent,GaussianGammaCanonicalTailName.point,shifted,Syn.shift,
    GaussianGammaCanonicalTailName.subst_data,subst_shiftData] using
    shifted_distance (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

/-- Genuine independent-precision C8 equivalence of the original tail and
the actual sum of the original local factor and successor tail names. -/
theorem tail_shift_equivalent (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGammaCanonicalTailName.pointF shiftF
      (GaussianGammaCanonicalTailName.data z R B N) (shiftData z R B N) :=
  GaussianNameEquivalence.diagonal_to_cross _ _ _ _
    (GaussianGammaCanonicalTailName.name_regular z R B N h) (shift_name_regular z R B N h)
    (tail_shift_diagonal z R B N h)

/-! The actual fixed-arity supplier returns the two persistent name data. -/
def output (z R B N : PTm n) : PTm n := pairT
  (GaussianGammaCanonicalTailName.data z R B N) (shiftData z R B N)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z R B N : PTm n) : PTm n := PTm.app outputF ![z,R,B,N]
ipra_subst output
ipra_subst run
theorem program_at (z R B N : PTm n) : Γ ⊢[PRAAx] run z R B N ≐ output z R B N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,R,B,N]
theorem returned_tail_data (z R B N : PTm n) : Γ ⊢[PRAAx]
    fstT (run z R B N) ≐ GaussianGammaCanonicalTailName.data z R B N :=
  (program_at _ _ _ _).fstE
theorem returned_sum_data (z R B N : PTm n) : Γ ⊢[PRAAx] sndT (run z R B N) ≐ shiftData z R B N :=
  (program_at _ _ _ _).sndE

theorem returned_equivalence (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGammaCanonicalTailName.pointF shiftF
      (fstT (run z R B N)) (sndT (run z R B N)) :=
  GaussianNameEquivalence.cross_data_congr _ _ _ _ _ _
    (returned_tail_data z R B N).eqSymm (returned_sum_data z R B N).eqSymm (tail_shift_equivalent z R B N h)

theorem actual_original_local_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (localPoint (var 0) (var 1) (var 2) (var 3) ≐ ofGaussian
      (GammaLocalFactorName.observation (var 0) (var 1) (var 2) (var 3)) (DyadicComplexLogarithm.unit (var 0))) :=
  closeUniv 4 (local_at _ _ _ _)
theorem source_local_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1) ⟶
      le (two*var 1) (var 2) ⟶ pointCN localF (localData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (local_name_regular _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_tail_shift_add_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shifted (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      qadd (localValue (GaussianFastValueCut.exponent two (var 0)) (var 1) (var 2*var 3) (var 3*succ (var 4)))
        (GaussianGammaCanonicalTailName.point (GaussianFastValueCut.exponent two (var 0))
          (var 1) (var 2) (var 3) (succ (var 4)))) := closeUniv 5 (shifted_at _ _ _ _ _)
theorem source_tail_shift_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN shiftF (shiftData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (shift_name_regular _ _ _ _ Prf.hyp0))
theorem source_tail_shift_diagonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ diagonalEquivalent GaussianGammaCanonicalTailName.pointF shiftF
      (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (var 3))
      (shiftData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (tail_shift_diagonal _ _ _ _ Prf.hyp0))
theorem source_tail_shift_cross_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent GaussianGammaCanonicalTailName.pointF shiftF
      (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (var 3))
      (shiftData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (tail_shift_equivalent _ _ _ _ Prf.hyp0))
theorem actual_tail_shift_supplier_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_tail_shift_returned_data_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (var 3)) ⋏
      (sndT (run (var 0) (var 1) (var 2) (var 3)) ≐ shiftData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (returned_tail_data _ _ _ _) (returned_sum_data _ _ _ _))
theorem source_returned_tail_shift_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent GaussianGammaCanonicalTailName.pointF shiftF
      (fstT (run (var 0) (var 1) (var 2) (var 3))) (sndT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (returned_equivalence _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailShift
