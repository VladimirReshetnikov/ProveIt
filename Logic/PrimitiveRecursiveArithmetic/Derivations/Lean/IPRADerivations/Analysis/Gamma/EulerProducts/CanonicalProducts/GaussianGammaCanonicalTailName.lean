import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GammaCanonicalNames
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmName

/-!
# The original canonical Gamma tail as a Gaussian regular name

Source C6/C7 uses T_N(z/B), the sum of the local canonical factors at
indices greater than N. The old jointly cofinal Taylor/index observations
are retained exactly, without a replacement sampler or precision shift.
Their genuine finite C6 bound and original rounding give radius
R²/N+2/2^(p+4). The actual Gaussian PR2 name is regular; the additional
safe cutoff 4R²<=N gives true Euclidean unit-disk samples, so the existing
verified exponential-name constructor applies to this actual tail.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailName

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_represents represents positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open DyadicComplexLogarithm (unit)
open GammaCanonicalNames (observation)
open GaussianLocalLogarithmName (unit_positive unit_factor unit_lower)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B N : PTm n) : Fm PTm n := le one B ⋏ (le one N ⋏
  (ComplexLogarithmRemainder.bounded z (R*B) ⋏ le (two*R) N))
def safeSource (z R B N : PTm n) : Fm PTm n := source z R B N ⋏ le (num 4*R*R) N
def value (p z R B N : PTm n) : PTm n := ofGaussian (observation p z R B N) (unit p)
def radius (p R N : PTm n) : PTm n := R*R*unit p+two*N
def denominator (p N : PTm n) : PTm n := N*unit p
ipra_subst source
ipra_subst safeSource
ipra_subst value
ipra_subst radius
ipra_subst denominator

theorem denominator_positive (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (denominator p N) :=
  positive_product _ _ hN (unit_positive p)

/-- Sharp original C6 plus the actual two-coordinate rounding slack. -/
theorem value_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    bounded (value p z R B N) (radius p R N) (denominator p N) := by
  have native := GammaCanonicalNames.observation_disk_bound p z R B N h.andE₂.andE₂.andE₁
    h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂
  have clear : Γ ⊢[PRAAx] le
      ((denominator p N*denominator p N)*ComplexLogarithmRemainder.normSq (observation p z R B N))
      ((radius p R N*radius p R N)*(unit p*unit p)) :=
    le_congr (by
      have e := natEq (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) N (observation p z R B N))
      apply deriveNat; unfold denominator; ipra_simps; rw [e]; ring)
      (by unfold radius; ipra_ring) (le_mul_mono (le_refl (unit p*unit p)) native)
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (unit_positive p)
    (denominator_positive p N h.andE₂.andE₁) (ofGaussian_represents _ _ (unit_positive p)) clear

theorem safe_radius (p R N : PTm n) (h : Γ ⊢[PRAAx] le (num 4*R*R) N) : Γ ⊢[PRAAx]
    le (radius p R N) (denominator p N) := by
  have twice : Γ ⊢[PRAAx] le (two*R*R) N := le_trans
    (le_of_eq_add (d := two*R*R) (by ipra_ring)) h
  have four : Γ ⊢[PRAAx] le (num 4) (unit p) := le_trans
    (le_of_eq_add (d := num 12) (by ipra_ring)) (unit_lower p)
  have combined := add_le_add₂ (le_mul_mono twice (le_refl (unit p))) (le_mul_mono four (le_refl N))
  apply mul_le_cancel (d' := one)
  exact le_congr (by unfold radius; ipra_ring) (by unfold denominator; ipra_ring) combined

theorem value_unit_disk (p z R B N : PTm n) (h : Γ ⊢[PRAAx] safeSource z R B N) : Γ ⊢[PRAAx]
    bounded (value p z R B N) one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (denominator_positive p N h.andE₁.andE₂.andE₁) (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) (safe_radius p R N h.andE₂))
    (value_bound p z R B N h.andE₁)

theorem ordered_distance (p k z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (value (p+k) z R B N) (value p z R B N) (num 5) (unit p) := by
  have up := unit_positive (Γ := Γ) p
  have uq := unit_positive (Γ := Γ) (p+k)
  have early := GaussianRationalSyntheticDivision.rescale_to (value p z R B N) (observation p z R B N) (unit p)
    (pw two k) (unit (p+k)) (ofGaussian_represents _ _ up) (DyadicComplexLogarithm.unit_add p k).eqSymm
  have later := ofGaussian_represents (Γ := Γ) (observation (p+k) z R B N) (unit (p+k)) uq
  have rep : Γ ⊢[PRAAx] represents (qsub (value (p+k) z R B N) (value p z R B N))
      (GammaCanonicalNames.discrepancy p k z R B N) (unit (p+k)) := by
    simpa only [value,GammaCanonicalNames.discrepancy,GaussianRootAlgebra.sub] using
      GaussianRationalMetric.qsub_represents _ _ _ _ _ uq later early
  have radius : Γ ⊢[PRAAx] (unit p*unit p)*((num 5*pw two k)*(num 5*pw two k)) ≐
      (num 5*num 5)*(unit (p+k)*unit (p+k)) := by
    have e := natEq (DyadicComplexLogarithm.unit_add (Γ := Γ) p k)
    apply deriveNat; ipra_simps; rw [e]; ring
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ uq up rep
    (le_congr (.eqRefl _) radius (le_mul_mono (le_refl (unit p*unit p))
      (GammaCanonicalNames.regular_dyadic_bound p k z R B N h.andE₂.andE₂.andE₁ h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂)))

theorem ordered_unit_distance (p k z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (value (p+k) z R B N) (value p z R B N) one (GaussianCoefficientNameBounds.unit p) := by
  have budget : Γ ⊢[PRAAx] le (num 5*GaussianCoefficientNameBounds.unit p) (one*unit p) := by
    refine le_of_eq_add (d := num 11*GaussianCoefficientNameBounds.unit p) ?_
    have e := natEq (unit_factor (Γ := Γ) p)
    apply deriveNat; ipra_simps; rw [e]; ring
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (GaussianCoefficientNameBounds.unit_positive p) budget
    (ordered_distance p k z R B N h)

theorem value_congr_precision (z R B N : PTm n) {p q : PTm n} (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    value p z R B N ≐ value q z R B N := by
  ipra_congr (value (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [h, .eqRefl z, .eqRefl R, .eqRefl B, .eqRefl N]

theorem later_distance (s t z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (value t z R B N) (value s z R B N) one (GaussianCoefficientNameBounds.unit s) :=
  distance_congr (value_congr_precision z R B N (eq_add_of_le hst).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (ordered_unit_distance s (monus t s) z R B N h)

theorem value_regularity (s t z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (value s z R B N) (value t z R B N)
      (GaussianCoefficientNameBounds.unit s+GaussianCoefficientNameBounds.unit t)
      (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) := by
  let U := GaussianCoefficientNameBounds.unit s
  let V := GaussianCoefficientNameBounds.unit t
  have us := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) s
  have ut := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) t
  refine .orE (lt_or_le s t) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ us.wk (positive_product _ _ us.wk ut.wk)
      (le_of_eq_add (d := U*U) (by ipra_ring))
      (distance_symmetric _ _ _ _ us.wk (later_distance s t z R B N h.wk (le_of_lt Prf.hyp0)))
  · exact distance_radius_mono _ _ _ _ _ _ ut.wk (positive_product _ _ us.wk ut.wk)
      (le_of_eq_add (d := V*V) (by ipra_ring)) (later_distance t s z R B N h.wk Prf.hyp0)

/-! Actual persistent data is exactly(z,(R,(B,N))). -/
def data (z R B N : PTm n) : PTm n := pairT z (pairT R (pairT B N))
def pointTerm (p x : PTm n) : PTm n := value p (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x)))
def pointF : PR 2 := PTm.toPR (pointTerm (var 0) (var 1))
def point (p z R B N : PTm n) : PTm n := ap2 pointF p (data z R B N)
ipra_subst data
ipra_subst pointTerm
ipra_subst point

theorem point_at (p z R B N : PTm n) : Γ ⊢[PRAAx] point p z R B N ≐ value p z R B N := by
  have prog : Γ ⊢[PRAAx] point p z R B N ≐ pointTerm p (data z R B N) := by
    simpa [point,pointF,ap2] using toPR_eq (Γ := Γ) (pointTerm (var 0) (var 1) : PTm 2) ![p,data z R B N]
  refine prog.eqTrans ?_
  simpa only [pointTerm,subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (value (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,fstT (data z R B N),fstT (sndT (data z R B N)),fstT (sndT (sndT (data z R B N))),sndT (sndT (sndT (data z R B N)))]) (σ' := ![p,z,R,B,N])
      (fun i => by
        fin_cases i
        · exact .eqRefl _
        · exact fst_pair _ _
        · exact (snd_pair _ _).fstE
        · exact (snd_pair _ _).sndE.fstE
        · exact (snd_pair _ _).sndE.sndE)

theorem point_canonical (p z R B N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (point p z R B N) :=
  GaussianRationalHorner.canonical_congr (point_at p z R B N) (GaussianRationalHorner.ofGaussian_canonical _ _ (unit_positive p))
theorem point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    bounded (point p z R B N) (radius p R N) (denominator p N) :=
  bound_congr (point_at p z R B N).eqSymm (.eqRefl _) (.eqRefl _) (value_bound p z R B N h)
theorem point_unit_disk (p z R B N : PTm n) (h : Γ ⊢[PRAAx] safeSource z R B N) : Γ ⊢[PRAAx]
    bounded (point p z R B N) one one :=
  bound_congr (point_at p z R B N).eqSymm (.eqRefl _) (.eqRefl _) (value_unit_disk p z R B N h)
theorem point_regularity (s t z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (point s z R B N) (point t z R B N)
      (GaussianCoefficientNameBounds.unit s+GaussianCoefficientNameBounds.unit t)
      (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) :=
  distance_congr (point_at s z R B N).eqSymm (point_at t z R B N).eqSymm (.eqRefl _) (.eqRefl _) (value_regularity s t z R B N h)

theorem name_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx] pointCN pointF (data z R B N) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,point,Syn.shift,subst_data] using
    point_regularity (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) hs

theorem name_unit_samples (z R B N : PTm n) (h : Γ ⊢[PRAAx] safeSource z R B N) : Γ ⊢[PRAAx]
    GaussianUnitDiskExponentialName.unitSamples pointF (data z R B N) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] safeSource (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianUnitDiskExponentialName.unitSamples,point,Syn.shift,subst_data] using
    point_unit_disk (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

theorem original_exponential_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] safeSource z R B N) : Γ ⊢[PRAAx]
    GaussianUnitDiskExponentialName.input pointF (data z R B N) := .andI (name_regular z R B N h.andE₁) (name_unit_samples z R B N h)
theorem original_exponential_name_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] safeSource z R B N) : Γ ⊢[PRAAx]
    pointCN (GaussianUnitDiskExponentialName.nameF pointF) (data z R B N) :=
  GaussianUnitDiskExponentialName.name_regular pointF _ (original_exponential_input z R B N h)

theorem actual_original_tail_point_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (point (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      ofGaussian (observation (var 0) (var 1) (var 2) (var 3) (var 4)) (unit (var 0))) := closeUniv 5 (point_at _ _ _ _ _)
theorem actual_tail_point_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalHorner.canonical (point (var 0) (var 1) (var 2) (var 3) (var 4))) := closeUniv 5 (point_canonical _ _ _ _ _)
theorem source_sharp_tail_point_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶
      bounded (point (var 0) (var 1) (var 2) (var 3) (var 4)) (radius (var 0) (var 2) (var 4)) (denominator (var 0) (var 4))) :=
  closeUniv 5 (.impI (point_bound _ _ _ _ _ Prf.hyp0))
theorem source_independent_tail_precisions_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (point (var 0) (var 2) (var 3) (var 4) (var 5)) (point (var 1) (var 2) (var 3) (var 4) (var 5))
        (GaussianCoefficientNameBounds.unit (var 0)+GaussianCoefficientNameBounds.unit (var 1))
        (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) :=
  closeUniv 6 (.impI (point_regularity _ _ _ _ _ _ Prf.hyp0))
theorem original_tail_regular_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN pointF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))
theorem original_safe_tail_unit_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (safeSource (var 1) (var 2) (var 3) (var 4) ⟶ bounded (point (var 0) (var 1) (var 2) (var 3) (var 4)) one one) :=
  closeUniv 5 (.impI (point_unit_disk _ _ _ _ _ Prf.hyp0))
theorem original_safe_tail_exponential_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (safeSource (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianUnitDiskExponentialName.input pointF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_exponential_input _ _ _ _ Prf.hyp0))
theorem original_safe_tail_exponential_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (safeSource (var 0) (var 1) (var 2) (var 3) ⟶
      pointCN (GaussianUnitDiskExponentialName.nameF pointF) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_exponential_name_regular _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailName
