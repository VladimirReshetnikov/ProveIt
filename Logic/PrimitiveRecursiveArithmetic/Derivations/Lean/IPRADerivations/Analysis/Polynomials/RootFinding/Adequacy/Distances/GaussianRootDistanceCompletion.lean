import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceVariation
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRootSupport
import IPRADerivations.Analysis.Geometry.Distances.GaussianLinearDistanceName

/-!
# Actual Euclidean distance to the collision-tolerant root-support name

The raw stage t evaluates the actual Euclidean distance program against
roots_t, with its original point/square-root precision t+2. Original root
stability supplies an exact cross-stage represented comparison at arbitrary
independent observation indices. A genuine derived raw modulus and actual
scalar precision shift yield a nonnegative fast PR2 diagonal distance name.
All degrees, stages, data and normalization shifts remain internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootDistanceCompletion

open_ipra
open LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (distanceSample pointCN)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots roots_length)
open LeanProofs.IPRA.Analysis.GaussianRootSupport (coverDenominator cover_denominator_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! Generic actual scalar normalization, later instantiated with a derived
modulus two and the fixed numerical shift two. -/
def regular (f : PR 2) (M x : PTm n) : Fm PTm n := .all (.all
  (RationalValueBounds.radius (ap2 f (var 1) (Syn.shift (Syn.shift x)))
    (ap2 f (var 0) (Syn.shift (Syn.shift x)))
    (Syn.shift (Syn.shift M)*(unit (var 1)+unit (var 0))) (unit (var 1)*unit (var 0))))
def normalized (f : PR 2) (h x k : PTm n) : PTm n := ap2 f (k+h) x
def normalizeData (h x : PTm n) : PTm n := pairT h x
def normalizeBody (f : PR 2) : PTm 2 := normalized f (fstT (var 1)) (sndT (var 1)) (var 0)
def normalizeF (f : PR 2) : PR 2 := PTm.toPR (normalizeBody f)

ipra_subst regular [Syn.subst_shift, Syn.shift_subst]
ipra_subst normalized
ipra_subst normalizeData

theorem regular_at (f : PR 2) (M x s t : PTm n) (h : Γ ⊢[PRAAx] regular f M x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 f s x) (ap2 f t x) (M*(unit s+unit t)) (unit s*unit t) := by
  have first : Γ ⊢[PRAAx] .all (RationalValueBounds.radius (ap2 f (Syn.shift s) (Syn.shift x))
      (ap2 f (var 0) (Syn.shift x)) (Syn.shift M*(unit (Syn.shift s)+unit (var 0)))
      (unit (Syn.shift s)*unit (var 0))) := by
    simpa only [regular,Fm.subst_all,RationalValueBounds.subst_radius,subst_ap2,subst_unit,
      PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
      Foundations.BoundedFormulas.subst_up_shift',Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE s
  simpa only [RationalValueBounds.subst_radius,subst_ap2,subst_unit,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using first.allE t

theorem normalization_budget (M h s t : PTm n) (hM : Γ ⊢[PRAAx] le M (unit h)) : Γ ⊢[PRAAx]
    le ((M*(unit (s+h)+unit (t+h)))*(unit s*unit t))
      ((unit s+unit t)*(unit (s+h)*unit (t+h))) := by
  have scaled := le_mul_mono hM (le_refl ((unit s+unit t)*unit h*unit s*unit t))
  have hs := natEq (show Γ ⊢[PRAAx] unit (s+h) ≐ unit s*unit h from pw_add two s h)
  have ht := natEq (show Γ ⊢[PRAAx] unit (t+h) ≐ unit t*unit h from pw_add two t h)
  apply le_congr ?_ ?_ scaled
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring

theorem normalized_radius (f : PR 2) (M h x s t : PTm n)
    (hReg : Γ ⊢[PRAAx] regular f M x) (hM : Γ ⊢[PRAAx] le M (unit h)) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (normalized f h x s) (normalized f h x t)
      (unit s+unit t) (unit s*unit t) :=
  RationalValueBounds.radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
    (regular_at f M x (s+h) (t+h) hReg) (normalization_budget M h s t hM)

theorem normalize_program (f : PR 2) (h x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (normalizeF f) k (normalizeData h x) ≐ normalized f h x k := by
  simpa [normalizeF, normalizeBody, normalizeData] using
    (toPR_pair_eq (Γ := Γ) (normalized f (var 1) (var 2) (var 0)) k h x)

theorem normalized_fast (f : PR 2) (M h x : PTm n)
    (hReg : Γ ⊢[PRAAx] regular f M x) (hM : Γ ⊢[PRAAx] le M (unit h)) : Γ ⊢[PRAAx]
    GaussianLinearDistanceName.scalarCN (normalizeF f) (normalizeData h x) := by
  refine .allI (.allI ?_)
  have reg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] regular f
      (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using hReg.shift.shift
  have budget : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      le (Syn.shift (Syn.shift M)) (unit (Syn.shift (Syn.shift h))) := by
    simpa only [Fm.shift,subst_le,subst_unit,Syn.shift] using hM.shift.shift
  simpa only [Syn.shift,subst_normalizeData] using
    RationalValueBounds.radius_congr (normalize_program f (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) (var 1)).eqSymm
      (normalize_program f (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift x)) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (normalized_radius f _ _ _ (var 1) (var 0) reg budget)

/-! Concrete actual root-distance observations. -/
def input (step a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n :=
  monicRD step ⋏ (CN a N x ⋏ (le one N ⋏ pointCN point x))
def raw (step a : PR 3) (point : PR 2) (N x t : PTm n) : PTm n :=
  distanceSample point (roots step a N t x) x t
def data (N x : PTm n) : PTm n := pairT N x
def rawBody (step a : PR 3) (point : PR 2) : PTm 2 := raw step a point (fstT (var 1)) (sndT (var 1)) (var 0)
def rawF (step a : PR 3) (point : PR 2) : PR 2 := PTm.toPR (rawBody step a point)
def sample (step a : PR 3) (point : PR 2) (N x k : PTm n) : PTm n := raw step a point N x (k+two)
def nameF (step a : PR 3) (point : PR 2) : PR 2 := normalizeF (rawF step a point)
def nameData (N x : PTm n) : PTm n := normalizeData two (data N x)

ipra_subst input
ipra_subst raw
ipra_subst data
ipra_subst sample
ipra_subst nameData

theorem raw_congr (step a : PR 3) (point : PR 2) {N N' x x' t t' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hx : Γ ⊢[PRAAx] x ≐ x') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    raw step a point N x t ≐ raw step a point N' x' t' := by
  ipra_congr (raw step a point (var 0) (var 1) (var 2) : PTm 3) with [hN, hx, ht]

theorem raw_at (step a : PR 3) (point : PR 2) (N x t : PTm n) : Γ ⊢[PRAAx]
    ap2 (rawF step a point) t (data N x) ≐ raw step a point N x t := by
  simpa [rawF, rawBody, data] using
    (toPR_pair_eq (Γ := Γ) (raw step a point (var 1) (var 2) (var 0)) t N x)

theorem name_at (step a : PR 3) (point : PR 2) (N x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF step a point) k (nameData N x) ≐ sample step a point N x k :=
  (normalize_program (rawF step a point) two (data N x) k).eqTrans (raw_at step a point N x (k+two))

/-- The exact source cross-stage distance radius, with independent
observation errors retained rather than absorbed into a weaker modulus. -/
theorem stage_variation (step a : PR 3) (point : PR 2) (N t u x m l : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (distanceSample point (roots step a N t x) x m)
      (distanceSample point (roots step a N u x) x l)
      (unit m*unit l+coverDenominator t*(unit m+unit l)) (coverDenominator t*unit m*unit l) := by
  have nt : Γ ⊢[PRAAx] le one (Foundations.SequenceComposition.length (roots step a N t x)) :=
    le_congr (.eqRefl _) (roots_length step a N t x).eqSymm hN
  have nu : Γ ⊢[PRAAx] le one (Foundations.SequenceComposition.length (roots step a N u x)) :=
    le_congr (.eqRefl _) (roots_length step a N u x).eqSymm hN
  have actual := GaussianEuclideanDistanceVariation.sample_radius point (roots step a N t x)
    (roots step a N u x) x l m one (coverDenominator t) hPoint nt nu (cover_denominator_positive t)
    (GaussianRootSupport.root_support step a N t u x hRD hCN hN htu)
  exact RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _)
    (by unfold GaussianEuclideanDistanceVariation.sampleNumerator; ipra_ring)
    (by unfold GaussianEuclideanDistanceVariation.sampleDenominator; ipra_ring)
    (RationalValueBounds.radius_symmetric _ _ _ _ actual)

theorem cover_denominator_ge_unit (t : PTm n) : Γ ⊢[PRAAx] le (unit t) (coverDenominator t) :=
  GaussianEuclideanDistanceName.unit_le_shift t

theorem stage_budget (r l D : PTm n) (hD : Γ ⊢[PRAAx] le (unit r) D) : Γ ⊢[PRAAx]
    le ((unit r*unit l+D*(unit r+unit l))*(unit r*unit l))
      ((two*unit l+unit r)*(D*unit r*unit l)) := by
  have first := mul_le_mul_right (unit l) hD
  have added := add_le_add_right (D*(unit r+unit l)) first
  exact le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (unit r*unit l) added)

/-- A fixed raw diagonal query can be compared with any later stage and
any precision in that stage. This is the finite input for zero-distance
and Member equivalence; no completed-distance equality is assumed. -/
theorem raw_stage_upper (step a : PR 3) (point : PR 2) (N x r t l : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hrt : Γ ⊢[PRAAx] le r t) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (raw step a point N x r) (distanceSample point (roots step a N t x) x l)
      (two*unit l+unit r) (unit r*unit l) :=
  RationalValueBounds.upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (cover_denominator_positive r) (unit_positive r)) (unit_positive l))
    (RationalValueBounds.upper_of_radius _ _ _ _ (stage_variation step a point N r t x r l hRD hCN hN hPoint hrt))
    (stage_budget r l (coverDenominator r) (cover_denominator_ge_unit r))

theorem raw_ordered_radius (step a : PR 3) (point : PR 2) (N x t u : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (raw step a point N x t) (raw step a point N x u)
      (two*(unit t+unit u)) (unit t*unit u) := by
  have first := stage_budget (Γ := Γ) t u (coverDenominator t) (cover_denominator_ge_unit t)
  have enlarge : Γ ⊢[PRAAx] le ((two*unit u+unit t)*(coverDenominator t*unit t*unit u))
      ((two*(unit t+unit u))*(coverDenominator t*unit t*unit u)) :=
    mul_le_mul_right _ (le_of_eq_add (d := unit t) (by ipra_ring))
  exact RationalValueBounds.radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (cover_denominator_positive t) (unit_positive t)) (unit_positive u))
    (stage_variation step a point N t u x t u hRD hCN hN hPoint htu) (le_trans first enlarge)

theorem raw_radius (step a : PR 3) (point : PR 2) (N x t u : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] pointCN point x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (raw step a point N x t) (raw step a point N x u)
      (two*(unit t+unit u)) (unit t*unit u) := by
  refine .orE (le_total t u) ?_ ?_
  · exact raw_ordered_radius step a point N x t u hRD.wk hCN.wk hN.wk hPoint.wk Prf.hyp0
  · have reversed := raw_ordered_radius step a point N x u t hRD.wk hCN.wk hN.wk hPoint.wk Prf.hyp0
    exact RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (RationalValueBounds.radius_symmetric _ _ _ _ reversed)

theorem raw_regular (step a : PR 3) (point : PR 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] input step a point N x) : Γ ⊢[PRAAx] regular (rawF step a point) two (data N x) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input step a point
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift.shift
  have result := raw_radius step a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (var 1) (var 0)
    (Prf.andE₁ hs) (Prf.andE₁ (Prf.andE₂ hs)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hs)))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hs)))
  simpa only [Syn.shift,subst_data,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using RationalValueBounds.radius_congr
    (raw_at step a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (var 1)).eqSymm
    (raw_at step a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) result

theorem name_fast (step a : PR 3) (point : PR 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] input step a point N x) : Γ ⊢[PRAAx]
    GaussianLinearDistanceName.scalarCN (nameF step a point) (nameData N x) :=
  normalized_fast _ two two _ (raw_regular step a point N x h)
    (le_trans (le_succ_self two) (RationalClosure.succ_le_two_pow two))

theorem raw_denominator_positive (step a : PR 3) (point : PR 2) (N x t : PTm n) : Γ ⊢[PRAAx]
    le one (GaussianEuclideanDistanceUpperCut.denominator point (roots step a N t x) x t) :=
  GaussianEuclideanDistanceUpperCut.denominator_positive _ _ _ _

theorem raw_represents (step a : PR 3) (point : PR 2) (N x t : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (raw step a point N x t)
      (ZT.ofNat (GaussianEuclideanDistanceUpperCut.numerator point (roots step a N t x) x t))
      (GaussianEuclideanDistanceUpperCut.denominator point (roots step a N t x) x t) :=
  GaussianEuclideanDistanceUpperCut.sample_represents _ _ _ _

theorem raw_nonnegative (step a : PR 3) (point : PR 2) (N x t : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one) (raw step a point N x t) :=
  GaussianEuclideanDistanceName.sample_zero_lower _ _ _ _

theorem raw_canonical (step a : PR 3) (point : PR 2) (N x t : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (raw step a point N x t) :=
  RationalNormalForm.normalize_well_formed _ _ (raw_denominator_positive step a point N x t)

theorem name_nonnegative (step a : PR 3) (point : PR 2) (N x k : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
      (ap2 (nameF step a point) k (nameData N x)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (name_at step a point N x k).eqSymm
    (raw_nonnegative step a point N x (k+two))

theorem name_canonical (step a : PR 3) (point : PR 2) (N x k : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (ap2 (nameF step a point) k (nameData N x)) := by
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (RationalNormalForm.wellFormed (var 0) : Fm PTm 1)
    (σ := ![sample step a point N x k]) (σ' := ![ap2 (nameF step a point) k (nameData N x)])
    (fun i => by fin_cases i; exact (name_at step a point N x k).eqSymm)
    (by simpa only [sample,RationalNormalForm.subst_wellFormed,Syn.subst_var,Matrix.cons_val_zero] using
      raw_canonical step a point N x (k+two))
  simpa only [RationalNormalForm.subst_wellFormed,Syn.subst_var,Matrix.cons_val_zero] using e

theorem name_nonnegative_all (step a : PR 3) (point : PR 2) (N x : PTm n) : Γ ⊢[PRAAx]
    .all (RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
      (ap2 (nameF step a point) (var 0) (nameData (Syn.shift N) (Syn.shift x)))) :=
  .allI (name_nonnegative step a point (Syn.shift N) (Syn.shift x) (var 0))

theorem stage_variation_input (step a : PR 3) (point : PR 2) (N t u x m l : PTm n)
    (h : Γ ⊢[PRAAx] input step a point N x) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (distanceSample point (roots step a N t x) x m)
      (distanceSample point (roots step a N u x) x l)
      (unit m*unit l+coverDenominator t*(unit m+unit l)) (coverDenominator t*unit m*unit l) :=
  stage_variation step a point N t u x m l (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))) htu

/-- Exact source (RS) error for the represented stage distances: the two
independent rational observation errors remain visible in the sentence. -/
theorem stage_variation_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input step a point (var 0) (var 3) ⟶ le (var 1) (var 2) ⟶
      RationalValueBounds.radius
        (distanceSample point (roots step a (var 0) (var 1) (var 3)) (var 3) (var 4))
        (distanceSample point (roots step a (var 0) (var 2) (var 3)) (var 3) (var 5))
        (unit (var 4)*unit (var 5)+coverDenominator (var 1)*(unit (var 4)+unit (var 5)))
        (coverDenominator (var 1)*unit (var 4)*unit (var 5))) :=
  closeUniv 6 (.impI (.impI (stage_variation_input _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem generic_scalar_normalization_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (regular f (var 0) (var 2) ⟶ le (var 0) (unit (var 1)) ⟶
      GaussianLinearDistanceName.scalarCN (normalizeF f) (normalizeData (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (normalized_fast _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem generic_scalar_normalization_program_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (normalizeF f) (var 2) (normalizeData (var 0) (var 1)) ≐ ap2 f (var 2+var 0) (var 1)) :=
  closeUniv 3 (normalize_program _ _ _ _)

theorem raw_regular_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input step a point (var 0) (var 1) ⟶ regular (rawF step a point) two (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (raw_regular _ _ _ _ _ Prf.hyp0))

theorem completed_distance_name_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input step a point (var 0) (var 1) ⟶
      GaussianLinearDistanceName.scalarCN (nameF step a point) (nameData (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_fast _ _ _ _ _ Prf.hyp0))

theorem completed_distance_nonnegative_canonical_closed (step a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
        (ap2 (nameF step a point) (var 2) (nameData (var 0) (var 1))) ⋏
      RationalNormalForm.wellFormed (ap2 (nameF step a point) (var 2) (nameData (var 0) (var 1)))) :=
  closeUniv 3 (.andI (name_nonnegative _ _ _ _ _ _) (name_canonical _ _ _ _ _ _))

theorem completed_distance_query_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap2 (rawF step a point) (var 2) (data (var 0) (var 1)) ≐ raw step a point (var 0) (var 1) (var 2)) ⋏
      (ap2 (nameF step a point) (var 2) (nameData (var 0) (var 1)) ≐
        distanceSample point (roots step a (var 0) (var 2+two) (var 1)) (var 1) (var 2+two))) :=
  closeUniv 3 (.andI (raw_at _ _ _ _ _ _) (name_at _ _ _ _ _ _))

theorem raw_representation_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (GaussianEuclideanDistanceUpperCut.denominator point (roots step a (var 0) (var 2) (var 1)) (var 1) (var 2)) ⋏
      RationalArithmetic.represents (raw step a point (var 0) (var 1) (var 2))
        (ZT.ofNat (GaussianEuclideanDistanceUpperCut.numerator point (roots step a (var 0) (var 2) (var 1)) (var 1) (var 2)))
        (GaussianEuclideanDistanceUpperCut.denominator point (roots step a (var 0) (var 2) (var 1)) (var 1) (var 2))) :=
  closeUniv 3 (.andI (raw_denominator_positive _ _ _ _ _ _) (raw_represents _ _ _ _ _ _))

theorem raw_stage_upper_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input step a point (var 0) (var 1) ⟶ le (var 2) (var 3) ⟶
      RationalValueBounds.upper (raw step a point (var 0) (var 1) (var 2))
        (distanceSample point (roots step a (var 0) (var 3) (var 1)) (var 1) (var 4))
        (two*unit (var 4)+unit (var 2)) (unit (var 2)*unit (var 4))) := by
  apply closeUniv 5
  refine .impI (.impI ?_)
  have h : ([le (var 2) (var 3),input step a point (var 0) (var 1)] : List (Fm PTm 5)) ⊢[PRAAx]
      input step a point (var 0) (var 1) := Prf.hyp1
  exact raw_stage_upper _ _ _ _ _ _ _ _ (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))) Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRootDistanceCompletion
