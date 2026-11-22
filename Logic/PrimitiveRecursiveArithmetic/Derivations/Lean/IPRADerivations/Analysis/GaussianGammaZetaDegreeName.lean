import IPRADerivations.Analysis.GaussianGammaFixedDegreeHorizon
import IPRADerivations.Analysis.GaussianGammaReciprocalDegreeCells
import IPRADerivations.Analysis.RationalReciprocalPowerName
import IPRADerivations.Analysis.RationalGaussianNameEmbedding
import IPRADerivations.Analysis.GaussianGammaCofinalDegreeTail
import IPRADerivations.Analysis.GaussianNamedRateTransport

/-!
# The original zeta-tail coefficients in a genuine finite-degree Gamma name

The polynomial uses actual observations of the proved C17 coefficient
names. A common numerical precision makes all coefficient observations
the SAME finite factor horizon. Literal finite separation then identifies
the whole polynomial with the original degree-major rectangle. The C6
horizon bound and one later bit give exact independent equivalence to the
actual fixed-degree Gamma tail name.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDegreeName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaReciprocalDegreeCells (degree monomial sourcePart separatedSum)
open RationalGaussianEmbedding (embed)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalFiniteSum (sum termsEqual)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianGammaCanonicalTailName (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem degree_positive (j : PTm n) : Γ ⊢[PRAAx] le two (degree j) :=
  le_of_eq_add (d := j) (by unfold degree; ipra_ring)
theorem coefficient_name_regular (j N : PTm n) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (RationalGaussianNameEmbedding.nameF RationalReciprocalPowerName.tailNameF)
      (RationalReciprocalPowerName.tailData (degree j) N) :=
  RationalGaussianNameEmbedding.name_regular _ _ (RationalReciprocalPowerName.tail_name_regular _ _ (degree_positive j))
theorem coefficient_is_original_zeta_tail (p q j N : PTm n) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (RationalReciprocalPowerName.zetaSample p (degree j))
      (RationalArithmetic.add (RationalReciprocalPowerName.harmonicPrefix (degree j) N)
        (RationalReciprocalPowerName.tailSample q (degree j) N)) (unit p+unit q) (unit p*unit q) :=
  RationalValueBounds.radius_congr (.eqRefl _) (RationalReciprocalPowerName.reconstruction_actual_sum q (degree j) N)
    (.eqRefl _) (.eqRefl _) (RationalReciprocalPowerName.reconstruction_error p q (degree j) N (degree_positive j))

def coefficientPart (q z B N j : PTm n) : PTm n :=
  qmul (monomial z B j) (embed (RationalReciprocalPowerName.tailSample q (degree j) N))
def coefficientData (q z B N : PTm n) : PTm n := pairT q (pairT z (pairT B N))
def coefficientBody : PTm 2 := coefficientPart (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def clock (p R : PTm n) : PTm n := succ p+R*R+num 5
def horizon (p R : PTm n) : PTm n := RationalReciprocalPowerName.cutoff (clock p R)
def observation (p z R B N L : PTm n) : PTm n := sum coefficientBody (succ L) (coefficientData (clock p R) z B N)
@[simp] theorem subst_coefficientPart {m : ℕ} (σ : Fin n → PTm m) (q z B N j : PTm n) :
    Syn.subst σ (coefficientPart q z B N j) = coefficientPart (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ j) := by simp [coefficientPart]
@[simp] theorem subst_coefficientData {m : ℕ} (σ : Fin n → PTm m) (q z B N : PTm n) :
    Syn.subst σ (coefficientData q z B N) = coefficientData (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [coefficientData]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (clock p R) = clock (Syn.subst σ p) (Syn.subst σ R) := by simp [clock]
@[simp] theorem subst_horizon {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (horizon p R) = horizon (Syn.subst σ p) (Syn.subst σ R) := by simp [horizon]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B N L : PTm n) :
    Syn.subst σ (observation p z R B N L) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ L) := by simp [observation]

theorem coefficient_part_congr {q z B N j q' z' B' N' j' : PTm n}
    (hq : Γ ⊢[PRAAx] q ≐ q') (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    coefficientPart q z B N j ≐ coefficientPart q' z' B' N' j' := by
  simpa only [subst_coefficientPart,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (coefficientPart (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![q,z,B,N,j]) (σ' := ![q',z',B',N',j'])
      (fun i => by fin_cases i; exact hq; exact hz; exact hB; exact hN; exact hj)
theorem coefficient_term_at (q z B N j : PTm n) : Γ ⊢[PRAAx]
    inst2 coefficientBody j (coefficientData q z B N) ≐ coefficientPart q z B N j := by
  simp only [coefficientBody,inst2,subst_coefficientPart,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have t₁ := snd_pair (Γ := Γ) q (pairT z (pairT B N))
  have t₂ := (congrSnd t₁).eqTrans (snd_pair z (pairT B N))
  exact coefficient_part_congr (fst_pair _ _) ((congrFst t₁).eqTrans (fst_pair _ _))
    ((congrFst t₂).eqTrans (fst_pair _ _)) ((congrSnd t₂).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem coefficient_part_finite (q z B N j : PTm n) : Γ ⊢[PRAAx]
    coefficientPart q z B N j ≐ sourcePart z B N (RationalReciprocalPowerName.cutoff q) j :=
  qmul_congr (.eqRefl _) (RationalGaussianRealPart.embed_congr (RationalReciprocalPowerName.tail_sample_at q (degree j) N))

theorem actual_polynomial_as_degree (p z R B N L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    observation p z R B N L ≐ GaussianGammaFiniteDegreeRearrangement.degreeMajor z B N (horizon p R) L := by
  have align : Γ ⊢[PRAAx] observation p z R B N L ≐ separatedSum z B N (horizon p R) L := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    have left := (coefficient_term_at (Γ := lt (var 0) (succ (Syn.shift L)) :: Γ.map Fm.shift)
      (clock (Syn.shift p) (Syn.shift R)) (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0)).eqTrans
      (coefficient_part_finite _ _ _ _ _)
    have right := GaussianGammaReciprocalDegreeCells.separated_term_at (Γ := lt (var 0) (succ (Syn.shift L)) :: Γ.map Fm.shift)
      (Syn.shift z) (Syn.shift B) (Syn.shift N) (horizon (Syn.shift p) (Syn.shift R)) (var 0)
    simpa only [termsEqual,subst_coefficientData,subst_clock,GaussianGammaReciprocalDegreeCells.subst_separatedData,
      subst_horizon,Syn.shift,ConciseIPRA.PTm.subst_succ] using left.eqTrans right.eqSymm
  exact align.eqTrans (GaussianGammaReciprocalDegreeCells.degree_major_separation z B N (horizon p R) L hB).eqSymm

theorem horizon_product (p R : PTm n) : Γ ⊢[PRAAx] horizon p R ≐
    num 4*pw two (GammaCanonicalNames.precision (succ p))*pw two (R*R) := by
  have ec : Γ ⊢[PRAAx] clock p R ≐ GammaCanonicalNames.precision (succ p)+R*R := by
    unfold clock GammaCanonicalNames.precision
    ipra_ring
  unfold horizon RationalReciprocalPowerName.cutoff RationalReciprocalPowerName.unit
  exact (congrMul (.eqRefl _) ((congrAp2 powF ec (.eqRefl two)).eqTrans
    (pw_add two (GammaCanonicalNames.precision (succ p)) (R*R)))).eqTrans (by ipra_ring)
theorem horizon_dominates (p R : PTm n) : Γ ⊢[PRAAx]
    le (GammaCanonicalNames.count (succ p) R) (horizon p R) := by
  let U := pw two (GammaCanonicalNames.precision (succ p))
  let V := pw two (R*R)
  have first := AnalyticNumberTheory.PhiLower.le_mul_mono (Γ := Γ) (le_refl U) (RationalClosure.succ_le_two_pow (R*R))
  have last : Γ ⊢[PRAAx] le (U*V) (num 4*U*V) := le_of_eq_add (d := num 3*U*V) (by ipra_ring)
  exact le_congr (by unfold GammaCanonicalNames.count; ipra_ring) (horizon_product p R).eqSymm (le_trans first last)

theorem polynomial_to_fixed_observation (p z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (observation p z R B N L) (GaussianGammaFixedDegreeHorizon.observation (succ p) z R B N L)
      one (unit (succ p)) := by
  let r := GammaCanonicalNames.count (succ p) R
  have finite := GaussianGammaFixedDegreeHorizon.finite_horizon_distance z R B N r
    (LeanProofs.IPRA.PTm.monus (horizon p R) r) L h
  have moved := distance_congr
    (GaussianRationalFiniteSum.sum_index_congr (Γ := Γ) _ (.eqRefl _)
      (congrPairT (eq_add_of_le (horizon_dominates p R)).eqSymm (.eqRefl _)))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) finite
  have close := distance_radius_mono _ _ (R*R) (N+r) one (unit (succ p))
    (le_trans h.andE₂.andE₁ (le_add_right N r)) (unit_positive _)
    (le_congr (mul_comm (unit (succ p)) (R*R)) (one_mul _).eqSymm
      (GaussianGammaFixedDegreeHorizon.original_count_budget (succ p) R N)) moved
  exact distance_congr (actual_polynomial_as_degree p z R B N L h.andE₁).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) close

theorem observation_error (p q z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (observation p z R B N L) (GaussianGammaFixedDegreeHorizon.observation q z R B N L)
      (unit p+unit q) (unit p*unit q) := by
  have den := positive_product (Γ := Γ) _ _ (unit_positive (succ p)) (unit_positive q)
  have first := distance_radius_mono _ _ one (unit (succ p)) (unit q) (unit (succ p)*unit q)
    (unit_positive _) den (le_of_eq_add (d := zero) (by ipra_ring)) (polynomial_to_fixed_observation p z R B N L h)
  have both := distance_triangle_same _ _ _ _ _ _ den first (GaussianGammaFixedDegreeHorizon.observation_regularity (succ p) q z R B N L h)
  apply distance_radius_mono _ _ _ _ _ _ den (positive_product _ _ (unit_positive p) (unit_positive q)) _ both
  have e := natEq (pw_succ (Γ := Γ) two p)
  apply le_of_eq_add (d := zero)
  apply deriveNat
  unfold unit
  ipra_simps
  rw [e]
  ring

def data (z R B N L : PTm n) : PTm n := GaussianGammaFixedDegreeHorizon.data z R B N L
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) : PTm 2)
def sample (p z R B N L : PTm n) : PTm n := ap2 nameF p (data z R B N L)
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B N L : PTm n) :
    Syn.subst σ (data z R B N L) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ L) := by simp [data]
theorem observation_congr {p p' z z' R R' B B' N N' L L' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R')
    (hB : Γ ⊢[PRAAx] B ≐ B') (hN : Γ ⊢[PRAAx] N ≐ N') (hL : Γ ⊢[PRAAx] L ≐ L') : Γ ⊢[PRAAx]
    observation p z R B N L ≐ observation p' z' R' B' N' L' := by
  have e5 : (![p,z,R,B,N,L] : Fin 6 → PTm n) 5 = L := rfl
  have e5' : (![p',z',R',B',N',L'] : Fin 6 → PTm n) 5 = L' := rfl
  simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,e5,e5',Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,z,R,B,N,L]) (σ' := ![p',z',R',B',N',L'])
      (fun i => by fin_cases i; exact hp; exact hz; exact hR; exact hB; exact hN; exact hL)
theorem sample_at (p z R B N L : PTm n) : Γ ⊢[PRAAx] sample p z R B N L ≐ observation p z R B N L := by
  have raw := toPR_eq (Γ := Γ) (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) : PTm 2)
    ![p,data z R B N L]
  have e : Γ ⊢[PRAAx] sample p z R B N L ≐ observation p (fstT (data z R B N L)) (fstT (sndT (data z R B N L)))
      (fstT (sndT (sndT (data z R B N L)))) (fstT (sndT (sndT (sndT (data z R B N L)))))
      (sndT (sndT (sndT (sndT (data z R B N L))))) := by
    simpa only [sample,nameF,ap2,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using raw
  have t₁ := snd_pair (Γ := Γ) z (pairT R (pairT B (pairT N L)))
  have t₂ := (congrSnd t₁).eqTrans (snd_pair R (pairT B (pairT N L)))
  have t₃ := (congrSnd t₂).eqTrans (snd_pair B (pairT N L))
  exact e.eqTrans (observation_congr (.eqRefl _) (fst_pair _ _) ((congrFst t₁).eqTrans (fst_pair _ _))
    ((congrFst t₂).eqTrans (fst_pair _ _)) ((congrFst t₃).eqTrans (fst_pair _ _)) ((congrSnd t₃).eqTrans (snd_pair _ _)))
theorem sample_canonical (p z R B N L : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p z R B N L) :=
  GaussianRationalHorner.canonical_congr (sample_at p z R B N L) (GaussianRationalFiniteSum.sum_canonical _ _ _)
theorem sample_bound (p z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (sample p z R B N L) (R*R) N :=
  GaussianRationalReciprocal.bound_congr ((sample_at p z R B N L).eqTrans (actual_polynomial_as_degree p z R B N L h.andE₁)).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianGammaFiniteDegreeRearrangement.uniform_rearranged_bound z R B N (horizon p R) L h)

theorem named_equivalence (z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent nameF GaussianGammaFixedDegreeHorizon.nameF (data z R B N L)
      (GaussianGammaFixedDegreeHorizon.data z R B N L) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  have bound := distance_congr
    (sample_at (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L))).eqSymm
    (GaussianGammaFixedDegreeHorizon.sample_at (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L))).eqSymm (.eqRefl _) (.eqRefl _)
    (observation_error (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L)) hs)
  simpa only [GaussianNameEquivalence.crossEquivalent,sample,GaussianGammaFixedDegreeHorizon.sample,Syn.shift,subst_data,
    GaussianGammaFixedDegreeHorizon.subst_data,unit,GaussianEuclideanPointDistance.unit] using bound
theorem name_regular (z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B N L) := by
  have he := named_equivalence z R B N L h
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ he (GaussianNameEquivalence.cross_symm _ _ _ _ he)

theorem original_zeta_C18_rate (z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate GaussianGammaCanonicalTailName.pointF nameF
      (GaussianGammaCanonicalTailName.data z R B N) (data z R B N L) (R*R) (GaussianGammaCofinalDegreeTail.rateDen N L) :=
  GaussianNamedRateTransport.transport GaussianGammaCanonicalTailName.pointF GaussianGammaFixedDegreeHorizon.nameF
    GaussianGammaCanonicalTailName.pointF nameF (GaussianGammaCanonicalTailName.data z R B N)
    (GaussianGammaFixedDegreeHorizon.data z R B N L) (GaussianGammaCanonicalTailName.data z R B N) (data z R B N L)
    (R*R) (GaussianGammaCofinalDegreeTail.rateDen N L) (GaussianGammaCofinalDegreeTail.rate_den_positive N L h.andE₂.andE₁)
    (GaussianGammaCofinalDegreeTail.original_C18_name_rate z R B N L h)
    (GaussianNameEquivalence.cross_refl _ _ (GaussianGammaCanonicalTailName.name_regular z R B N h)) (named_equivalence z R B N L h)

theorem original_zeta_tail_coefficient_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (RationalValueBounds.radius (RationalReciprocalPowerName.zetaSample (var 0) (degree (var 2)))
      (RationalArithmetic.add (RationalReciprocalPowerName.harmonicPrefix (degree (var 2)) (var 3))
        (RationalReciprocalPowerName.tailSample (var 1) (degree (var 2)) (var 3)))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 4 (coefficient_is_original_zeta_tail _ _ _ _)
theorem actual_zeta_polynomial_finite_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
      GaussianGammaFiniteDegreeRearrangement.degreeMajor (var 1) (var 3) (var 4) (horizon (var 0) (var 2)) (var 5)) :=
  closeUniv 6 (.impI (actual_polynomial_as_degree _ _ _ _ _ _ Prf.hyp0))
theorem original_zeta_polynomial_name_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianNameEquivalence.crossEquivalent nameF GaussianGammaFixedDegreeHorizon.nameF
        (data (var 0) (var 1) (var 2) (var 3) (var 4)) (GaussianGammaFixedDegreeHorizon.data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (named_equivalence _ _ _ _ _ Prf.hyp0))
theorem original_zeta_polynomial_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ GaussianEuclideanDistanceName.pointCN nameF
      (data (var 0) (var 1) (var 2) (var 3) (var 4))) := closeUniv 5 (.impI (name_regular _ _ _ _ _ Prf.hyp0))
theorem original_zeta_polynomial_C18_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianNamedInverseRate.independentRate GaussianGammaCanonicalTailName.pointF nameF
        (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3) (var 4))
        (var 1*var 1) (GaussianGammaCofinalDegreeTail.rateDen (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_zeta_C18_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDegreeName
