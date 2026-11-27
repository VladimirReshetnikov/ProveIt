import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumName
import IPRADerivations.Foundations.CoherentMinimizer
import IPRADerivations.Analysis.Names.Aggregation.AggregateChain

/-!
# The actual coherent subsequence of original cube minimizers

The only extra source hypothesis is the supplied quantitative uniqueness
modulus. The selected points use its actual running majorant. A second
actual schedule supplies the original canonical evaluation procedure.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeCoherentMinimizer

open_ipra
open RationalCubeMinimum (coherence continuity presentedCube minimizer sample precision)
open RationalCubeGrid (scale)
open RationalCubeInfimumName (value data)
open RationalHausdorff (pointRadius)
open LeanProofs.IPRA.Probability.Ninther (mn)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def modulusBody (u : PR 2) : PTm 2 := ap2 u (var 0) (var 1)
def schedule (u : PR 2) (k x : PTm n) : PTm n := Foundations.ModulusNormalization.mhat (modulusBody u) k x
def point (A : PR 3) (mu u : PR 2) (d k x : PTm n) : PTm n := minimizer A mu d (schedule u k x) x
def nearAt (A : PR 3) (mu : PR 2) (d x y e p q : PTm n) : Fm PTm n :=
  RationalValueBounds.upper (sample A y p x) (value A mu d q x)
    (scale q*scale p+scale e*(scale q+scale p)) (scale e*scale q*scale p)
def near (A : PR 3) (mu : PR 2) (d x y e : PTm n) : Fm PTm n := .all (.all
  (nearAt A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
    (Syn.shift (Syn.shift e)) (var 1) (var 0)))
def uniqueness (A : PR 3) (mu u : PR 2) (d x : PTm n) : Fm PTm n := .all (.all (.all
  (presentedCube (var 1) (Syn.shift (Syn.shift (Syn.shift d))) ⟶ presentedCube (var 0) (Syn.shift (Syn.shift (Syn.shift d))) ⟶
    near A mu (Syn.shift (Syn.shift (Syn.shift d))) (Syn.shift (Syn.shift (Syn.shift x))) (var 1)
      (ap2 u (var 2) (Syn.shift (Syn.shift (Syn.shift x)))) ⟶
    near A mu (Syn.shift (Syn.shift (Syn.shift d))) (Syn.shift (Syn.shift (Syn.shift x))) (var 0)
      (ap2 u (var 2) (Syn.shift (Syn.shift (Syn.shift x)))) ⟶
    pointRadius (var 1) (var 0) (Syn.shift (Syn.shift (Syn.shift d))) one (scale (var 2)))))

ipra_subst schedule [Foundations.ModulusNormalization.mhat]
ipra_subst point
ipra_subst nearAt
ipra_subst near [Syn.subst_shift, Syn.shift_subst]
ipra_subst uniqueness [Syn.subst_shift, Syn.shift_subst]

theorem schedule_index (u : PR 2) (k x : PTm n) : Γ ⊢[PRAAx] le k (schedule u k x) := Foundations.ModulusNormalization.index_le _ _ _
theorem schedule_modulus (u : PR 2) (k l x : PTm n) (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx] le (ap2 u k x) (schedule u l x) := by
  simpa only [schedule,modulusBody,inst2,subst_ap2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Foundations.ModulusNormalization.modulus_le (Γ := Γ) (modulusBody u) (x := x) h
theorem schedule_mono (u : PR 2) (k l x : PTm n) (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx] le (schedule u k x) (schedule u l x) := Foundations.ModulusNormalization.mhat_mono _ h

theorem selected_near_at (A : PR 3) (mu : PR 2) (d j e x p q : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (he : Γ ⊢[PRAAx] le e j) : Γ ⊢[PRAAx]
    nearAt A mu d x (minimizer A mu d j x) e p q := by
  have hp := AnalyticNumberTheory.PowerCleared.pw_le_exp (Foundations.CoherentMinimizer.two_pos (Γ := Γ)) he
  have old := RationalCubeInfimumName.approximate_attainment A mu d j q p x hc ht
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (RationalAlgebra.positive_product (RationalAlgebra.positive_product
      (RationalAlgebra.positive_product (le_of_eq_add (d := succ two) (by ipra_ring)) (RationalCubeGrid.scale_positive j))
      (RationalCubeGrid.scale_positive q)) (RationalCubeGrid.scale_positive p)) old
  refine le_of_eq_add (d := (scale e+(two*two)*monus (scale j) (scale e))*(scale q*scale p)*(scale q*scale p)) ?_
  have eq := natEq (eq_add_of_le hp)
  apply deriveNat
  ipra_simps
  change 𝔞(scale j) = 𝔞(scale e)+𝔞(monus (scale j) (scale e)) at eq
  linear_combination 4*𝔞(scale q)^2*𝔞(scale p)^2*eq

theorem selected_near (A : PR 3) (mu : PR 2) (d j e x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (he : Γ ⊢[PRAAx] le e j) : Γ ⊢[PRAAx]
    near A mu d x (minimizer A mu d j x) e := by
  refine .allI (.allI ?_)
  have c : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have t : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  have eb : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift j)) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift.shift
  simpa only [Syn.shift,RationalCubeMinimum.subst_minimizer] using selected_near_at A mu
    (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift x)) (var 1) (var 0) c t eb

theorem near_at (A : PR 3) (mu : PR 2) (d x y e p q : PTm n) (h : Γ ⊢[PRAAx] near A mu d x y e) : Γ ⊢[PRAAx]
    nearAt A mu d x y e p q := by
  simpa [near,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using (h.allE p).allE q

theorem uniqueness_at (A : PR 3) (mu u : PR 2) (d x k y z : PTm n) (h : Γ ⊢[PRAAx] uniqueness A mu u d x)
    (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d)
    (hn : Γ ⊢[PRAAx] near A mu d x y (ap2 u k x)) (hm : Γ ⊢[PRAAx] near A mu d x z (ap2 u k x)) :
    Γ ⊢[PRAAx] pointRadius y z d one (scale k) := by
  have law : Γ ⊢[PRAAx] presentedCube y d ⟶ presentedCube z d ⟶ near A mu d x y (ap2 u k x) ⟶
      near A mu d x z (ap2 u k x) ⟶ pointRadius y z d one (scale k) := by
    simpa [uniqueness,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using ((h.allE k).allE y).allE z
  exact .impE (.impE (.impE (.impE law hy) hz) hn) hm

theorem point_presented (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] presentedCube (point A mu u d k x) d := RationalCubeMinimum.minimizer_presented _ _ _ _ _

theorem point_later (A : PR 3) (mu u : PR 2) (d k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hkl : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] pointRadius (point A mu u d k x) (point A mu u d l x) d one (scale k) :=
  uniqueness_at A mu u d x k _ _ hu (point_presented _ _ _ _ _ _) (point_presented _ _ _ _ _ _)
    (selected_near A mu d _ _ x hc ht (schedule_modulus u k k x (le_refl _)))
    (selected_near A mu d _ _ x hc ht (schedule_modulus u k l x hkl))

theorem point_strong (A : PR 3) (mu u : PR 2) (d k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) :
    Γ ⊢[PRAAx] pointRadius (point A mu u d k x) (point A mu u d l x) d one (scale (mn k l)) :=
  uniqueness_at A mu u d x (mn k l) _ _ hu (point_presented _ _ _ _ _ _) (point_presented _ _ _ _ _ _)
    (selected_near A mu d _ _ x hc ht (schedule_modulus u _ _ x (Foundations.CoherentMinimizer.mn_le_left k l)))
    (selected_near A mu d _ _ x hc ht (schedule_modulus u _ _ x (Foundations.CoherentMinimizer.mn_le_right k l)))

theorem point_regular (A : PR 3) (mu u : PR 2) (d k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) : Γ ⊢[PRAAx]
    pointRadius (point A mu u d k x) (point A mu u d l x) d (scale k+scale l) (scale k*scale l) :=
  AggregateChain.point_mono _ _ _ _ _ _ _ (RationalCubeGrid.scale_positive _) (point_strong A mu u d k l x hc ht hu)
    (le_congr (one_mul _).eqSymm (.eqRefl _) (Foundations.CoherentMinimizer.pw_min k l))


def evaluationIndex (mu : PR 2) (p x : PTm n) : PTm n := schedule mu (precision p) x
def evaluation (A : PR 3) (mu u : PR 2) (d p x : PTm n) : PTm n := sample A (point A mu u d (evaluationIndex mu p x) x) (precision p) x
ipra_subst evaluationIndex
ipra_subst evaluation

theorem precision_mono (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (precision p) (precision q) :=
  le_of_eq_add (d := monus q p) ((congrSucc (congrSucc (eq_add_of_le h))).eqTrans (by unfold precision; ipra_ring))
theorem scale_precision_exact (p : PTm n) : Γ ⊢[PRAAx] scale (precision p) ≐ (two*two)*scale p :=
  (RationalCubeMinimum.scale_precision p).eqTrans ((congrMul (pw_succ two p) (.eqRefl two)).eqTrans (by unfold scale; ipra_ring))
theorem evaluation_index_ge (mu : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le (precision p) (evaluationIndex mu p x) := schedule_index _ _ _
theorem evaluation_index_modulus (mu : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le (ap2 mu (precision p) x) (evaluationIndex mu p x) := schedule_modulus _ _ _ _ (le_refl _)
theorem evaluation_index_mono (mu : PR 2) (p q x : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    le (evaluationIndex mu p x) (evaluationIndex mu q x) := schedule_mono _ _ _ _ (precision_mono p q h)

theorem evaluation_distance (A : PR 3) (mu u : PR 2) (d p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    pointRadius (point A mu u d (evaluationIndex mu p x) x) (point A mu u d (evaluationIndex mu q x) x) d one (scale (ap2 mu (precision p) x)) :=
  AggregateChain.point_mono _ _ _ _ _ _ _ (RationalCubeGrid.scale_positive _)
    (point_later A mu u d _ _ x hc ht hu (evaluation_index_mono mu p q x hpq))
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm
      (AnalyticNumberTheory.PowerCleared.pw_le_exp Foundations.CoherentMinimizer.two_pos (evaluation_index_modulus mu p x)))

theorem evaluation_regular_later (A : PR 3) (mu u : PR 2) (d p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu u d p x) (evaluation A mu u d q x) (scale p+scale q) (scale p*scale q) := by
  have h := RationalCubeMinimum.continuity_at A mu d x _ _ (precision p) (precision p) (precision q) ht
    (point_presented _ _ _ _ _ _) (point_presented _ _ _ _ _ _) (evaluation_distance A mu u d p q x hc ht hu hpq)
  apply RationalValueBounds.radius_mono _ _ _ _ _ _ (RationalCubeMinimum.error_denominator_positive _ _ _) h
  refine le_of_eq_add (d := ((two*two)*(two*two))*scale p*scale p*scale q*((succ two)*scale p+two*scale q)) ?_
  apply deriveNat
  simp only [RationalCubeMinimum.errorNumerator,RationalCubeMinimum.errorDenominator]
  ipra_simps
  rw [natEq (scale_precision_exact (Γ := Γ) p),natEq (scale_precision_exact (Γ := Γ) q)]
  ipra_simps
  ring

theorem evaluation_regular (A : PR 3) (mu u : PR 2) (d p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu u d p x) (evaluation A mu u d q x) (scale p+scale q) (scale p*scale q) := by
  refine .orE (le_total p q) (evaluation_regular_later A mu u d p q x hc.wk ht.wk hu.wk Prf.hyp0) ?_
  exact RationalValueBounds.radius_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (RationalValueBounds.radius_symmetric _ _ _ _ (evaluation_regular_later A mu u d q p x hc.wk ht.wk hu.wk Prf.hyp0))

/-- The original canonical evaluation procedure has the infimum value,
with the explicit source half-dyadic evaluation error. -/
theorem evaluation_value (A : PR 3) (mu u : PR 2) (d p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (evaluation A mu u d p x) (value A mu d q x)
      (scale q+two*scale p) (two*scale p*scale q) := by
  let c := two*scale (precision p)
  have h := selected_near_at A mu d (schedule u (evaluationIndex mu p x) x) (precision p) x (precision p) q hc ht
    (le_trans (evaluation_index_ge mu p x) (schedule_index u (evaluationIndex mu p x) x))
  have upper : Γ ⊢[PRAAx] RationalValueBounds.upper (evaluation A mu u d p x) (value A mu d q x)
      (scale q+two*scale p) (two*scale p*scale q) := by
    apply RationalValueBounds.upper_cancel _ _ _ _ c
      (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring)) (RationalCubeGrid.scale_positive _))
    apply RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) _ _ h
    · apply deriveNat
      dsimp [c]
      ipra_simps
      rw [natEq (scale_precision_exact (Γ := Γ) p)]
      ipra_simps
      ring
    · apply deriveNat
      dsimp [c]
      ipra_simps
      rw [natEq (scale_precision_exact (Γ := Γ) p)]
      ipra_simps
      ring
  have lower : Γ ⊢[PRAAx] RationalValueBounds.upper (value A mu d q x) (evaluation A mu u d p x)
      (scale q+two*scale p) (two*scale p*scale q) := by
    apply RationalValueBounds.upper_mono _ _ _ _ _ _
      (RationalAlgebra.positive_product (RationalCubeGrid.scale_positive q) (RationalCubeGrid.scale_positive (precision p)))
      (RationalCubeInfimumName.value_lower_bound A mu d q x _ (precision p) hc ht (point_presented _ _ _ _ _ _))
    refine le_of_eq_add (d := two*scale p*scale q*scale q) ?_
    apply deriveNat
    ipra_simps
    rw [natEq (scale_precision_exact (Γ := Γ) p)]
    ipra_simps
    ring
  exact RationalValueBounds.radius_of_upper _ _ _ _ upper lower


def pointBody (A : PR 3) (mu u : PR 2) : PTm 2 := point A mu u (fstT (var 1)) (var 0) (sndT (var 1))
def pointF (A : PR 3) (mu u : PR 2) : PR 2 := PTm.toPR (pointBody A mu u)
def evaluationBody (A : PR 3) (mu u : PR 2) : PTm 2 := evaluation A mu u (fstT (var 1)) (var 0) (sndT (var 1))
def evaluationF (A : PR 3) (mu u : PR 2) : PR 2 := PTm.toPR (evaluationBody A mu u)

theorem point_at (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    ap2 (pointF A mu u) k (data d x) ≐ point A mu u d k x := by
  simpa [pointF, pointBody, RationalCubeInfimumName.data] using
    (toPR_pair_eq (Γ := Γ) (point A mu u (var 1) (var 0) (var 2)) k d x)
theorem evaluation_at (A : PR 3) (mu u : PR 2) (d p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (evaluationF A mu u) p (data d x) ≐ evaluation A mu u d p x := by
  simpa [evaluationF, evaluationBody, RationalCubeInfimumName.data] using
    (toPR_pair_eq (Γ := Γ) (evaluation A mu u (var 1) (var 0) (var 2)) p d x)

def pointName (f : PR 2) (d z : PTm n) : Fm PTm n := .all (.all
  (pointRadius (ap2 f (var 1) (Syn.shift (Syn.shift z))) (ap2 f (var 0) (Syn.shift (Syn.shift z)))
    (Syn.shift (Syn.shift d)) (scale (var 1)+scale (var 0)) (scale (var 1)*scale (var 0))))
ipra_subst pointName [Syn.subst_shift, Syn.shift_subst]

theorem point_name_radius (A : PR 3) (mu u : PR 2) (d k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) : Γ ⊢[PRAAx]
    pointRadius (ap2 (pointF A mu u) k (data d x)) (ap2 (pointF A mu u) l (data d x)) d (scale k+scale l) (scale k*scale l) :=
  RationalHausdorffConcat.pointRadius_congr (point_at A mu u d k x).eqSymm (point_at A mu u d l x).eqSymm (point_regular A mu u d k l x hc ht hu)

theorem point_fast (A : PR 3) (mu u : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) : Γ ⊢[PRAAx]
    pointName (pointF A mu u) d (data d x) := by
  refine .allI (.allI ?_)
  have c : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have t : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  have u' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] uniqueness A mu u (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_uniqueness,Syn.shift] using hu.shift.shift
  simpa only [Syn.shift,RationalCubeInfimumName.subst_data] using point_name_radius A mu u
    (Syn.shift (Syn.shift d)) (var 1) (var 0) (Syn.shift (Syn.shift x)) c t u'

theorem evaluation_name_radius (A : PR 3) (mu u : PR 2) (d p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 (evaluationF A mu u) p (data d x)) (ap2 (evaluationF A mu u) q (data d x)) (scale p+scale q) (scale p*scale q) :=
  RationalValueBounds.radius_congr (evaluation_at A mu u d p x).eqSymm (evaluation_at A mu u d q x).eqSymm (.eqRefl _) (.eqRefl _)
    (evaluation_regular A mu u d p q x hc ht hu)
theorem evaluation_fast (A : PR 3) (mu u : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hu : Γ ⊢[PRAAx] uniqueness A mu u d x) : Γ ⊢[PRAAx]
    RationalCubeInfimumName.regular (evaluationF A mu u) (data d x) := by
  refine .allI (.allI ?_)
  have c : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have t : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  have u' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] uniqueness A mu u (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_uniqueness,Syn.shift] using hu.shift.shift
  simpa only [Syn.shift,RationalCubeInfimumName.subst_data] using evaluation_name_radius A mu u
    (Syn.shift (Syn.shift d)) (var 1) (var 0) (Syn.shift (Syn.shift x)) c t u'

theorem evaluation_name_value (A : PR 3) (mu u : PR 2) (d p q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 (evaluationF A mu u) p (data d x)) (ap2 (RationalCubeInfimumName.nameF A mu) q (data d x))
      (scale q+two*scale p) (two*scale p*scale q) :=
  RationalValueBounds.radius_congr (evaluation_at A mu u d p x).eqSymm (RationalCubeInfimumName.name_at A mu d q x).eqSymm (.eqRefl _) (.eqRefl _)
    (evaluation_value A mu u d p q x hc ht)

def output (A : PR 3) (mu u : PR 2) (d k x : PTm n) : PTm n := pairT (point A mu u d k x)
  (pairT (evaluation A mu u d k x) (pairT (schedule u k x) (evaluationIndex mu k x)))
def outputF (A : PR 3) (mu u : PR 2) : PR 3 := PTm.toPR (output A mu u (var 0) (var 1) (var 2))
def run (A : PR 3) (mu u : PR 2) (d k x : PTm n) : PTm n := app (outputF A mu u) ![d,k,x]
ipra_subst output
ipra_subst run

theorem program_at (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] run A mu u d k x ≐ output A mu u d k x := by
  simpa [run,outputF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output A mu u (var 0) (var 1) (var 2) : PTm 3) ![d,k,x]
theorem returned_point (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (run A mu u d k x) ≐ point A mu u d k x :=
  (program_at A mu u d k x).fstE
private theorem returned_tail (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (run A mu u d k x) ≐
    pairT (evaluation A mu u d k x) (pairT (schedule u k x) (evaluationIndex mu k x)) :=
  (program_at A mu u d k x).sndE
theorem returned_evaluation (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A mu u d k x)) ≐ evaluation A mu u d k x :=
  (returned_tail A mu u d k x).fstE
private theorem returned_tail2 (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run A mu u d k x)) ≐ pairT (schedule u k x) (evaluationIndex mu k x) :=
  (returned_tail A mu u d k x).sndE
theorem returned_schedule (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A mu u d k x))) ≐ schedule u k x :=
  (returned_tail2 A mu u d k x).fstE
theorem returned_evaluation_index (A : PR 3) (mu u : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run A mu u d k x))) ≐ evaluationIndex mu k x :=
  (returned_tail2 A mu u d k x).sndE

theorem actual_original_majorant_schedule_closed (u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ le (ap2 u (var 0) (var 2)) (schedule u (var 1) (var 2))) :=
  closeUniv 3 (.impI (schedule_modulus u (var 0) (var 1) (var 2) Prf.hyp0))
theorem actual_selected_original_points_presented_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (presentedCube (point A mu u (var 0) (var 1) (var 2)) (var 0)) := closeUniv 3 (point_presented _ _ _ _ _ _)
theorem actual_source_selected_points_strong_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 3) ⟶ continuity A mu (var 0) (var 3) ⟶ uniqueness A mu u (var 0) (var 3) ⟶
      pointRadius (point A mu u (var 0) (var 1) (var 3)) (point A mu u (var 0) (var 2) (var 3)) (var 0) one (scale (mn (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.impI (.impI (point_strong _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_source_coherent_point_name_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶ uniqueness A mu u (var 0) (var 1) ⟶
      pointName (pointF A mu u) (var 0) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (point_fast _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_original_evaluation_schedule_closed (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (precision (var 0)) (evaluationIndex mu (var 0) (var 1)) ⋏ le (ap2 mu (precision (var 0)) (var 1)) (evaluationIndex mu (var 0) (var 1))) :=
  closeUniv 2 (.andI (evaluation_index_ge _ _ _) (evaluation_index_modulus _ _ _))
theorem actual_source_canonical_evaluation_regular_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶ uniqueness A mu u (var 0) (var 1) ⟶
      RationalCubeInfimumName.regular (evaluationF A mu u) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (evaluation_fast _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_source_canonical_evaluation_infimum_value_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 3) ⟶ continuity A mu (var 0) (var 3) ⟶
      RationalValueBounds.radius (ap2 (evaluationF A mu u) (var 1) (data (var 0) (var 3)))
        (ap2 (RationalCubeInfimumName.nameF A mu) (var 2) (data (var 0) (var 3)))
        (scale (var 2)+two*scale (var 1)) (two*scale (var 1)*scale (var 2))) :=
  closeUniv 4 (.impI (.impI (evaluation_name_value _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_coherent_minimizer_point_program_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (pointF A mu u) (var 1) (data (var 0) (var 2)) ≐ point A mu u (var 0) (var 1) (var 2)) := closeUniv 3 (point_at _ _ _ _ _ _)
theorem actual_coherent_minimizer_evaluation_program_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (evaluationF A mu u) (var 1) (data (var 0) (var 2)) ≐ evaluation A mu u (var 0) (var 1) (var 2)) := closeUniv 3 (evaluation_at _ _ _ _ _ _)
theorem actual_coherent_minimizer_output_program_closed (A : PR 3) (mu u : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run A mu u (var 0) (var 1) (var 2) ≐ output A mu u (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalCubeCoherentMinimizer
