import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals

/-!
# Actual signed running intersections and their infimum value name

The running endpoints are actual bounded rational argmin programs, with
numerator swap for the lower maximum. The midpoint program is canonical.
All interval and name laws follow from the original sampler hypotheses;
no consistency or regularity law is supplied for the output.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeInfimumName

open_ipra
open RationalCubeMinimum (coherence continuity)
open RationalCubeGrid (scale)
open RationalArgmin (rationalLE)
open RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters (midpoint)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def data (d x : PTm n) : PTm n := pairT d x
def lowerBody (A : PR 3) (mu : PR 2) : PTm 2 := RationalValueBounds.negate
  (RationalCubeInfimumIntervals.lower A mu (fstT (var 1)) (var 0) (sndT (var 1)))
def upperBody (A : PR 3) (mu : PR 2) : PTm 2 :=
  RationalCubeInfimumIntervals.upper A mu (fstT (var 1)) (var 0) (sndT (var 1))
def lowerF (A : PR 3) (mu : PR 2) : PR 2 := PTm.toPR (lowerBody A mu)
def upperF (A : PR 3) (mu : PR 2) : PR 2 := PTm.toPR (upperBody A mu)
def lowerIndex (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := RationalArgmin.selected (lowerF A mu) k (data d x)
def upperIndex (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := RationalArgmin.selected (upperF A mu) k (data d x)
def lower (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n :=
  RationalCubeInfimumIntervals.lower A mu d (lowerIndex A mu d k x) x
def upper (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n :=
  RationalCubeInfimumIntervals.upper A mu d (upperIndex A mu d k x) x
def value (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := midpoint (lower A mu d k x) (upper A mu d k x)

ipra_subst data
ipra_subst lowerIndex
ipra_subst upperIndex
ipra_subst lower
ipra_subst upper
ipra_subst value

theorem lower_program_at (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.value (lowerF A mu) k (data d x) ≐ RationalValueBounds.negate (RationalCubeInfimumIntervals.lower A mu d k x) := by
  simpa [RationalArgmin.value, lowerF, lowerBody, data] using
    (toPR_pair_eq (Γ := Γ)
      (RationalValueBounds.negate (RationalCubeInfimumIntervals.lower A mu (var 1) (var 0) (var 2))) k d x)
theorem upper_program_at (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.value (upperF A mu) k (data d x) ≐ RationalCubeInfimumIntervals.upper A mu d k x := by
  simpa [RationalArgmin.value, upperF, upperBody, data] using
    (toPR_pair_eq (Γ := Γ) (RationalCubeInfimumIntervals.upper A mu (var 1) (var 0) (var 2)) k d x)

theorem lower_index_bound (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] le (lowerIndex A mu d k x) k := RationalArgmin.selected_spec _ _ _
theorem upper_index_bound (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] le (upperIndex A mu d k x) k := RationalArgmin.selected_spec _ _ _

theorem lower_maximal (A : PR 3) (mu : PR 2) (d k x i : PTm n) (hi : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx]
    rationalLE (RationalCubeInfimumIntervals.lower A mu d i x) (lower A mu d k x) := by
  have h := RationalArgmin.rationalLE_congr (lower_program_at A mu d (lowerIndex A mu d k x) x)
    (lower_program_at A mu d i x) (RationalArgmin.selected_minimal (lowerF A mu) k i (data d x) hi)
  exact le_congr (RationalValueBounds.crossLeft_negate _ _) (RationalValueBounds.crossLeft_negate _ _) h

theorem upper_minimal (A : PR 3) (mu : PR 2) (d k x i : PTm n) (hi : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx]
    rationalLE (upper A mu d k x) (RationalCubeInfimumIntervals.upper A mu d i x) :=
  RationalArgmin.rationalLE_congr (upper_program_at A mu d (upperIndex A mu d k x) x)
    (upper_program_at A mu d i x) (RationalArgmin.selected_minimal (upperF A mu) k i (data d x) hi)

theorem lower_nested (A : PR 3) (mu : PR 2) (d k l x : PTm n) (hkl : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] rationalLE (lower A mu d k x) (lower A mu d l x) :=
  lower_maximal A mu d l x _ (le_trans (lower_index_bound A mu d k x) hkl)
theorem upper_nested (A : PR 3) (mu : PR 2) (d k l x : PTm n) (hkl : Γ ⊢[PRAAx] le k l) :
    Γ ⊢[PRAAx] rationalLE (upper A mu d l x) (upper A mu d k x) :=
  upper_minimal A mu d l x _ (le_trans (upper_index_bound A mu d k x) hkl)

theorem cross_order (A : PR 3) (mu : PR 2) (d x k l : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] rationalLE (lower A mu d k x) (upper A mu d l x) :=
  RationalCubeInfimumIntervals.cross_order A mu d x _ _ hc ht

theorem width (A : PR 3) (mu : PR 2) (d k x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (upper A mu d k x) (lower A mu d k x) (succ two) ((two*two)*scale k) :=
  RationalValueBounds.radius_of_upper _ _ _ _
    (RationalValueBounds.upper_order_left _ _ _ _ _ (upper_minimal A mu d k x k (le_refl _))
      (RationalValueBounds.upper_order_right _ _ _ _ _
        (RationalValueBounds.upper_of_radius _ _ _ _ (RationalCubeInfimumIntervals.original_width A mu d k x))
        (lower_maximal A mu d k x k (le_refl _))))
    (RationalValueBounds.upper_of_order _ _ _ _ (cross_order A mu d x k k hc ht))

theorem midpoint_lower (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE a b) :
    Γ ⊢[PRAAx] rationalLE a (midpoint a b) := by
  have e := RationalArgmin.rationalLE_congr (RationalAlgebra.midpoint_self a) (.eqRefl _)
    (RationalAlgebra.midpoint_monotone a a a b (RationalArgmin.reflexive _) h)
  exact RationalArgmin.transitive (RationalArgmin.eq_le (RationalArithmetic.recode_equal a).eqSymm) e
theorem midpoint_upper (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE a b) :
    Γ ⊢[PRAAx] rationalLE (midpoint a b) b := by
  have e := RationalArgmin.rationalLE_congr (.eqRefl _) (RationalAlgebra.midpoint_self b)
    (RationalAlgebra.midpoint_monotone a b b b h (RationalArgmin.reflexive _))
  exact RationalArgmin.transitive e (RationalArgmin.eq_le (RationalArithmetic.recode_equal b))

theorem value_lower (A : PR 3) (mu : PR 2) (d k x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] rationalLE (lower A mu d k x) (value A mu d k x) :=
  midpoint_lower _ _ (cross_order A mu d x k k hc ht)
theorem value_upper (A : PR 3) (mu : PR 2) (d k x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] rationalLE (value A mu d k x) (upper A mu d k x) :=
  midpoint_upper _ _ (cross_order A mu d x k k hc ht)
theorem value_canonical (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (value A mu d k x) :=
  RationalNormalForm.normalize_well_formed _ _ (LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters.midpoint_denominator_positive _ _)

/-- Any two genuine members of one ordered interval share its proved width. -/
theorem interval_radius (a b u v P Q : PTm n) (hau : Γ ⊢[PRAAx] rationalLE a u) (hub : Γ ⊢[PRAAx] rationalLE u b)
    (hav : Γ ⊢[PRAAx] rationalLE a v) (hvb : Γ ⊢[PRAAx] rationalLE v b)
    (hw : Γ ⊢[PRAAx] RationalValueBounds.radius b a P Q) : Γ ⊢[PRAAx] RationalValueBounds.radius u v P Q := by
  have h := RationalValueBounds.upper_of_radius _ _ _ _ hw
  exact RationalValueBounds.radius_of_upper _ _ _ _
    (RationalValueBounds.upper_order_left _ _ _ _ _ hub (RationalValueBounds.upper_order_right _ _ _ _ _ h hav))
    (RationalValueBounds.upper_order_left _ _ _ _ _ hvb (RationalValueBounds.upper_order_right _ _ _ _ _ h hau))

theorem value_later_radius (A : PR 3) (mu : PR 2) (d k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (value A mu d k x) (value A mu d l x) (succ two) ((two*two)*scale k) :=
  interval_radius _ _ _ _ _ _ (value_lower A mu d k x hc ht)
    (value_upper A mu d k x hc ht)
    (RationalArgmin.transitive (lower_nested A mu d k l x hkl) (value_lower A mu d l x hc ht))
    (RationalArgmin.transitive (value_upper A mu d l x hc ht) (upper_nested A mu d k l x hkl)) (width A mu d k x hc ht)

theorem value_regular (A : PR 3) (mu : PR 2) (d k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (value A mu d k x) (value A mu d l x) (scale k+scale l) (scale k*scale l) := by
  refine .orE (le_total k l) ?_ ?_
  · apply RationalValueBounds.radius_mono _ _ _ _ _ _ (RationalAlgebra.positive_product (le_of_eq_add (d := succ two) (by ipra_ring)) (RationalCubeGrid.scale_positive k))
      (value_later_radius A mu d k l x hc.wk ht.wk Prf.hyp0)
    exact le_of_eq_add (d := scale k*scale l+((two*two)*scale k)*scale k) (by ipra_ring)
  · have h := RationalValueBounds.radius_symmetric _ _ _ _ (value_later_radius A mu d l k x hc.wk ht.wk Prf.hyp0)
    apply RationalValueBounds.radius_mono _ _ _ _ _ _ (RationalAlgebra.positive_product (le_of_eq_add (d := succ two) (by ipra_ring)) (RationalCubeGrid.scale_positive l)) h
    exact le_of_eq_add (d := scale k*scale l+((two*two)*scale l)*scale l) (by ipra_ring)


/-- The actual midpoint consumes half the original one-sided width. -/
theorem midpoint_half_left (a b P Q : PTm n) (h : Γ ⊢[PRAAx] RationalValueBounds.upper b a P Q) :
    Γ ⊢[PRAAx] RationalValueBounds.upper (midpoint a b) a P (two*Q) := by
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _
    (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring))
      (RationalArithmetic.product_denominator_positive a b)) (RationalArgmin.denominator_positive a)
    (RationalAlgebra.midpoint_value a b) (RationalRepresentations.represents_self a)
  let gap := monus (Q*RationalValueBounds.crossLeft a b+P*denominatorOf b*denominatorOf a)
    (Q*RationalValueBounds.crossLeft b a)
  apply zle_of_toZ (two*denominatorOf a*gap)
  have e := natEq (eq_add_of_le h)
  simp only [RationalArithmetic.addNumerator,RationalArithmetic.productDenominator,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  dsimp [gap]
  unfold RationalValueBounds.crossLeft at e ⊢
  ipra_simps
  linear_combination -2*𝔞(denominatorOf a)*e

theorem midpoint_half_right (a b P Q : PTm n) (h : Γ ⊢[PRAAx] RationalValueBounds.upper b a P Q) :
    Γ ⊢[PRAAx] RationalValueBounds.upper b (midpoint a b) P (two*Q) := by
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _
    (RationalArgmin.denominator_positive b)
    (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring))
      (RationalArithmetic.product_denominator_positive a b))
    (RationalRepresentations.represents_self b) (RationalAlgebra.midpoint_value a b)
  let gap := monus (Q*RationalValueBounds.crossLeft a b+P*denominatorOf b*denominatorOf a)
    (Q*RationalValueBounds.crossLeft b a)
  apply zle_of_toZ (two*denominatorOf b*gap)
  have e := natEq (eq_add_of_le h)
  simp only [RationalArithmetic.addNumerator,RationalArithmetic.productDenominator,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  dsimp [gap]
  unfold RationalValueBounds.crossLeft at e ⊢
  ipra_simps
  linear_combination -2*𝔞(denominatorOf b)*e

theorem lower_sample (A : PR 3) (mu : PR 2) (d k x y p : PTm n) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hy : Γ ⊢[PRAAx] RationalCubeMinimum.presentedCube y d) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (lower A mu d k x) (RationalCubeMinimum.sample A y p x) one (scale p) :=
  RationalCubeInfimumIntervals.lower_sample A mu d _ x y p ht hy

theorem value_above_lower (A : PR 3) (mu : PR 2) (d k x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (value A mu d k x) (lower A mu d k x) (succ two) (two*((two*two)*scale k)) :=
  midpoint_half_left _ _ _ _ (RationalValueBounds.upper_of_radius _ _ _ _ (width A mu d k x hc ht))

theorem upper_above_value (A : PR 3) (mu : PR 2) (d k x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (upper A mu d k x) (value A mu d k x) (succ two) (two*((two*two)*scale k)) :=
  midpoint_half_right _ _ _ _ (RationalValueBounds.upper_of_radius _ _ _ _ (width A mu d k x hc ht))

/-- The regular-name lower-bound inequality, with both actual queries internal. -/
theorem value_lower_bound (A : PR 3) (mu : PR 2) (d k x y p : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hy : Γ ⊢[PRAAx] RationalCubeMinimum.presentedCube y d) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (value A mu d k x) (RationalCubeMinimum.sample A y p x)
      (scale k+scale p) (scale k*scale p) := by
  have h := RationalValueBounds.upper_triangle _ _ _ _ _ _ _
    (value_above_lower A mu d k x hc ht) (lower_sample A mu d k x y p ht hy)
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (RationalAlgebra.positive_product
      (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring))
        (RationalAlgebra.positive_product (le_of_eq_add (d := succ two) (by ipra_ring)) (RationalCubeGrid.scale_positive k)))
      (RationalCubeGrid.scale_positive p)) h
  exact le_of_eq_add (d := (succ (two*two))*scale k*scale p*scale p) (by ipra_ring)

/-- Every original lower endpoint lies below the value name. -/
theorem original_lower_value (A : PR 3) (mu : PR 2) (d k q x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (RationalCubeInfimumIntervals.lower A mu d k x) (value A mu d q x) one (scale q) := by
  have h := RationalValueBounds.upper_order_left _ _ _ _ _
    (RationalCubeInfimumIntervals.cross_order A mu d x k (upperIndex A mu d q x) hc ht)
    (upper_above_value A mu d q x hc ht)
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (RationalAlgebra.positive_product (le_of_eq_add (d := one) (by ipra_ring))
      (RationalAlgebra.positive_product (le_of_eq_add (d := succ two) (by ipra_ring)) (RationalCubeGrid.scale_positive q))) h
  exact le_of_eq_add (d := (succ (two*two))*scale q) (by ipra_ring)

/-- Source approximate attainment at the actual grid minimizer, unfolded
at arbitrary finite function and infimum-name precisions. -/
theorem approximate_attainment (A : PR 3) (mu : PR 2) (d k q p x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (RationalCubeMinimum.sample A (RationalCubeMinimum.minimizer A mu d k x) p x)
      (value A mu d q x) ((succ two)*scale q*scale p+((two*two)*scale k)*(scale q+scale p))
      (((two*two)*scale k)*scale q*scale p) := by
  have a := RationalCubeInfimumIntervals.selected_sample A mu d k x p hc
  have b := RationalValueBounds.upper_of_radius (Γ := Γ) _ _ _ _ (RationalCubeInfimumIntervals.original_width A mu d k x)
  have c := original_lower_value A mu d k q x hc ht
  exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (RationalValueBounds.upper_triangle _ _ _ _ _ _ _ a (RationalValueBounds.upper_triangle _ _ _ _ _ _ _ b c))


def nameBody (A : PR 3) (mu : PR 2) : PTm 2 := value A mu (fstT (var 1)) (var 0) (sndT (var 1))
def nameF (A : PR 3) (mu : PR 2) : PR 2 := PTm.toPR (nameBody A mu)
theorem name_at (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF A mu) k (data d x) ≐ value A mu d k x := by
  simpa [nameF, nameBody, data] using
    (toPR_pair_eq (Γ := Γ) (value A mu (var 1) (var 0) (var 2)) k d x)

def regular (f : PR 2) (x : PTm n) : Fm PTm n := .all (.all
  (RationalValueBounds.radius (ap2 f (var 1) (Syn.shift (Syn.shift x))) (ap2 f (var 0) (Syn.shift (Syn.shift x)))
    (scale (var 1)+scale (var 0)) (scale (var 1)*scale (var 0))))
ipra_subst regular [Syn.subst_shift, Syn.shift_subst]

theorem name_radius (A : PR 3) (mu : PR 2) (d k l x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 (nameF A mu) k (data d x)) (ap2 (nameF A mu) l (data d x))
      (scale k+scale l) (scale k*scale l) :=
  RationalValueBounds.radius_congr (name_at A mu d k x).eqSymm (name_at A mu d l x).eqSymm (.eqRefl _) (.eqRefl _)
    (value_regular A mu d k l x hc ht)

theorem name_regular (A : PR 3) (mu : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] regular (nameF A mu) (data d x) := by
  refine .allI (.allI ?_)
  have c : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] coherence A (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift
  have t : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] continuity A mu (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift
  simpa only [Syn.shift,subst_data] using name_radius A mu (Syn.shift (Syn.shift d)) (var 1) (var 0) (Syn.shift (Syn.shift x)) c t

theorem name_canonical (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (ap2 (nameF A mu) k (data d x)) :=
  RationalCubeMinimum.well_formed_congr (name_at A mu d k x).eqSymm (value_canonical A mu d k x)

def output (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := pairT (value A mu d k x)
  (pairT (lower A mu d k x) (pairT (upper A mu d k x)
    (pairT (lowerIndex A mu d k x) (pairT (upperIndex A mu d k x) (RationalCubeMinimum.minimizer A mu d k x)))))
def outputF (A : PR 3) (mu : PR 2) : PR 3 := PTm.toPR (output A mu (var 0) (var 1) (var 2))
def run (A : PR 3) (mu : PR 2) (d k x : PTm n) : PTm n := app (outputF A mu) ![d,k,x]
ipra_subst output
ipra_subst run

theorem program_at (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] run A mu d k x ≐ output A mu d k x := by
  simpa [run,outputF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output A mu (var 0) (var 1) (var 2) : PTm 3) ![d,k,x]
theorem returned_value (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (run A mu d k x) ≐ value A mu d k x :=
  (program_at A mu d k x).fstE
private theorem returned_tail (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (run A mu d k x) ≐
    pairT (lower A mu d k x) (pairT (upper A mu d k x) (pairT (lowerIndex A mu d k x) (pairT (upperIndex A mu d k x) (RationalCubeMinimum.minimizer A mu d k x)))) :=
  (program_at A mu d k x).sndE
theorem returned_lower (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A mu d k x)) ≐ lower A mu d k x :=
  (returned_tail A mu d k x).fstE
private theorem returned_tail2 (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run A mu d k x)) ≐
    pairT (upper A mu d k x) (pairT (lowerIndex A mu d k x) (pairT (upperIndex A mu d k x) (RationalCubeMinimum.minimizer A mu d k x))) :=
  (returned_tail A mu d k x).sndE
theorem returned_upper (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A mu d k x))) ≐ upper A mu d k x :=
  (returned_tail2 A mu d k x).fstE
private theorem returned_tail3 (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run A mu d k x))) ≐
    pairT (lowerIndex A mu d k x) (pairT (upperIndex A mu d k x) (RationalCubeMinimum.minimizer A mu d k x)) :=
  (returned_tail2 A mu d k x).sndE
theorem returned_lower_index (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run A mu d k x)))) ≐ lowerIndex A mu d k x :=
  (returned_tail3 A mu d k x).fstE
private theorem returned_tail4 (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run A mu d k x)))) ≐
    pairT (upperIndex A mu d k x) (RationalCubeMinimum.minimizer A mu d k x) :=
  (returned_tail3 A mu d k x).sndE
theorem returned_upper_index (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run A mu d k x))))) ≐ upperIndex A mu d k x :=
  (returned_tail4 A mu d k x).fstE
theorem returned_minimizer (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run A mu d k x))))) ≐ RationalCubeMinimum.minimizer A mu d k x :=
  (returned_tail4 A mu d k x).sndE

theorem returned_width (A : PR 3) (mu : PR 2) (d k x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (fstT (sndT (sndT (run A mu d k x)))) (fstT (sndT (run A mu d k x))) (succ two) ((two*two)*scale k) :=
  RationalValueBounds.radius_congr (returned_upper A mu d k x).eqSymm (returned_lower A mu d k x).eqSymm (.eqRefl _) (.eqRefl _) (width A mu d k x hc ht)

theorem actual_running_interval_indices_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (lowerIndex A mu (var 0) (var 1) (var 2)) (var 1) ⋏ le (upperIndex A mu (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.andI (lower_index_bound _ _ _ _ _) (upper_index_bound _ _ _ _ _))
theorem actual_running_interval_extrema_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ (rationalLE (RationalCubeInfimumIntervals.lower A mu (var 0) (var 3) (var 2)) (lower A mu (var 0) (var 1) (var 2)) ⋏
      rationalLE (upper A mu (var 0) (var 1) (var 2)) (RationalCubeInfimumIntervals.upper A mu (var 0) (var 3) (var 2)))) :=
  closeUniv 4 (.impI (.andI (lower_maximal _ _ _ _ _ _ Prf.hyp0) (upper_minimal _ _ _ _ _ _ Prf.hyp0)))
theorem actual_running_intervals_nested_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 1) (var 3) ⟶ (rationalLE (lower A mu (var 0) (var 1) (var 2)) (lower A mu (var 0) (var 3) (var 2)) ⋏
      rationalLE (upper A mu (var 0) (var 3) (var 2)) (upper A mu (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (.andI (lower_nested _ _ _ _ _ _ Prf.hyp0) (upper_nested _ _ _ _ _ _ Prf.hyp0)))
theorem actual_running_intervals_cross_order_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶
      rationalLE (lower A mu (var 0) (var 2) (var 1)) (upper A mu (var 0) (var 3) (var 1))) :=
  closeUniv 4 (.impI (.impI (cross_order _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_running_interval_width_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (coherence A (var 0) (var 2) ⟶ continuity A mu (var 0) (var 2) ⟶
      RationalValueBounds.radius (upper A mu (var 0) (var 1) (var 2)) (lower A mu (var 0) (var 1) (var 2)) (succ two) ((two*two)*scale (var 1))) :=
  closeUniv 3 (.impI (.impI (width _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_infimum_midpoint_canonical_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalNormalForm.wellFormed (value A mu (var 0) (var 1) (var 2))) := closeUniv 3 (value_canonical _ _ _ _ _)
theorem actual_infimum_midpoint_regular_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 3) ⟶ continuity A mu (var 0) (var 3) ⟶
      RationalValueBounds.radius (value A mu (var 0) (var 1) (var 3)) (value A mu (var 0) (var 2) (var 3))
        (scale (var 1)+scale (var 2)) (scale (var 1)*scale (var 2))) :=
  closeUniv 4 (.impI (.impI (value_regular _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_infimum_lower_bound_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coherence A (var 0) (var 2) ⟶ continuity A mu (var 0) (var 2) ⟶ RationalCubeMinimum.presentedCube (var 3) (var 0) ⟶
      RationalValueBounds.upper (value A mu (var 0) (var 1) (var 2)) (RationalCubeMinimum.sample A (var 3) (var 4) (var 2))
        (scale (var 1)+scale (var 4)) (scale (var 1)*scale (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (value_lower_bound _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_infimum_approximate_attainment_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coherence A (var 0) (var 4) ⟶ continuity A mu (var 0) (var 4) ⟶
      RationalValueBounds.upper (RationalCubeMinimum.sample A (RationalCubeMinimum.minimizer A mu (var 0) (var 1) (var 4)) (var 3) (var 4))
        (value A mu (var 0) (var 2) (var 4))
        ((succ two)*scale (var 2)*scale (var 3)+((two*two)*scale (var 1))*(scale (var 2)+scale (var 3)))
        (((two*two)*scale (var 1))*scale (var 2)*scale (var 3))) :=
  closeUniv 5 (.impI (.impI (approximate_attainment _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_infimum_name_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (nameF A mu) (var 1) (data (var 0) (var 2)) ≐ value A mu (var 0) (var 1) (var 2)) := closeUniv 3 (name_at _ _ _ _ _)
theorem actual_infimum_name_regular_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶ regular (nameF A mu) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (name_regular _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_infimum_output_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run A mu (var 0) (var 1) (var 2) ≐ output A mu (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _ _ _)
theorem actual_returned_infimum_interval_width_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (coherence A (var 0) (var 2) ⟶ continuity A mu (var 0) (var 2) ⟶
      RationalValueBounds.radius (fstT (sndT (sndT (run A mu (var 0) (var 1) (var 2))))) (fstT (sndT (run A mu (var 0) (var 1) (var 2))))
        (succ two) ((two*two)*scale (var 1))) := closeUniv 3 (.impI (.impI (returned_width _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCubeInfimumName
