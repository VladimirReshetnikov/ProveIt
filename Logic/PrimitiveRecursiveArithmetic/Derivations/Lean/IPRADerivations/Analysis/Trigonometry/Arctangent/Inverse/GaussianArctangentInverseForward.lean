import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentInverseSampler
import IPRADerivations.Analysis.Trigonometry.Arctangent.Comparisons.GaussianArctangentNamedChord
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialUnitEndpoint

/-!
# Forward error of the clamped arctangent inverse observations

The original input angle is bounded by zero and the original quarter
turn, with independent observation precisions. Signed observations
may lie outside their limit interval. The negative, in-range, and
above-range branches all satisfy the same forward dyadic bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentInverseForward

open_ipra
open ComplexLogarithmRemainder (zeroCode eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentClampedTarget (nativeValue cutoff_independent)
open GaussianArctangentExponentialPrefix (prefixValue prefix_zero total)
open GaussianArctangentInverseSampler (ordinate targetNumerator targetDenominator clearing mesh index
  nonpositive_index_zero nonnegative_numerator_value ordinate_represents target_denominator_positive source_certificate
  index_spec mesh_positive)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentPartialUnitEndpoint (unit_endpoint_distance)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianArctangentRationalTarget (targetPoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameRingLaws (zeroF zero_at)
open GaussianRationalHorner (qzero ofGaussian_represents scalar_congr positive_product zero_represents)
open GaussianRationalMetric (comparison_of_cleared)
open GaussianRootAlgebra (im_scale)
open RationalArithmetic (represents order_of_representations)
open RationalSupMetric (numeratorOf)
open RationalValueBounds (upper radius upper_congr radius_congr radius_symmetric radius_mono upper_mono
  upper_of_order upper_of_radius radius_of_upper upper_order_left upper_order_right upper_triangle)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def imaginaryOrder (f g : PR 2) (x y : PTm n) : Fm PTm n := .all (.all
  (upper (ordinate f (var 1) (Syn.shift (Syn.shift x))) (ordinate g (var 0) (Syn.shift (Syn.shift y)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

def input (f : PR 2) (x z : PTm n) : Fm PTm n :=
  pointCN f x ⋏ (imaginaryOrder zeroF f z x ⋏ imaginaryOrder f quarterF x z)

ipra_subst imaginaryOrder [ordinate, Syn.subst_shift, Syn.shift_subst]

ipra_subst input

ipra_subst nativeValue

theorem imaginary_order_at (f g : PR 2) (x y p q : PTm n) (h : Γ ⊢[PRAAx] imaginaryOrder f g x y) :
    Γ ⊢[PRAAx] upper (ordinate f p x) (ordinate g q y) (unit p+unit q) (unit p*unit q) := by
  have hfirst : Γ ⊢[PRAAx] .all (upper (ordinate f (Syn.shift p) (Syn.shift x)) (ordinate g (var 0) (Syn.shift y))
      (unit (Syn.shift p)+unit (var 0)) (unit (Syn.shift p)*unit (var 0))) := by
    simpa only [imaginaryOrder, ordinate, Fm.subst_all, RationalValueBounds.subst_upper, subst_sndT, subst_ap2,
      PTm.subst_add, PTm.subst_mul, GaussianCoefficientNameBounds.subst_unit, Syn.subst_var,
      Syn.up_zero, Syn.up_one, Syn.up_succ, Foundations.BoundedFormulas.subst_up_shift',
      Syn.inst_zero, Syn.subst_inst_shift, Syn.shift_var] using h.allE p
  simpa only [ordinate, RationalValueBounds.subst_upper, subst_sndT, subst_ap2,
    GaussianCoefficientNameBounds.subst_unit, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.inst_succ, Syn.subst_inst_shift] using hfirst.allE q

private theorem same_precision (a b p : PTm n)
    (h : Γ ⊢[PRAAx] upper a b (unit p+unit p) (unit p*unit p)) :
    Γ ⊢[PRAAx] upper a b two (unit p) :=
  upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) h
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl (two*(unit p*unit p))))

theorem upper_sum_same (a b c A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] upper a b A B) (hb : Γ ⊢[PRAAx] upper b c C B) :
    Γ ⊢[PRAAx] upper a c (A+C) B :=
  upper_mono _ _ _ _ _ _ (positive_product _ _ hB hB) (upper_triangle _ _ _ _ _ _ _ ha hb)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl ((A+C)*(B*B))))

private theorem nativeValue_congr {j k : PTm n} (M : PTm n) (h : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] nativeValue j M ≐ nativeValue k M := by
  simpa only [subst_nativeValue, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
    Prf.eqCongr (nativeValue (var 0) (var 1) : PTm 2) (σ := ![j,M]) (σ' := ![k,M]) (fun i => by
      fin_cases i
      · exact h
      · exact .eqRefl M)

private theorem prefix_ordinate_represents (j M L : PTm n) :
    Γ ⊢[PRAAx] represents (sndT (prefixValue j M L)) (ZT.ofNat (two*total j M L)) (fact L) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (ofGaussian_represents _ _ (GaussianRationalPolynomialExponential.factorial_positive L)).andE₂
  apply ZT.derive
  simp only [im_scale, imaginaryCode, eval_im_code, ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem target_ordinate_represents (Q D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] represents (sndT (targetPoint Q D)) (ZT.ofNat Q) D := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ hD).andE₂
  apply ZT.derive
  simp only [im_scale, imaginaryCode, eval_im_code, ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem nonnegative_ordinate (f : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).neg (numeratorOf (ordinate f p x)).pos) :
    Γ ⊢[PRAAx] represents (ordinate f p x) (ZT.ofNat (targetNumerator f p x)) (targetDenominator f p x) :=
  scalar_congr (.eqRefl _) (ZT.derive (nonnegative_numerator_value f p x h).symm) (.eqRefl _)
    (ordinate_represents f p x)

private theorem nonpositive_ordinate (f : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).pos (numeratorOf (ordinate f p x)).neg) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (ordinate f p x) (sndT qzero) := by
  let r := numeratorOf (ordinate f p x)
  let D := targetDenominator f p x
  have hz : Γ ⊢[PRAAx] represents (sndT qzero) (ZT.ofNat zero) one := by
    apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (zero_represents one).andE₂
    apply ZT.derive
    simp [zeroCode, eval_im_code, ZT.toZ_ofNat]
  apply order_of_representations _ _ r (ZT.ofNat zero) D one (ordinate_represents f p x) hz
    (RationalArgmin.denominator_positive (ordinate f p x)) (le_refl one)
  apply zle_of_toZ (monus r.neg r.pos)
  have eq := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul, ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  dsimp only [r]
  linear_combination -eq

private theorem endpoint_at (p : PTm n) :
    Γ ⊢[PRAAx] ap2 GaussianArctangentPartialQuadrature.nameF p (GaussianArctangentPartialQuadrature.data one one) ≐
      nativeValue (mesh p) (mesh p) := by
  have e := Prf.eqCongr (Γ := Γ) (nativeValue (var 0) (var 0) : PTm 1)
    (σ := fun _ => one*mesh p) (σ' := fun _ => mesh p) (fun _ => one_mul (mesh p))
  refine (GaussianArctangentPartialQuadrature.sample_at p one one).eqTrans ?_
  change Γ ⊢[PRAAx] nativeValue (one*mesh p) (one*mesh p) ≐ nativeValue (mesh p) (mesh p)
  simpa only [subst_nativeValue, Syn.subst_var] using e

private theorem endpoint_radius (p z : PTm n) :
    Γ ⊢[PRAAx] radius (ordinate quarterF p z) (sndT (nativeValue (mesh p) (mesh p))) (num 5) (unit p) := by
  have h := imaginary_coordinate_radius (Γ := Γ) _ _ _ _ (unit_positive p) (unit_endpoint_distance p z)
  exact radius_symmetric _ _ _ _ (radius_congr (congrSnd (endpoint_at p)) (.eqRefl _) (.eqRefl _) (.eqRefl _) h)

private theorem negative_branch (f : PR 2) (p x z : PTm n) (h : Γ ⊢[PRAAx] input f x z)
    (hn : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).pos (numeratorOf (ordinate f p x)).neg) :
    Γ ⊢[PRAAx] radius (sndT (nativeValue (index f p x) (mesh p))) (ordinate f p x) (num 7) (unit p) := by
  have e := (nativeValue_congr (mesh p) (nonpositive_index_zero f p x hn)).eqTrans (prefix_zero _ _)
  have low := same_precision _ _ p (imaginary_order_at zeroF f z x p p h.andE₂.andE₁)
  have lo := upper_congr (congrSnd (zero_at p z)) (.eqRefl _) (.eqRefl _) (.eqRefl _) low
  have lhs := upper_mono _ _ two (unit p) (num 7) (unit p) (unit_positive p) lo (by ipra_le 5*𝔞 (unit p))
  have rhs := upper_of_order _ _ (num 7) (unit p) (nonpositive_ordinate f p x hn)
  exact radius_congr (congrSnd e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (radius_of_upper _ _ _ _ lhs rhs)

private theorem in_range_branch (f : PR 2) (p x : PTm n)
    (hs : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).neg (numeratorOf (ordinate f p x)).pos)
    (hr : Γ ⊢[PRAAx] GaussianArctangentClampedTarget.upper (targetNumerator f p x) (targetDenominator f p x)
      (mesh p) (clearing f p x)) :
    Γ ⊢[PRAAx] radius (sndT (nativeValue (index f p x) (mesh p))) (ordinate f p x) (num 7) (unit p) := by
  let Q := targetNumerator f p x
  let D := targetDenominator f p x
  let a := sndT (nativeValue (index f p x) (mesh p))
  let b := sndT (targetPoint Q D)
  let r := ordinate f p x
  have hD := target_denominator_positive (Γ := Γ) f p x
  have hM := mesh_positive (Γ := Γ) p
  have d : Γ ⊢[PRAAx] radius a b two (mesh p) :=
    imaginary_coordinate_radius _ _ _ _ hM (.impE (index_spec f p x).andE₂.andE₁ hr)
  have hq := target_ordinate_represents Q D hD
  have hs' := nonnegative_ordinate f p x hs
  have br : Γ ⊢[PRAAx] RationalArgmin.rationalLE b r := comparison_of_cleared _ _ _ _ _ _ hD hD hq hs'
    (le_congr (.eqRefl _) (mul_comm _ _) (le_refl _))
  have rb : Γ ⊢[PRAAx] RationalArgmin.rationalLE r b := comparison_of_cleared _ _ _ _ _ _ hD hD hs' hq
    (le_congr (.eqRefl _) (mul_comm _ _) (le_refl _))
  have atMesh := radius_of_upper a r two (mesh p)
    (upper_order_right a b r two (mesh p) (upper_of_radius _ _ _ _ d) br)
    (upper_order_left r b a two (mesh p) rb (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ d)))
  exact radius_mono _ _ two (mesh p) (num 7) (unit p) hM atMesh (by unfold mesh GaussianArctangentPartialQuadrature.mesh; ipra_le 26*𝔞 (unit p))

private theorem above_branch (f : PR 2) (p x z : PTm n) (h : Γ ⊢[PRAAx] input f x z)
    (hs : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).neg (numeratorOf (ordinate f p x)).pos)
    (hr : Γ ⊢[PRAAx] GaussianArctangentClampedTarget.above (targetNumerator f p x) (targetDenominator f p x)
      (mesh p) (clearing f p x)) :
    Γ ⊢[PRAAx] radius (sndT (nativeValue (index f p x) (mesh p))) (ordinate f p x) (num 7) (unit p) := by
  let Q := targetNumerator f p x
  let D := targetDenominator f p x
  let M := mesh p
  let L := clearing f p x
  let a := sndT (nativeValue M M)
  let r := ordinate f p x
  let b := ordinate quarterF p z
  have hsrc := source_certificate (Γ := Γ) f p x
  have hD := target_denominator_positive (Γ := Γ) f p x
  have hc : Γ ⊢[PRAAx] nativeValue M M ≐ prefixValue M M L :=
    cutoff_independent _ _ _ _ (.andI hsrc.andE₁ (le_refl _)) hsrc (le_refl _)
  have exactOrder : Γ ⊢[PRAAx] RationalArgmin.rationalLE a r := by
    have hp := scalar_congr (congrSnd hc).eqSymm (.eqRefl _) (.eqRefl _) (prefix_ordinate_represents M M L)
    have hl : Γ ⊢[PRAAx] le ((two*D)*total M M L) (Q*fact L) :=
      le_trans (le_succ_self _) hr
    exact comparison_of_cleared _ _ _ _ _ _ (GaussianRationalPolynomialExponential.factorial_positive L) hD hp
      (nonnegative_ordinate f p x hs) (le_congr (by ipra_ring) (.eqRefl _) hl)
  have low := upper_of_order _ _ (num 7) (unit p) exactOrder
  have top := same_precision _ _ p (imaginary_order_at f quarterF x z p p h.andE₂.andE₂)
  have upperRaw := upper_sum_same r b a two (num 5) (unit p) (unit_positive p) top
    (upper_of_radius _ _ _ _ (endpoint_radius p z))
  have top' : Γ ⊢[PRAAx] upper r a (num 7) (unit p) :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) upperRaw
  have ei : Γ ⊢[PRAAx] nativeValue (index f p x) M ≐ nativeValue M M :=
    .impE (index_spec f p x).andE₂.andE₂ hr
  exact radius_congr (congrSnd ei).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (radius_of_upper _ _ _ _ low top')

theorem forward_at (f : PR 2) (p x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] radius (sndT (nativeValue (index f p x) (mesh p))) (ordinate f p x) (num 7) (unit p) := by
  let r := numeratorOf (ordinate f p x)
  refine .orE (le_total r.pos r.neg) (negative_branch f p x z h.wk Prf.hyp0) ?_
  let Q := targetNumerator f p x
  let D := targetDenominator f p x
  let M := mesh p
  let L := clearing f p x
  refine .orE (lt_or_le ((two*D)*total M M L) (Q*fact L)) ?_ ?_
  · exact above_branch f p x z h.wk.wk Prf.hyp1 Prf.hyp0
  · exact in_range_branch f p x Prf.hyp1 Prf.hyp0

theorem actual_arctangent_inverse_forward_error_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 1) (var 2) ⟶
      radius (sndT (nativeValue (index f (var 0) (var 1)) (mesh (var 0))))
        (ordinate f (var 0) (var 1)) (num 7) (unit (var 0))) :=
  closeUniv 3 (.impI (forward_at f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentInverseForward
