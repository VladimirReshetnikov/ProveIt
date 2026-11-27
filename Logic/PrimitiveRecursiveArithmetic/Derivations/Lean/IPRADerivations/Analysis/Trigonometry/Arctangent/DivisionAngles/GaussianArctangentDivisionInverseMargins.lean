import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngleGaps
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialUnitEndpoint
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.Coordinates.GaussianArctangentCayleySquareGap
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalUpperAddition

/-!
# Common-mesh inverse margins for divided angles

At a sufficiently fine common query, the raw inverse indices have
positive margins from zero, from each other, and from the mesh end.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionInverseMargins

open_ipra
open BaselQuadrature (Qb)
open ComplexLogarithmRemainder (eval_im_code eval_re_code scale zeroCode)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentCayleySquareGap (marginSource)
open GaussianArctangentClampedTarget (nativeValue)
open GaussianArctangentDivisionAngles (nameF data clock modulus odd_source interval_input sample_at sample_represents
  quarterNumerator quarterDenominator)
open GaussianArctangentDivisionAngleGaps (ordinate quarterOrdinate gap_at top_margin_at)
open GaussianArctangentExponentialPrefix (source total prefix_zero)
open GaussianArctangentInverseSampler (index mesh mesh_positive index_le)
open GaussianArctangentInverseForward (forward_at subst_nativeValue)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (point_at)
open GaussianRationalHorner (positive_product ofGaussian_represents scalar_congr canonical_congr qmul_canonical
  canonical_unique qzero zero_represents represents_congr)
open GaussianRationalPolynomialExponential (factorial_positive)
open GaussianRootAlgebra (im_scale re_scale equal equal_of_values re_zero im_zero)
open Products (fact)
open RationalArithmetic (add)
open RationalArgmin (rationalLE)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalRepresentedUpper (to_signed from_signed left right)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper radius radius_symmetric radius_congr radius_triangle radius_mono radius_diagonal upper_of_radius upper_of_order
  upper_triangle upper_mono upper_congr upper_order_right positive_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def inverseIndex (k J z p : PTm n) : PTm n := index nameF p (data k (modulus J) z)

private theorem grid_rep (i M : PTm n) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (sndT (nativeValue i M))
      (ZT.ofNat (two*total i M (two*(M*M)))) (fact (two*(M*M))) := by
  let L := two*(M*M)
  change Γ ⊢[PRAAx] RationalArithmetic.represents
    (sndT (GaussianRationalHorner.ofGaussian (scale (two*total i M L) imaginaryCode) (fact L)))
      (ZT.ofNat (two*total i M L)) (fact L)
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (ofGaussian_represents (scale (two*total i M L) imaginaryCode) (fact L) (factorial_positive L)).andE₂
  apply ZT.derive
  simp only [im_scale,imaginaryCode,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem sorted_slope (i j M L : PTm n) (hM : Γ ⊢[PRAAx] source M L)
    (hi : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] le ((two*M)*total i M L) ((two*M)*total j M L) ⋏
      le ((two*M)*total j M L) ((two*M)*total i M L+two*monus j i*fact L) := by
  have e := (eq_add_of_le hi).eqSymm
  have r : Γ ⊢[PRAAx] total (i+monus j i) M L ≐ total j M L := congrAp2 (sumF Qb) e (.eqRefl _)
  have result := GaussianArctangentSlope.finite_slope i (monus j i) M L hM (le_congr e.eqSymm (.eqRefl _) hj)
  refine .andI ?_ ?_
  · exact le_congr (.eqRefl _) (congrMul (.eqRefl (two*M)) r)
      (le_trans (le_add_left _ _) result.andE₁)
  · exact le_congr ((congrMul (.eqRefl two) (congrMul (.eqRefl M) r)).eqTrans (by ipra_ring))
      (by ipra_ring) (le_mul_mono (le_refl two) result.andE₂)

private theorem grid_slope (i j M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] le i M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] upper (sndT (nativeValue j M)) (sndT (nativeValue i M)) (two*monus j i) M := by
  let L := two*(M*M)
  let F := fact L
  let X := two*total i M L
  let Y := two*total j M L
  let D := two*monus j i
  have hF := factorial_positive (Γ := Γ) L
  have hs : Γ ⊢[PRAAx] source M L := .andI hM (le_refl _)
  have base : Γ ⊢[PRAAx] le (M*Y) (M*X+D*F) := by
    refine .orE (le_total i j) ?_ ?_
    · exact le_congr (by dsimp only [Y]; ipra_ring) (by dsimp only [X,D]; ipra_ring)
        (sorted_slope i j M L hs.wk Prf.hyp0 hj.wk).andE₂
    · exact le_trans
        (le_congr (by dsimp only [Y]; ipra_ring) (by dsimp only [X]; ipra_ring)
          (sorted_slope j i M L hs.wk Prf.hyp0 hi.wk).andE₁) (le_add_right _ _)
  apply from_signed _ _ (ZT.ofNat Y) (ZT.ofNat X) F F D M hF hF (grid_rep j M) (grid_rep i M)
  let A := M*Y
  let B := M*X+D*F
  have eq := natEq (eq_add_of_le base)
  apply zle_of_toZ (F*monus B A)
  simp only [left,right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,A,B,Q.mk_add,Q.mk_mul,map_mul,map_add] at eq ⊢
  linear_combination -𝔞 F*eq

private theorem cancel_addition (a N m C M : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] upper (add a (fraction N m)) a C M) :
    Γ ⊢[PRAAx] le (N*M) (C*m) := by
  let X := numeratorOf a
  let E := denominatorOf a
  have ha : Γ ⊢[PRAAx] RationalArithmetic.represents a X E := RationalRepresentations.represents_self a
  have hadd := RationalRepresentations.represents_add _ _ _ _ _ _ ha (fraction_represents N m hm)
  have hs := to_signed _ _ _ _ _ _ _ _ hadd ha h
  let l := left (X*ZT.ofNat m+ZT.ofNat N*ZT.ofNat E) E M
  let r := right X (E*m) E C M
  let s := PolynomialBisection.slack l r
  have eq := zle_toZ hs
  change ZT.toZ Γ l+𝔞 s = ZT.toZ Γ r at eq
  apply positive_cancel (c := E*E) (positive_product _ _ (RationalArgmin.denominator_positive a)
    (RationalArgmin.denominator_positive a))
  apply le_of_eq_add (d := s)
  apply deriveNat
  simp only [l,r,left,right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_add,Q.mk_mul,map_add,map_mul] at eq ⊢
  linear_combination -eq

private theorem mesh_error (a b E p : PTm n) (h : Γ ⊢[PRAAx] radius a b E (unit p)) :
    Γ ⊢[PRAAx] upper a b (num 4*E) (mesh p) :=
  upper_mono _ _ _ _ _ _ (unit_positive p) (upper_of_radius _ _ _ _ h)
    (le_of_eq_add (d := zero) (by unfold mesh GaussianArctangentPartialQuadrature.mesh; ipra_ring))

theorem inverse_gap_of_samples (i j m N p A B e f : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le i (mesh p)) (hj : Γ ⊢[PRAAx] le j (mesh p))
    (hla : Γ ⊢[PRAAx] radius (sndT (nativeValue i (mesh p))) A e (unit p))
    (hra : Γ ⊢[PRAAx] radius B (sndT (nativeValue j (mesh p))) f (unit p))
    (hg : Γ ⊢[PRAAx] rationalLE (add A (fraction N m)) B)
    (hp : Γ ⊢[PRAAx] le (num 2*(e+f)*m) (unit p)) :
    Γ ⊢[PRAAx] le (mesh p) ((num 4*m)*monus j i) := by
  let M := mesh p
  let a := sndT (nativeValue i M)
  let b := sndT (nativeValue j M)
  let K := fraction N m
  let D := monus j i
  let C := num 4*(e+f)
  have hM := mesh_positive (Γ := Γ) p
  have step : Γ ⊢[PRAAx] upper (add a K) (add A K) (num 4*e) M :=
    RationalUpperAddition.add_upper_order_right (mesh_error _ _ _ _ hla) (RationalArgmin.reflexive K)
  have s := RationalValueBounds.upper_triangle_same hM (upper_order_right _ _ _ _ _ step hg)
    (RationalValueBounds.upper_triangle_same hM (mesh_error _ _ _ _ hra) (grid_slope i j M hM hi hj))
  have clear : Γ ⊢[PRAAx] le M (m*(C+two*D)) :=
    le_trans (le_congr (one_mul M) (.eqRefl _) (le_mul_mono hN (le_refl M)))
      (le_congr (.eqRefl _) (by dsimp only [C,D]; ipra_ring) (cancel_addition a N m _ M hm s))
  have fine : Γ ⊢[PRAAx] le (two*m*C) M :=
    le_congr (by dsimp only [C]; ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (num 4)) hp)
  apply le_of_add_le_add_right (c := M)
  exact le_trans
    (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl two) clear))
    (le_congr (.eqRefl _) (by ipra_ring) (add_le_add_right ((num 4*m)*D) fine))

private theorem zero_ordinate (m z p : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ordinate zero m z p ≐ sndT (nativeValue zero (mesh p)) := by
  let Q := quarterNumerator (clock p)
  let F := quarterDenominator (clock p)
  have hF : Γ ⊢[PRAAx] le one F := factorial_positive _
  have c : Γ ⊢[PRAAx] equal (scale (two*zero*Q) imaginaryCode) zeroCode := by
    apply equal_of_values <;> simp only [re_scale,im_scale,re_zero,im_zero,imaginaryCode,eval_re_code,
      eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring
  have a := canonical_congr (sample_at (Γ := Γ) zero m z p) (qmul_canonical _ _)
  have zeroValue : Γ ⊢[PRAAx] ap2 nameF p (data zero m z) ≐ qzero :=
    canonical_unique _ _ _ (m*F) a GaussianRationalSyntheticDivision.qzero_canonical (positive_product _ _ hm hF)
      (represents_congr (.eqRefl _) c (.eqRefl _) (sample_represents zero m z p hm)) (zero_represents _)
  exact congrSnd (zeroValue.eqTrans (prefix_zero _ _).eqSymm)

private theorem endpoint_error (p z : PTm n) :
    Γ ⊢[PRAAx] radius (quarterOrdinate (clock p) z) (sndT (nativeValue (mesh p) (mesh p))) (num 7) (unit p) := by
  let M := mesh p
  let U := unit p
  let V := unit (clock p)
  let A := quarterOrdinate (clock p) z
  let B := quarterOrdinate p z
  let C := sndT (nativeValue M M)
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) (clock p)
  have hVU := positive_product _ _ hV hU
  have order : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have chain : Γ ⊢[PRAAx] radius A B (V+U) (V*U) :=
    imaginary_coordinate_radius (ap2 quarterF (clock p) z) (ap2 quarterF p z) (V+U) (V*U) hVU
      (point_at quarterF z (clock p) p (quarter_regular z))
  have step : Γ ⊢[PRAAx] radius A B two U :=
    radius_mono _ _ _ _ _ _ hVU chain (by ipra_le 𝔞 U*sl order)
  have endpoint : Γ ⊢[PRAAx] ap2 GaussianArctangentPartialQuadrature.nameF p
      (GaussianArctangentPartialQuadrature.data one one) ≐ nativeValue M M := by
    have e := Prf.eqCongr (Γ := Γ) (nativeValue (var 0) (var 0) : PTm 1)
      (σ := fun _ => one*M) (σ' := fun _ => M) (fun _ => one_mul M)
    refine (GaussianArctangentPartialQuadrature.sample_at p one one).eqTrans ?_
    change Γ ⊢[PRAAx] nativeValue (one*M) (one*M) ≐ nativeValue M M
    simpa only [subst_nativeValue,Syn.subst_var] using e
  have last : Γ ⊢[PRAAx] radius B C (num 5) U :=
    radius_symmetric _ _ _ _ (radius_congr (congrSnd endpoint) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (imaginary_coordinate_radius _ _ _ _ hU (GaussianArctangentPartialUnitEndpoint.unit_endpoint_distance p z)))
  exact radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (RationalValueBounds.radius_triangle_same hU step last)

theorem inverse_start (k J z p : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hJ : Γ ⊢[PRAAx] le k J)
    (hfine : Γ ⊢[PRAAx] le (num 14*modulus J) (unit p)) :
    Γ ⊢[PRAAx] le (mesh p) ((num 4*modulus J)*inverseIndex k J z p) := by
  let m := modulus J
  let M := mesh p
  let i := inverseIndex k J z p
  let T := num 4*m
  let A := ordinate zero m z p
  let B := ordinate k m z p
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hi : Γ ⊢[PRAAx] le i M := index_le nameF p (data k m z)
  have left : Γ ⊢[PRAAx] radius (sndT (nativeValue i M)) B (num 7) (unit p) :=
    forward_at nameF p (data k m z) z (interval_input k m z (odd_source k J hJ))
  have hn : Γ ⊢[PRAAx] le one (two*one) := le_of_eq_add (d := one) (by ipra_ring)
  have startFine : Γ ⊢[PRAAx] le (num 2*(zero+num 7)*m) (unit p) := le_congr (by ipra_ring) (.eqRefl _) hfine
  have startError : Γ ⊢[PRAAx] radius (sndT (nativeValue zero M)) A zero (unit p) :=
    radius_congr (.eqRefl _) (zero_ordinate m z p hm).eqSymm (.eqRefl _) (.eqRefl _)
      (radius_diagonal (sndT (nativeValue zero M)) zero (unit p))
  have start := inverse_gap_of_samples zero i m (two*one) p A B zero (num 7)
    hm hn (zero_le M) hi startError (radius_symmetric _ _ _ _ left)
    (gap_at zero k one m z p hm (le_congr (zero_add one).eqSymm (.eqRefl _) hk)) startFine
  exact le_congr (.eqRefl _) (congrMul (.eqRefl T) (monus_zero i)) start

theorem inverse_margins (k l J z p : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkl : Γ ⊢[PRAAx] le (k+one) l) (hl : Γ ⊢[PRAAx] le l J)
    (hfine : Γ ⊢[PRAAx] le (num 28*modulus J) (unit p)) :
    Γ ⊢[PRAAx] marginSource (mesh p) (inverseIndex k J z p) (inverseIndex l J z p) (num 4*modulus J) := by
  let m := modulus J
  let M := mesh p
  let i := inverseIndex k J z p
  let j := inverseIndex l J z p
  let T := num 4*m
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hM := mesh_positive (Γ := Γ) p
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring)) hm
  have hi : Γ ⊢[PRAAx] le i M := index_le nameF p (data k m z)
  have hj : Γ ⊢[PRAAx] le j M := index_le nameF p (data l m z)
  have hkJ := le_trans (le_add_right k one) (le_trans hkl hl)
  have hks := odd_source k J hkJ
  have hls := odd_source l J hl
  have left := forward_at nameF p (data k m z) z (interval_input k m z hks)
  have right := forward_at nameF p (data l m z) z (interval_input l m z hls)
  have hn : Γ ⊢[PRAAx] le one (two*one) := le_of_eq_add (d := one) (by ipra_ring)
  have fine : Γ ⊢[PRAAx] le (num 2*(num 7+num 7)*m) (unit p) :=
    le_congr (by ipra_ring) (.eqRefl _) hfine
  have start := inverse_start k J z p hk hkJ (le_trans (by ipra_le 14*𝔞 m) hfine)
  have middle : Γ ⊢[PRAAx] le M (T*monus j i) :=
    inverse_gap_of_samples i j m (two*one) p (ordinate k m z p) (ordinate l m z p) (num 7) (num 7)
      hm hn hi hj left (radius_symmetric _ _ _ _ right) (gap_at k l one m z p hm hkl) fine
  have last : Γ ⊢[PRAAx] le M (T*monus M j) :=
    inverse_gap_of_samples j M m one p (ordinate l m z p) (quarterOrdinate (clock p) z) (num 7) (num 7)
      hm (le_refl one) hj (le_refl M) right (endpoint_error p z) (top_margin_at l J z p hl) fine
  have order : Γ ⊢[PRAAx] le i j := by
    refine .orE (le_total i j) Prf.hyp0 ?_
    apply not_succ_le_self zero
    exact le_trans hM.wk (le_congr (.eqRefl _) ((congrMul (.eqRefl T) Prf.hyp0).eqTrans (by ipra_ring)) middle.wk)
  exact .andI (.andI hM hT) (.andI (.andI order hj)
    (.andI start (.andI middle last)))

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionInverseMargins
