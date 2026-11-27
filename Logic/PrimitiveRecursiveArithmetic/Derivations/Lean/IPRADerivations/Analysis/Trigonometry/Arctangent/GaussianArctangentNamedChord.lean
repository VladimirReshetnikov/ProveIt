import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentChordComparison
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialTrig
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentPartialUnitEndpoint
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# Chord comparison on the original arctangent observations

The rational Cayley sine scales the unit-endpoint quadrature. A matched
grid gives an exact finite comparison; regularity and slack removal
then transport it to independent observations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedChord

open_ipra
open ComplexLogarithmRemainder (code scale im normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (denominator denominator_positive imaginaryCode)
open GaussianArctangentCayleyTrig (sineCode sinePoint)
open GaussianArctangentExponentialPrefix (source total prefixValue)
open GaussianArctangentPartialQuadrature (observation clearing prefix_as_sum rowBody)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaRealValues (scalar_radius_of_embedded_distance)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_represents represents_rescale positive_product
  scalar_congr qzero qmul qmul_represents)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (comparison_of_cleared bounded bounded_of_cleared bounded_difference_iff distanceBounded)
open GaussianRootAlgebra (im_scale im_mul re_scale)
open RationalValueBounds (upper upper_congr upper_triangle upper_mono upper_of_order upper_of_radius)
open GaussianRationalPolynomialExponential (factorial_positive)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem imaginary_prefix_represents (j M L : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (sndT (prefixValue j M L)) (ZT.ofNat (two*total j M L)) (fact L) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ (factorial_positive L)).andE₂
  apply ZT.derive
  simp only [im_scale,imaginaryCode,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem imaginary_scaled_prefix_represents (A B j M L : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (sndT (qmul (sinePoint B A) (prefixValue j M L)))
      (ZT.ofNat ((two*B*A)*(two*total j M L))) (denominator B A*fact L) := by
  have hd := denominator_positive B A hB
  have hF := factorial_positive (Γ := Γ) L
  have h := qmul_represents (sinePoint B A) (prefixValue j M L) (sineCode B A)
    (scale (two*total j M L) imaginaryCode) (denominator B A) (fact L) hd hF
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hF)
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) h.andE₂
  apply ZT.derive
  simp only [im_mul,im_scale,re_scale,sineCode,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem full_prefix_readback (J L : PTm n) (h : Γ ⊢[PRAAx] source J L) :
    Γ ⊢[PRAAx] prefixValue J J L ≐ observation one one J := by
  have hJ : Γ ⊢[PRAAx] le one (one*J) :=
    le_congr (.eqRefl _) (one_mul J).eqSymm h.andE₁
  have e : Γ ⊢[PRAAx] observation one one J ≐ GaussianRationalFiniteSum.sum rowBody (one*J) (one*J) :=
    prefix_as_sum _ _ _ (.andI hJ (le_refl _)) (le_refl _)
  have read := GaussianRationalFiniteSum.sum_index_congr rowBody (one_mul (Γ := Γ) J) (one_mul J)
  exact (prefix_as_sum J J L h (le_refl J)).eqTrans (read.eqSymm.eqTrans e.eqSymm)

theorem observation_chord_order (A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hAB : Γ ⊢[PRAAx] le A B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (sndT (observation A B N))
      (sndT (qmul (sinePoint B A) (observation one one (A*N)))) := by
  let J := A*N
  let M := B*N
  let L := clearing M
  let d := denominator B A
  have hB := le_trans hA hAB
  have hJ := le_mul_mono hAB (le_refl N)
  have hl : Γ ⊢[PRAAx] le (two*(J*J)) L :=
    le_mul_mono (le_refl two) (le_mul_mono hJ hJ)
  have hFp := factorial_positive (Γ := Γ) L
  have hd := denominator_positive B A hB
  have cmp := GaussianArctangentChordComparison.matched_prefix_bound J J M L hJ (le_refl _) (le_refl _)
  have reduced : Γ ⊢[PRAAx] le (d*total J M L) ((two*B*A)*total J J L) :=
    RationalValueBounds.positive_cancel (positive_product N N hN hN)
      (le_congr (by dsimp only [d,denominator,J,M]; ipra_ring) (by dsimp only [J,M]; ipra_ring) cmp)
  have core := comparison_of_cleared (sndT (prefixValue J M L)) (sndT (qmul (sinePoint B A) (prefixValue J J L)))
    (two*total J M L) ((two*B*A)*(two*total J J L)) (fact L) (d*fact L) hFp (positive_product _ _ hd hFp)
    (imaginary_prefix_represents _ _ _) (imaginary_scaled_prefix_represents A B _ _ _ hB)
    (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl (two*fact L)) reduced))
  have e := full_prefix_readback J L (.andI (positive_product _ _ hA hN) hl)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (congrSnd (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) e)) core

private theorem sine_point_zero (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] sinePoint B zero ≐ qzero := by
  let D := denominator B zero
  have hD := denominator_positive B zero hB
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (sineCode B zero) ComplexLogarithmRemainder.zeroCode := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [sineCode,ComplexLogarithmRemainder.zeroCode,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact GaussianRationalHorner.canonical_unique _ _ _ D
    (GaussianRationalHorner.ofGaussian_canonical _ _ hD)
    GaussianRationalSyntheticDivision.qzero_canonical hD
    (GaussianRationalHorner.represents_congr (.eqRefl _) eq (.eqRefl _) (ofGaussian_represents _ _ hD))
    (GaussianRationalHorner.zero_represents D)

theorem observation_zero (B N : PTm n) : Γ ⊢[PRAAx] observation zero B N ≐ qzero := by
  have decomp : Γ ⊢[PRAAx] observation zero B N ≐ prefixValue zero (B*N) (clearing (B*N)) := by
    simpa [observation] using Prf.eqCongr (prefixValue (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![zero*N,B*N,clearing (B*N)]) (σ' := ![zero,B*N,clearing (B*N)])
      (fun i => by fin_cases i; exact zero_mul _; exact .eqRefl _; exact .eqRefl _)
  exact decomp.eqTrans (GaussianArctangentExponentialPrefix.prefix_zero _ _)

theorem zero_chord_order (B N q : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (sndT (observation zero B N)) (sndT (qmul (sinePoint B zero) q)) := by
  have e := (GaussianRationalSyntheticDivision.qmul_congr (sine_point_zero B hB) (.eqRefl q)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_left q)
  exact RationalArgmin.rationalLE_congr (congrSnd (observation_zero B N)).eqSymm (congrSnd e).eqSymm
    (RationalArgmin.reflexive _)

theorem sine_point_bound (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] bounded (sinePoint B A) one one := by
  let d := denominator B A
  let w := two*B*A
  have hD := denominator_positive B A hB
  have hwd : Γ ⊢[PRAAx] le w d := by
    refine le_of_eq_add (d := monus B A*monus B A) ?_
    have e := natEq (eq_add_of_le hAB)
    apply deriveNat
    unfold d w denominator
    simp only [Q.mk_add,map_add] at e
    ipra_simps
    rw [e]
    ring
  have ns : Γ ⊢[PRAAx] normSq (sineCode B A) ≐ w*w := by
    apply deriveNat
    rw [normSq_eval]
    simp only [sineCode,eval_re_code,eval_im_code,ZT.toZ_ofNat,w]
    ipra_simps
    ring
  apply bounded_of_cleared _ _ d one one hD (le_refl _) (ofGaussian_represents _ _ hD)
  exact le_congr (ns.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring) (le_mul_mono hwd hwd)

private theorem imaginary_projection_norm (a b : PTm n) : Γ ⊢[PRAAx]
    le (normSq (GaussianRootAlgebra.sub (RationalGaussianEmbedding.native (im a)) (RationalGaussianEmbedding.native (im b))))
      (normSq (GaussianRootAlgebra.sub a b)) := by
  refine le_of_eq_add (d := normSq (RationalGaussianEmbedding.native
    (ComplexLogarithmRemainder.re (GaussianRootAlgebra.sub a b)))) ?_
  apply deriveNat
  ipra_simps
  simp only [normSq_eval,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    RationalGaussianEmbedding.native,eval_re_code,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem imaginary_coordinate_radius (a b A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx] RationalValueBounds.radius (sndT a) (sndT b) A B := by
  let C := rawDen a*rawDen b
  let u := scale (rawDen b) (rawGaussian a)
  let v := scale (rawDen a) (rawGaussian b)
  have hC := positive_product _ _ (raw_den_positive (Γ := Γ) a) (raw_den_positive b)
  have hu := represents_rescale a (rawGaussian a) (rawDen a) (rawDen b) (raw_represents (Γ := Γ) a)
  have hv := GaussianRationalSyntheticDivision.rescale_to b (rawGaussian b) (rawDen b) (rawDen a) C
    (raw_represents (Γ := Γ) b) (mul_comm _ _)
  have ca := (bounded_difference_iff a b u v C A B hC hB hu hv).iffMp h
  apply scalar_radius_of_embedded_distance _ _ _ _ hB
  apply (bounded_difference_iff _ _ _ _ C A B hC hB
    (RationalGaussianEmbedding.embed_from_representation _ _ _ hu.andE₂)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ hv.andE₂)).iffMpr
  exact le_trans (le_mul_mono (le_refl _) (imaginary_projection_norm u v)) ca

private theorem sine_scale_distance (A B x y C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded x y C D) :
    Γ ⊢[PRAAx] distanceBounded (qmul (sinePoint B A) x) (qmul (sinePoint B A) y) C D :=
  distance_congr (.eqRefl _) (.eqRefl _) (one_mul _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance _ _ _ one _ _ hD (sine_point_bound A B hB hAB) h)

open GaussianArctangentPartialQuadrature (nameF data mesh sample_at mesh_positive finite_refinement name_regular)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianNameEquivalence (point_at cross_at)

private theorem named_chord_slack (p q A B z t : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hAB : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx]
    upperSlack (sndT (ap2 nameF p (data A B))) (sndT (qmul (sinePoint B A) (ap2 quarterF q z)))
      (unit p+unit q) (unit p*unit q) (num 3) t := by
  let N := mesh t
  let J := A*N
  let c := sinePoint B A
  let f := ap2 nameF p (data A B)
  let g := qmul c (ap2 quarterF q z)
  let a := observation A B N
  let b := qmul c (observation one one J)
  let v := qmul c (observation one one N)
  let U := unit p*unit t
  let V := unit t*unit q
  have hB := le_trans hA hAB
  have hN := mesh_positive (Γ := Γ) t
  have hU : Γ ⊢[PRAAx] le one U := positive_product _ _ (unit_positive p) (unit_positive t)
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (unit_positive t) (unit_positive q)
  have first : Γ ⊢[PRAAx] distanceBounded f a (unit p+unit t) U :=
    distance_congr (.eqRefl _) (sample_at t A B) (.eqRefl _) (.eqRefl _)
      (point_at nameF (data A B) p t (name_regular A B hB hAB))
  have middle : Γ ⊢[PRAAx] upper (sndT a) (sndT b) zero one :=
    upper_of_order _ _ _ _ (observation_chord_order A B N hA hAB hN)
  have refine_unit := finite_refinement one one N A (le_refl one) (le_refl one) hN hA
  have second : Γ ⊢[PRAAx] distanceBounded b v one (unit t) :=
    distance_radius_mono _ _ _ _ _ _ hN (unit_positive t)
      (le_of_eq_add (d := zero) (by dsimp only [N,mesh]; ipra_ring))
      (sine_scale_distance A B _ _ _ _ hB hAB hN refine_unit)
  have third : Γ ⊢[PRAAx] distanceBounded v g (unit t+unit q) V :=
    distance_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (sample_at t one one)) (.eqRefl _)
      (.eqRefl _) (.eqRefl _)
      (sine_scale_distance A B _ _ _ _ hB hAB hV
        (cross_at nameF quarterF (data one one) z t q (GaussianArctangentPartialUnitEndpoint.unit_endpoint_cross z)))
  have joined := upper_triangle _ _ _ _ _ _ _
    (upper_triangle _ _ _ _ _ _ _
      (upper_triangle _ _ _ _ _ _ _ (upper_of_radius _ _ _ _ (imaginary_coordinate_radius _ _ _ _ hU first)) middle)
      (upper_of_radius _ _ _ _ (imaginary_coordinate_radius _ _ _ _ (unit_positive t) second)))
    (upper_of_radius _ _ _ _ (imaginary_coordinate_radius _ _ _ _ hV third))
  apply upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hU (le_refl one)) (unit_positive t)) hV) joined
  exact le_of_eq_add (d := zero) (by dsimp only [U,V]; ipra_ring)

theorem original_chord_at (p q A B z : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] upper (sndT (ap2 nameF p (data A B))) (sndT (qmul (sinePoint B A) (ap2 quarterF q z)))
      (unit p+unit q) (unit p*unit q) := by
  refine .orE (zero_or_succ A) ?_ ?_
  · let Δ := (A ≐ zero)::Γ
    have hA0 : Δ ⊢[PRAAx] A ≐ zero := Prf.hyp0
    have hx := congrAp2 nameF (.eqRefl p) (congrPairT hA0 (.eqRefl B))
    have hs : Δ ⊢[PRAAx] sinePoint B A ≐ sinePoint B zero := by
      simpa only [GaussianArctangentCayleyTrig.subst_sinePoint,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
        Prf.eqCongr (sinePoint (var 0) (var 1) : PTm 2)
          (σ := ![B,A]) (σ' := ![B,zero]) (fun i => by fin_cases i; exact .eqRefl _; exact hA0)
    have hy := GaussianRationalSyntheticDivision.qmul_congr hs (.eqRefl (ap2 quarterF q z))
    have raw := zero_chord_order (Γ := Δ) B (mesh p) (ap2 quarterF q z) hB.wk
    have ord := RationalArgmin.rationalLE_congr (congrSnd (sample_at p zero B)).eqSymm (.eqRefl _) raw
    exact upper_congr (congrSnd hx).eqSymm (congrSnd hy).eqSymm (.eqRefl _) (.eqRefl _) (upper_of_order _ _ _ _ ord)
  · have hA : ((A ≐ succ (pred A)) :: Γ) ⊢[PRAAx] le one A :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact remove_upper_slack _ _ _ _ (num 3) (named_chord_slack p q A B z _ hA hAB.wk)

theorem actual_original_arctangent_sine_chord_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 3) ⟶ le (var 2) (var 3) ⟶
        upper (sndT (ap2 nameF (var 0) (data (var 2) (var 3))))
          (sndT (qmul (sinePoint (var 3) (var 2)) (ap2 quarterF (var 1) (var 4))))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (.impI (original_chord_at _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedChord
