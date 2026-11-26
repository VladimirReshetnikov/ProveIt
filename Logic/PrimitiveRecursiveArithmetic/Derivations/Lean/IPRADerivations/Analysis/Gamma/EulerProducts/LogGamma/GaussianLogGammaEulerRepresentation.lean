import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerCofinal

/-!
# Rational presentation independence for the Euler logarithm

Equal canonical input codes give the same finite Euler logarithm at each
positive cutoff. Read both cofinal names against that common finite value.
The sign bits may differ when both imaginary numerators vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRepresentation

open_ipra
open ComplexLogarithmRemainder (re im eval_re_code eval_im_code)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerHead (argument rowData productF productData)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans subst_crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (ofGaussian_represents positive_product scalar_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open RationalArithmetic (select_zero select_one)
open RationalNormalForm (denominator_positive positive_integer_cancel)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "F" => GaussianLogGammaEulerNormalizedHead.nameF
local notation "headData" => GaussianLogGammaEulerNormalizedHead.data
local notation "sampleF" => GaussianLogGammaEulerCofinal.nameF
local notation "sampleData" => GaussianLogGammaEulerCofinal.canonicalData
local notation "residualF" => GaussianLogGammaEulerFactorSum.residualF
local notation "residualBody" => GaussianLogGammaEulerFactorSum.residualBody

def sameValue (A B D neg a b d sign : PTm n) : Fm PTm n :=
  (A*d ≐ a*D) ⋏ ((B*d ≐ b*D) ⋏ ((neg ≐ sign) ⋎ ((B ≐ zero) ⋏ (b ≐ zero))))

ipra_subst sameValue

ipra_subst argument [ZT.subst, ZT.ofNat]

private theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A D neg : PTm n) :
    (source A D neg).subst σ = source (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ neg) := by
  simp [source]

private theorem cleared_coordinate (q D d : PTm n) (v w : ZT n)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents q v D)
    (k : Γ ⊢[PRAAx] RationalArithmetic.represents q w d) :
    Γ ⊢[PRAAx] ZT.eq (v*ZT.ofNat d) (w*ZT.ofNat D) := by
  have x := ZT.toZ_eq h
  have y := ZT.toZ_eq k
  apply positive_integer_cancel (denominatorOf q) _ _ (denominator_positive q)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at x y ⊢
  linear_combination 𝔞(d)*x-𝔞(D)*y

private theorem imag_zero_sign (B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero) :
    ZT.toZ Γ (signedImag B neg) = 𝔞(B) := by
  have u := natEq (select_zero neg B zero h)
  have v := natEq (select_zero neg zero B h)
  simp only [signedImag,ZT.toZ]
  rw [u,v]
  ipra_simps
  ring

private theorem imag_one_sign (B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ one) :
    ZT.toZ Γ (signedImag B neg) = -𝔞(B) := by
  have u := natEq (select_one neg B zero h)
  have v := natEq (select_one neg zero B h)
  simp only [signedImag,ZT.toZ]
  rw [u,v]
  ipra_simps
  ring

private theorem opposite_imaginaries (B b D d : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hd : Γ ⊢[PRAAx] le one d) (e : Γ ⊢[PRAAx] B*d+b*D ≐ zero) :
    Γ ⊢[PRAAx] (B*d ≐ b*D) ⋏ ((B ≐ zero) ⋏ (b ≐ zero)) := by
  have zB : Γ ⊢[PRAAx] B*d ≐ zero :=
    le_antisymm (le_congr (.eqRefl _) e (le_add_right (B*d) (b*D))) (zero_le _)
  have zb : Γ ⊢[PRAAx] b*D ≐ zero :=
    le_antisymm (le_congr (.eqRefl _) e (le_add_left (b*D) (B*d))) (zero_le _)
  have eB : Γ ⊢[PRAAx] B ≐ zero := le_antisymm
    (le_congr (one_mul B) ((mul_comm d B).eqTrans zB) (mul_le_mul_right B hd)) (zero_le _)
  have eb : Γ ⊢[PRAAx] b ≐ zero := le_antisymm
    (le_congr (one_mul b) ((mul_comm D b).eqTrans zb) (mul_le_mul_right b hD)) (zero_le _)
  exact .andI (zB.eqTrans zb.eqSymm) (.andI eB eb)

private theorem signed_coordinate (B b D d neg sign : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hd : Γ ⊢[PRAAx] le one d)
    (hn : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one))
    (hs : Γ ⊢[PRAAx] (sign ≐ zero) ⋎ (sign ≐ one))
    (e : Γ ⊢[PRAAx] ZT.eq (signedImag B neg*ZT.ofNat d) (signedImag b sign*ZT.ofNat D)) :
    Γ ⊢[PRAAx] (B*d ≐ b*D) ⋏ ((neg ≐ sign) ⋎ ((B ≐ zero) ⋏ (b ≐ zero))) := by
  refine hn.orE ?_ ?_
  · refine hs.wk.orE ?_ ?_
    · refine .andI ?_ (.orI₁ (Prf.hyp1.eqTrans Prf.hyp0.eqSymm))
      let Δ := (sign ≐ zero) :: (neg ≐ zero) :: Γ
      have v := ZT.toZ_eq (Γ := Δ) e.wk.wk
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,imag_zero_sign (Γ := Δ) B neg Prf.hyp1,
        imag_zero_sign (Γ := Δ) b sign Prf.hyp0] at v
      apply deriveNat
      ipra_simps
      exact v
    · let Δ := (sign ≐ one) :: (neg ≐ zero) :: Γ
      have v := ZT.toZ_eq (Γ := Δ) e.wk.wk
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,imag_zero_sign (Γ := Δ) B neg Prf.hyp1,
        imag_one_sign (Γ := Δ) b sign Prf.hyp0] at v
      have z : Δ ⊢[PRAAx] B*d+b*D ≐ zero := by
        apply deriveNat
        ipra_simps
        linear_combination v
      have h := opposite_imaginaries B b D d hD.wk.wk hd.wk.wk z
      exact .andI h.andE₁ (.orI₂ h.andE₂)
  · refine hs.wk.orE ?_ ?_
    · let Δ := (sign ≐ zero) :: (neg ≐ one) :: Γ
      have v := ZT.toZ_eq (Γ := Δ) e.wk.wk
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,imag_one_sign (Γ := Δ) B neg Prf.hyp1,
        imag_zero_sign (Γ := Δ) b sign Prf.hyp0] at v
      have z : Δ ⊢[PRAAx] B*d+b*D ≐ zero := by
        apply deriveNat
        ipra_simps
        linear_combination -v
      have h := opposite_imaginaries B b D d hD.wk.wk hd.wk.wk z
      exact .andI h.andE₁ (.orI₂ h.andE₂)
    · refine .andI ?_ (.orI₁ (Prf.hyp1.eqTrans Prf.hyp0.eqSymm))
      let Δ := (sign ≐ one) :: (neg ≐ one) :: Γ
      have v := ZT.toZ_eq (Γ := Δ) e.wk.wk
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,imag_one_sign (Γ := Δ) B neg Prf.hyp1,
        imag_one_sign (Γ := Δ) b sign Prf.hyp0] at v
      apply deriveNat
      ipra_simps
      linear_combination -v

theorem coordinates (A B D neg a b d sign : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ argument a b d sign) :
    Γ ⊢[PRAAx] sameValue A B D neg a b d sign := by
  let x := argument A B D neg
  let u := native A B neg
  let v := native a b sign
  have hx := ofGaussian_represents u D h.andE₂
  have hy := ofGaussian_represents v d k.andE₂
  have r := cleared_coordinate (fstT x) D d (re u) (re v) hx.andE₁
    (scalar_congr (congrFst e.eqSymm) (.eqRefl _) (.eqRefl _) hy.andE₁)
  have s := cleared_coordinate (sndT x) D d (im u) (im v) hx.andE₂
    (scalar_congr (congrSnd e.eqSymm) (.eqRefl _) (.eqRefl _) hy.andE₂)
  have realEq : Γ ⊢[PRAAx] A*d ≐ a*D := by
    have equality := ZT.toZ_eq r
    simp only [u,v,GaussianLogGammaEulerResidualDomain.native,ZT.toZ_mul,eval_re_code,ZT.toZ_ofNat] at equality
    apply deriveNat
    ipra_simps
    exact equality
  have imagEq : Γ ⊢[PRAAx] ZT.eq (signedImag B neg*ZT.ofNat d) (signedImag b sign*ZT.ofNat D) := by
    have e := ZT.toZ_eq s
    apply ZT.derive
    simpa only [u,v,GaussianLogGammaEulerResidualDomain.native,ZT.toZ_mul,eval_im_code] using e
  exact .andI realEq (signed_coordinate B b D d neg sign h.andE₂ k.andE₂ h.andE₁.andE₂ k.andE₁.andE₂ imagEq)

private theorem move_inputs (f g : PR 2) {x x' y y' : PTm n}
    (e : Γ ⊢[PRAAx] x ≐ x') (e' : Γ ⊢[PRAAx] y ≐ y') (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent f g x' y' := by
  have h' : Γ ⊢[PRAAx] (crossEquivalent f g (var 0) (var 1) : Fm PTm 2).subst ![x,y] := by
    simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h
  have proof := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (crossEquivalent f g (var 0) (var 1) : Fm PTm 2)
    ![x,y] ![x',y'] (fun i => by fin_cases i; exact e; exact e') h'
  simpa only [subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using proof

private theorem log_data_congr {A B D neg a b d sign : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ a) (hB : Γ ⊢[PRAAx] B ≐ b) (hD : Γ ⊢[PRAAx] D ≐ d) (hS : Γ ⊢[PRAAx] neg ≐ sign) :
    Γ ⊢[PRAAx] P A B D neg ≐ P a b d sign := by
  simpa only [GaussianRightHalfPlaneLogarithm.subst_data,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (P (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![A,B,D,neg]) (σ' := ![a,b,d,sign])
      (fun i => by fin_cases i; exact hA; exact hB; exact hD; exact hS)

theorem logarithm_cross (A B D neg a b d sign : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign)
    (e : Γ ⊢[PRAAx] sameValue A B D neg a b d sign) :
    Γ ⊢[PRAAx] crossEquivalent G G (P A B D neg) (P a b d sign) := by
  refine e.andE₂.andE₂.orE ?_ ?_
  · let Δ := (neg ≐ sign) :: Γ
    let t := P (d*A) (d*B) (d*D) neg
    let u := P (D*a) (D*b) (D*d) sign
    have eqA : Δ ⊢[PRAAx] d*A ≐ D*a := (mul_comm d A).eqTrans (e.andE₁.wk.eqTrans (mul_comm a D))
    have eqB : Δ ⊢[PRAAx] d*B ≐ D*b := (mul_comm d B).eqTrans (e.andE₂.andE₁.wk.eqTrans (mul_comm b D))
    have middle : Δ ⊢[PRAAx] t ≐ u := log_data_congr eqA eqB (mul_comm d D) Prf.hyp0
    have left := GaussianRightHalfPlaneLogarithmRescale.rescale (Γ := Δ) A B D neg d h.wk k.andE₂.wk
    have right := GaussianRightHalfPlaneLogarithmRescale.rescale (Γ := Δ) a b d sign D k.wk h.andE₂.wk
    exact cross_trans G G G _ u _ (move_inputs G G (.eqRefl _) middle (cross_symm G G t _ left)) right
  · let Δ := ((B ≐ zero) ⋏ (b ≐ zero)) :: Γ
    have zeros : Δ ⊢[PRAAx] (B ≐ zero) ⋏ (b ≐ zero) := Prf.hyp0
    have left := GaussianRightHalfPlaneLogarithm.positive_axis (Γ := Δ) A D neg h.wk
    have right := GaussianRightHalfPlaneLogarithm.positive_axis (Γ := Δ) a d sign k.wk
    have middle := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper (Γ := Δ) A D a d
      (.andI h.andE₁.andE₁.wk h.andE₂.wk) (.andI k.andE₁.andE₁.wk k.andE₂.wk)
      (e.andE₁.wk.eqTrans (mul_comm a D))
    have aligned := cross_trans G logF G (P A zero D neg) (L a d) (P a zero d sign)
      (cross_trans G logF logF _ _ _ left middle) (cross_symm G logF _ _ right)
    exact move_inputs G G (log_data_congr (.eqRefl _) zeros.andE₁.eqSymm (.eqRefl _) (.eqRefl _))
      (log_data_congr (.eqRefl _) zeros.andE₂.eqSymm (.eqRefl _) (.eqRefl _)) aligned

theorem logarithm_proper (A B D neg a b d sign : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ argument a b d sign) :
    Γ ⊢[PRAAx] crossEquivalent G G (P A B D neg) (P a b d sign) :=
  logarithm_cross A B D neg a b d sign h k (coordinates A B D neg a b d sign h k e)

private theorem shifted_coordinates (A B D neg a b d sign j : PTm n)
    (e : Γ ⊢[PRAAx] sameValue A B D neg a b d sign) :
    Γ ⊢[PRAAx] sameValue (A+j*D) B (D*j) neg (a+j*d) b (d*j) sign := by
  refine .andI ?_ (.andI ?_ e.andE₂.andE₂)
  · have eq := natEq e.andE₁
    apply deriveNat
    ipra_simps
    linear_combination 𝔞(j)*eq
  · exact (mul_assoc B d j).eqSymm.eqTrans ((congrMul e.andE₂.andE₁ (.eqRefl _)).eqTrans (mul_assoc b D j))

private theorem shifted_source (A D neg j : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] source (A+j*D) (D*j) neg :=
  .andI (.andI (le_trans h.andE₁.andE₁ (le_add_right _ _)) h.andE₁.andE₂)
    (positive_product D j h.andE₂ hj)

theorem residual_rows_cross (A B D neg a b d sign N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign)
    (e : Γ ⊢[PRAAx] sameValue A B D neg a b d sign) :
    Γ ⊢[PRAAx] equalRows G G residualBody residualBody N (rowData A B D neg) (rowData a b d sign) := by
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  let j : PTm (n+1) := succ (var 0)
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using h.shift.wk
  have ks : Δ ⊢[PRAAx] source (sh a) (sh d) (sh sign) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using k.shift.wk
  have es : Δ ⊢[PRAAx] sameValue (sh A) (sh B) (sh D) (sh neg) (sh a) (sh b) (sh d) (sh sign) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_sameValue] using e.shift.wk
  have hj : Δ ⊢[PRAAx] le one j := le_of_eq_add (d := var 0) (by dsimp only [j]; ipra_ring)
  have agree := logarithm_cross (sh A+j*sh D) (sh B) (sh D*j) (sh neg) (sh a+j*sh d) (sh b) (sh d*j) (sh sign)
    (shifted_source _ _ _ _ hs hj) (shifted_source _ _ _ _ ks hj) (shifted_coordinates _ _ _ _ _ _ _ _ j es)
  simpa only [Δ,Syn.shift,sh,GaussianLogGammaEulerHead.subst_rowData] using move_inputs G G
    (GaussianLogGammaEulerFactorSum.residual_at (var 0) (sh A) (sh B) (sh D) (sh neg)).eqSymm
    (GaussianLogGammaEulerFactorSum.residual_at (var 0) (sh a) (sh b) (sh d) (sh sign)).eqSymm agree

theorem finite_head_cross (A B D neg a b d sign N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign) (hN : Γ ⊢[PRAAx] le one N)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ argument a b d sign) :
    Γ ⊢[PRAAx] crossEquivalent F F (headData A B D neg N) (headData a b d sign N) := by
  let z := argument A B D neg
  let w := argument a b d sign
  let m := L N one
  let x := rowData A B D neg
  let y := rowData a b d sign
  let U := GaussianNamedFiniteSumFamily.data N x
  let V := GaussianNamedFiniteSumFamily.data N y
  let denF := GaussianLogGammaEulerNormalizedHead.denominatorF
  have eq := coordinates A B D neg a b d sign h k e
  have base := logarithm_cross A B D neg a b d sign h k eq
  have rows := residual_rows_cross A B D neg a b d sign N h k eq
  have tails := GaussianNamedFiniteSumFamilyCongruence.family_sum_cross G G residualBody residualBody N x y rows
  have hx := GaussianNamedFiniteSumFamily.regular G residualBody N x (GaussianLogGammaEulerFactorSum.residual_rows A B D neg N h)
  have hy := GaussianNamedFiniteSumFamily.regular G residualBody N y (GaussianLogGammaEulerFactorSum.residual_rows a b d sign N k)
  have hm := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have factors := multiply_cross constantF constantF logF logF z w m m
    (constant_regular z) (constant_regular w) hm hm
    (move_inputs constantF constantF (.eqRefl _) e (cross_refl constantF z (constant_regular z)))
    (cross_refl logF m hm)
  have denom := add_cross G G residualF residualF (P A B D neg) (P a b d sign) U V
    (GaussianRightHalfPlaneLogarithm.regular A B D neg h) (GaussianRightHalfPlaneLogarithm.regular a b d sign k)
    hx hy base tails
  exact difference_proper productF productF denF denF _ _ _ _
    (GaussianLogGammaEulerNormalizedHead.product_regular A B D neg N hN)
    (GaussianLogGammaEulerNormalizedHead.product_regular a b d sign N hN)
    (GaussianLogGammaEulerNormalizedHead.denominator_regular A B D neg N h)
    (GaussianLogGammaEulerNormalizedHead.denominator_regular a b d sign N k) factors denom

theorem original_finite_head_cross (A B D neg a b d sign N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign) (hN : Γ ⊢[PRAAx] le one N)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ argument a b d sign) :
    Γ ⊢[PRAAx] crossEquivalent GaussianLogGammaEulerHead.nameF GaussianLogGammaEulerHead.nameF
      (GaussianLogGammaEulerHead.data A B D neg N) (GaussianLogGammaEulerHead.data a b d sign N) := by
  have left := GaussianLogGammaEulerNormalizedHead.equivalent A B D neg N h hN
  have right := GaussianLogGammaEulerNormalizedHead.equivalent a b d sign N k hN
  have middle := finite_head_cross A B D neg a b d sign N h k hN e
  exact cross_trans _ F _ _ _ _ left
    (cross_trans F F _ _ _ _ middle (cross_symm _ F _ _ right))

private theorem cofinal_diagonal (p A B D neg a b d sign : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ argument a b d sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 sampleF p (sampleData A B D neg)) (ap2 sampleF p (sampleData a b d sign)) (num 6) (unit p) := by
  let R := radius A B
  let S := radius a b
  let K := GaussianLogGammaEulerCofinal.cutoff R p
  let M := GaussianLogGammaEulerCofinal.cutoff S p
  let N := K+M
  let u := unit p
  let x := GaussianLogGammaEulerCofinal.observed p A B D neg R
  let y := GaussianLogGammaEulerCofinal.observed p a b d sign S
  let z := ap2 F p (headData A B D neg N)
  let w := ap2 F p (headData a b d sign N)
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product (Γ := Γ) u u hu hu
  have hN := le_trans (GaussianLogGammaEulerCofinal.cutoff_positive (Γ := Γ) R p) (le_add_right K M)
  have left := GaussianLogGammaEulerCofinal.late_cutoff_distance p p A B D neg R N
    (GaussianLogGammaEulerResidualRadius.source_of_right_half_plane A B D neg h) (le_add_right K M)
  have right := GaussianLogGammaEulerCofinal.late_cutoff_distance p p a b d sign S N
    (GaussianLogGammaEulerResidualRadius.source_of_right_half_plane a b d sign k) (le_add_left M K)
  have middle := cross_at F F (headData A B D neg N) (headData a b d sign N) p p
    (finite_head_cross A B D neg a b d sign N h k hN e)
  have pair := distance_triangle_same x z w (u+u) (u+u) (u*u) hD left middle
  have all := distance_triangle_same x w y _ (u+u) (u*u) hD pair (distance_symmetric _ _ _ _ hD right)
  have small := distance_radius_mono x y _ _ (num 6) u hD hu
    (le_of_eq_add (d := zero) (by dsimp only [u]; ipra_ring)) all
  exact distance_congr (GaussianLogGammaEulerCofinal.sample_at p A B D neg R).eqSymm
    (GaussianLogGammaEulerCofinal.sample_at p a b d sign S).eqSymm (.eqRefl _) (.eqRefl _) small

theorem canonical_cross (A B D neg a b d sign : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a d sign)
    (e : Γ ⊢[PRAAx] argument A B D neg ≐ argument a b d sign) :
    Γ ⊢[PRAAx] crossEquivalent sampleF sampleF (sampleData A B D neg) (sampleData a b d sign) := by
  refine equivalent_of_envelope _ _ _ _ (num 6)
    (GaussianLogGammaEulerCofinal.canonical_regular _ _ _ _ h)
    (GaussianLogGammaEulerCofinal.canonical_regular _ _ _ _ k) (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using h.shift
  have ks : Δ ⊢[PRAAx] source (sh a) (sh d) (sh sign) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using k.shift
  have es : Δ ⊢[PRAAx] argument (sh A) (sh B) (sh D) (sh neg) ≐ argument (sh a) (sh b) (sh d) (sh sign) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,Fm.subst_eq,subst_argument] using e.shift
  simpa only [Syn.shift,sh,GaussianLogGammaEulerCofinal.subst_canonicalData,PTm.subst_num] using
    cofinal_diagonal (var 0) (sh A) (sh B) (sh D) (sh neg) (sh a) (sh b) (sh d) (sh sign) hs ks es

theorem actual_Euler_log_Gamma_rational_representation_independence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((source (var 0) (var 2) (var 3) ⋏ source (var 4) (var 6) (var 7)) ⟶
        (argument (var 0) (var 1) (var 2) (var 3) ≐ argument (var 4) (var 5) (var 6) (var 7)) ⟶
        crossEquivalent sampleF sampleF (sampleData (var 0) (var 1) (var 2) (var 3))
          (sampleData (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (.impI (canonical_cross _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRepresentation
