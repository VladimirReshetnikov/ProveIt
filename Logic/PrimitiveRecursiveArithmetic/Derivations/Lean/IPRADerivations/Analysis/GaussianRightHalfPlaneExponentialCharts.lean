import IPRADerivations.Analysis.GaussianRightHalfPlaneExponentialMargin
import IPRADerivations.Analysis.GaussianRightHalfPlaneArgumentExponentialBranches
import IPRADerivations.Analysis.GaussianRightHalfPlaneLogarithm

/-!
# Transport of the rational half-plane logarithm exponential across its charts

The small-chart recovery also applies to the argument with its coordinates
swapped. The radial exponential is unchanged by the swap, and conjugation
followed by multiplication by the imaginary unit sends the recovered
swapped point back to the original one.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneExponentialCharts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code eval_re_code eval_im_code mul)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents
  qmul qmul_canonical qmul_represents canonical_unique represents_congr)
open GaussianRightHalfPlaneArgumentExponential (smallExpData)
open GaussianRightHalfPlaneArgumentExponentialBranches (unsignedExpData signedExpData wideProductF wideProductData)
open GaussianRightHalfPlaneExponentialMargin (productF productData point)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen log_source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "H" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "G" => GaussianRightHalfPlaneArgument.nameF
local notation "J" => GaussianRightHalfPlaneArgument.unsignedF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "C" => GaussianNameConjugation.nameF
local notation "V" => E GaussianRightHalfPlaneArgument.smallF
local notation "U" => GaussianPositiveRationalHalfLogarithm.positiveF
local notation "rData" => GaussianRightHalfPlaneRadialLogarithm.data

def modulusData (A B D : PTm n) : PTm n :=
  GaussianPositiveRationalHalfLogarithm.positiveData (normNum A B) (normDen D)
def unsignedProductData (A B D : PTm n) : PTm n :=
  multiplyData U (E J) (modulusData A B D) (unsignedExpData A B)
def signedProductData (A B D neg : PTm n) : PTm n :=
  multiplyData U (E G) (modulusData A B D) (signedExpData A B neg)

def unsignedFormula (A B D : PTm n) : Fm PTm n :=
  crossEquivalent (multiplyF U (E J)) constantF (unsignedProductData A B D) (point A B D)
def smallFormula (A B D : PTm n) : Fm PTm n :=
  crossEquivalent productF constantF (productData A B D) (point A B D)
def negativePoint (A B D : PTm n) : PTm n := ofGaussian (code (ZT.ofNat A) (-(ZT.ofNat B))) D
def signedPoint (A B D neg : PTm n) : PTm n :=
  RationalArithmetic.select neg (point A B D) (negativePoint A B D)

private theorem radial_cross (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent U (E H) (modulusData A B D)
      (GaussianRightHalfPlaneRadialLogarithm.exponentialData A B D) :=
  GaussianPositiveRationalHalfLogarithm.positive_cross _ _ (log_source A B D hA hD)

private theorem left_regular (f g : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] pointCN f x :=
  cross_trans _ _ _ _ _ _ h (cross_symm _ _ _ _ h)

private theorem modulus_regular (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] pointCN U (modulusData A B D) :=
  left_regular _ _ _ _ (radial_cross A B D hA hD)

private theorem small_exp_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] pointCN V (smallExpData A B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianRightHalfPlaneArgument.small_input A B hA hB)

private theorem unsigned_exp_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] pointCN (E J) (unsignedExpData A B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianRightHalfPlaneArgument.unsigned_input A B hA)

private theorem modulus_real (A B D : PTm n) :
    Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples U (modulusData A B D) := by
  let a := normNum (Syn.shift A) (Syn.shift B)
  let b := normDen (Syn.shift D)
  let p : PTm (n+1) := var 0
  let f := E GaussianPositiveRationalHalfLogarithm.quarterF
  let x := exponentialInputData GaussianPositiveRationalHalfLogarithm.quarterF
    (GaussianPositiveRationalHalfLogarithm.quarterData a b)
  have hc := GaussianNameArithmetic.multiply_canonical (Γ := Γ.map Fm.shift) f (C f) x x p
  have hp := GaussianExponentialRealPart.square_sample_positive (Γ := Γ.map Fm.shift) f p x
  have shifted : Syn.shift (modulusData A B D) = GaussianPositiveRationalHalfLogarithm.positiveData a b := by
    simp [modulusData,Syn.shift,normNum,normDen,a,b]
  refine .allI ?_
  rw [shifted]
  exact .andI hc hp.andE₁

private theorem modulus_fixed (A B D : PTm n) (h : Γ ⊢[PRAAx] pointCN U (modulusData A B D)) :
    Γ ⊢[PRAAx] crossEquivalent (C U) U (modulusData A B D) (modulusData A B D) :=
  GaussianNamedHalf.conjugate_fixed U _ h (modulus_real A B D)

private theorem cross_right_eq (f g : PR 2) (x y z : PTm n)
    (e : Γ ⊢[PRAAx] y ≐ z) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent f g x z := by
  let F : Fm PTm 2 := crossEquivalent f g (var 0) (var 1)
  have old : Γ ⊢[PRAAx] F.subst ![x,y] := by
    simpa only [F,GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using h
  have out : Γ ⊢[PRAAx] F.subst ![x,z] :=
    Prf.eqSubst (Ax := PRAAx) (Γ := Γ) F (σ := ![x,y]) (σ' := ![x,z])
      (fun i => by fin_cases i; exact .eqRefl x; exact e) old
  simpa only [F,GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using out

private theorem modulus_swap (A B D : PTm n) (h : Γ ⊢[PRAAx] pointCN U (modulusData A B D)) :
    Γ ⊢[PRAAx] crossEquivalent U U (modulusData A B D) (modulusData B A D) := by
  have e : Γ ⊢[PRAAx] modulusData A B D ≐ modulusData B A D := by
    simpa only [modulusData,GaussianPositiveRationalHalfLogarithm.subst_positiveData,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
      (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (GaussianPositiveRationalHalfLogarithm.positiveData (var 0) (var 1) : PTm 2)
        (σ := ![normNum A B,normDen D]) (σ' := ![normNum B A,normDen D]) (fun i => by
          fin_cases i
          exact add_comm _ _
          exact .eqRefl _))
  exact cross_right_eq U U _ _ _ e (cross_refl U _ h)

private theorem native_conjugate (A B : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (GaussianRationalReciprocal.conjugate (code (ZT.ofNat A) (ZT.ofNat B)))
      (code (ZT.ofNat A) (-(ZT.ofNat B))) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRationalReciprocal.re_conjugate, GaussianRationalReciprocal.im_conjugate,
      eval_re_code, eval_im_code, ZT.toZ_neg]

private theorem finite_conjugate (A B D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianRationalConjugation.point (point A B D) ≐ negativePoint A B D := by
  let z := code (ZT.ofNat A) (ZT.ofNat B)
  have rep := GaussianRationalConjugation.point_represents (point A B D) z D hD (ofGaussian_represents _ _ hD)
  exact canonical_unique _ _ _ D (GaussianRationalConjugation.point_canonical _)
    (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) (native_conjugate A B) (.eqRefl _) rep) (ofGaussian_represents _ _ hD)

private theorem constant_conjugate (A B D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent (C constantF) constantF (point A B D) (negativePoint A B D) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameConjugation.regular _ _ (constant_regular _)) (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let a := Syn.shift A
  let b := Syn.shift B
  let d := Syn.shift D
  let p : PTm (n+1) := var 0
  have hd : Δ ⊢[PRAAx] le one d := by simpa [Fm.shift,Syn.shift,Δ,d] using hD.shift
  have e := (GaussianNameConjugation.sample_at (Γ := Δ) constantF p (point a b d)).eqTrans
    (GaussianRationalConjugation.point_congr (constant_at p (point a b d)))
  simpa [GaussianNameConjugation.pointwiseEqual,Syn.shift,point,negativePoint,Δ,a,b,d,p] using
    e.eqTrans ((finite_conjugate a b d hd).eqTrans (constant_at p (negativePoint a b d)).eqSymm)

private theorem imaginary_rotate (A B D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qmul imaginaryPoint (negativePoint B A D) ≐ point A B D := by
  let v := code (ZT.ofNat B) (-(ZT.ofNat A))
  let z := code (ZT.ofNat A) (ZT.ofNat B)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul imaginaryCode v) z := by
    have hre := GaussianRootAlgebra.re_mul (Γ := Γ) imaginaryCode v
    have him := GaussianRootAlgebra.im_mul (Γ := Γ) imaginaryCode v
    apply GaussianRootAlgebra.equal_of_values
    · rw [hre]
      simp only [v,z,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat,ZT.toZ_neg]
      ipra_simps
      ring
    · rw [him]
      simp only [v,z,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat,ZT.toZ_neg]
      ipra_simps
      ring
  have r := qmul_represents imaginaryPoint (negativePoint B A D) imaginaryCode v one D (le_refl _) hD
    (ofGaussian_represents _ _ (le_refl _)) (ofGaussian_represents _ _ hD)
  exact canonical_unique _ _ _ D (qmul_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) native (one_mul _) r) (ofGaussian_represents _ _ hD)

private theorem left_rotate (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF g (multiplyF f h))
      (multiplyData f (multiplyF g h) x (multiplyData g h y z))
      (multiplyData g (multiplyF f h) y (multiplyData f h x z)) := by
  have rotate := multiply_cross (multiplyF f g) (multiplyF g f) h h
    (multiplyData f g x y) (multiplyData g f y x) z z
    (multiply_fast _ _ _ _ hf hg) (multiply_fast _ _ _ _ hg hf) hh hh
    (multiply_commutative f g x y hf hg) (cross_refl _ _ hh)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative f g h x y z hf hg hh))
    (cross_trans _ _ _ _ _ _ rotate (multiply_associative g f h y x z hg hf hh))

private theorem conjugated_product (A B a b D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] pointCN U (modulusData a b D))
    (hu : Γ ⊢[PRAAx] pointCN U (modulusData A B D))
    (hr : Γ ⊢[PRAAx] crossEquivalent U U (modulusData A B D) (modulusData a b D))
    (P : PR 2) (y : PTm n) (hP : Γ ⊢[PRAAx] pointCN P y)
    (proof : Γ ⊢[PRAAx] crossEquivalent (multiplyF U P) constantF
      (multiplyData U P (modulusData a b D) y) (point a b D)) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF U (C P)) constantF
      (multiplyData U (C P) (modulusData A B D) y) (negativePoint a b D) := by
  let u := modulusData A B D
  let v := modulusData a b D
  have change := cross_trans _ _ _ _ _ _ hr (cross_symm _ _ _ _ (modulus_fixed a b D hq))
  have cP := GaussianNameConjugation.regular P y hP
  have cU := GaussianNameConjugation.regular U v hq
  have first := multiply_cross U (C U) (C P) (C P) u v y y hu cU cP cP change (cross_refl _ _ cP)
  have factor := GaussianNameConjugation.multiply_cross U P v y hq hP
  have result := GaussianNameConjugation.conjugate_cross _ _ _ _ proof
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ factor)
      (cross_trans _ _ _ _ _ _ result (constant_conjugate a b D hD)))

theorem unsigned_small (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le B A) (hD : Γ ⊢[PRAAx] le one D) (proof : Γ ⊢[PRAAx] smallFormula A B D) :
    Γ ⊢[PRAAx] unsignedFormula A B D := by
  have u := modulus_regular A B D hA hD
  have first := multiply_cross U U (E J) V (modulusData A B D) (modulusData A B D)
    (unsignedExpData A B) (smallExpData A B)
    u u (unsigned_exp_regular A B hA) (small_exp_regular A B hA hB) (cross_refl _ _ u)
    (GaussianRightHalfPlaneArgumentExponentialBranches.small_chart A B hA hB)
  exact cross_trans _ _ _ _ _ _ first proof

theorem unsigned_large (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] lt A B) (hD : Γ ⊢[PRAAx] le one D) (proof : Γ ⊢[PRAAx] smallFormula B A D) :
    Γ ⊢[PRAAx] unsignedFormula A B D := by
  let x := modulusData A B D
  let y := smallExpData B A
  let c := imaginaryPoint (n := n)
  let W := C V
  have hB' := le_trans hA (le_of_lt hB)
  have u := modulus_regular A B D hA hD
  have ur := modulus_regular B A D hB' hD
  have v := small_exp_regular B A hB' (le_of_lt hB)
  have w := GaussianNameConjugation.regular _ _ v
  have i := constant_regular (Γ := Γ) c
  have branch := multiply_cross U U (E J) wideProductF x x (unsignedExpData A B) (wideProductData A B)
    u u (unsigned_exp_regular A B hA) (multiply_fast _ _ _ _ i w) (cross_refl _ _ u)
    (GaussianRightHalfPlaneArgumentExponentialBranches.large_chart A B hA hB)
  have rotate := left_rotate U constantF W x c y u i w
  have swapped := conjugated_product A B B A D hD ur u (modulus_swap A B D u) V y v proof
  have finish := multiply_cross constantF constantF (multiplyF U W) constantF
    c c (multiplyData U W x y) (negativePoint B A D) i i (multiply_fast _ _ _ _ u w)
      (constant_regular _) (cross_refl _ _ i) swapped
  exact cross_trans _ _ _ _ _ _ branch
    (cross_trans _ _ _ _ _ _ rotate
      (cross_trans _ _ _ _ _ _ finish
        (cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross c (negativePoint B A D))
          (GaussianArctangentExponentialPeriod.constant_cross_congr _ _ (imaginary_rotate A B D hD)))))

private theorem signed_recovery (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (recovery : Γ ⊢[PRAAx] unsignedFormula A B D) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF U (E G)) constantF (signedProductData A B D neg) (signedPoint A B D neg) := by
  let x := modulusData A B D
  let y := unsignedExpData A B
  let z := signedExpData A B neg
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have u := modulus_regular A B D hA hD
  have v := unsigned_exp_regular A B hA
  have w := GaussianRadiusExponentialName.name_regular G _ _
    (GaussianRightHalfPlaneArgument.exponential_input A B neg h.andE₁)
  refine .orE h.andE₁.andE₂ ?_ ?_
  · have sign := GaussianRightHalfPlaneArgumentExponentialBranches.nonnegative_imaginary A B neg hA.wk Prf.hyp0
    have product := multiply_cross U U (E G) (E J) x x z y u.wk u.wk w.wk v.wk (cross_refl _ _ u.wk) sign
    have target := RationalArithmetic.select_zero (Γ := (neg ≐ zero) :: Γ) neg (point A B D) (negativePoint A B D) Prf.hyp0
    exact cross_trans _ _ _ _ _ _ product (cross_trans _ _ _ _ _ _ recovery.wk
      (GaussianArctangentExponentialPeriod.constant_cross_congr _ _ target.eqSymm))
  · have sign := GaussianRightHalfPlaneArgumentExponentialBranches.nonpositive_imaginary A B neg hA.wk Prf.hyp0
    have product := multiply_cross U U (E G) (C (E J)) x x z y u.wk u.wk w.wk
      (GaussianNameConjugation.regular _ _ v.wk) (cross_refl _ _ u.wk) sign
    have result := conjugated_product (Γ := (neg ≐ one) :: Γ) A B A B D hD.wk u.wk u.wk (cross_refl _ _ u.wk) (E J) y v.wk recovery.wk
    have target := RationalArithmetic.select_one (Γ := (neg ≐ one) :: Γ) neg (point A B D) (negativePoint A B D) Prf.hyp0
    exact cross_trans _ _ _ _ _ _ product (cross_trans _ _ _ _ _ _ result
      (GaussianArctangentExponentialPeriod.constant_cross_congr _ _ target.eqSymm))

theorem recover (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (small : (le B A :: Γ) ⊢[PRAAx] smallFormula A B D)
    (wide : (lt A B :: Γ) ⊢[PRAAx] smallFormula B A D) :
    Γ ⊢[PRAAx] crossEquivalent (E L) constantF
      (exponentialInputData L (GaussianRightHalfPlaneLogarithm.data A B D neg)) (signedPoint A B D neg) := by
  let x := rData A B D
  let y := GaussianRightHalfPlaneArgument.data A B neg
  let z := GaussianRightHalfPlaneLogarithm.data A B D neg
  let R := GaussianNameBounds.U H x
  let S := GaussianRightHalfPlaneArgument.radius (n := n)
  let T := GaussianNameBounds.U L z
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have hx := exponential_input H x (GaussianRightHalfPlaneRadialLogarithm.regular A B D hA hD)
  have hy := GaussianRightHalfPlaneArgument.exponential_input A B neg h.andE₁
  have hz := exponential_input L z (GaussianRightHalfPlaneLogarithm.regular A B D neg h)
  have a := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent H G L R S T x y z
    hx hy hz (cross_refl _ _ hz.andE₁)
  have er := GaussianRadiusExponentialName.name_regular H R x hx
  have eg := GaussianRadiusExponentialName.name_regular G S y hy
  have rad := multiply_cross (E H) U (E G) (E G) (ed R x) (modulusData A B D) (ed S y) (ed S y)
    er (modulus_regular A B D hA hD) eg eg (cross_symm _ _ _ _ (radial_cross A B D hA hD))
      (cross_refl _ _ eg)
  have eq : Γ ⊢[PRAAx] unsignedFormula A B D :=
    .orE (lt_or_le A B) (unsigned_large A B D hA.wk Prf.hyp0 hD.wk wide)
      (unsigned_small A B D hA.wk Prf.hyp0 hD.wk small)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ a)
    (cross_trans _ _ _ _ _ _ rad (signed_recovery A B D neg h eq))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneExponentialCharts
