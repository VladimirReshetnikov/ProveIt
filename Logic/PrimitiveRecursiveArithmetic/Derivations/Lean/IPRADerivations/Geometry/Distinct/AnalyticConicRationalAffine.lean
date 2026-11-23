import IPRADerivations.Geometry.Distinct.AnalyticConicAffine
import IPRADerivations.Analysis.RationalAlgebra

/-!
# Actual rational affine pullback and evaluation of conics

The source packet's `con:covariance` and discriminant part of
`con:invariants` are proved for common-positive-denominator records.
A conic stores six signed integer numerators and a positive denominator D;
an affine map stores its four linear and two translation numerators over E;
a point stores its two signed coordinate numerators over F. Evaluation
normalizes the cleared numerator over D*F^2 using the existing actual
rational normalizer. The transformed conic denominator is D*E^2 and the
image point denominator is E*F.

The checked integer pullback is applied to (a,b,c,E*d,E*e,E^2*f).
Every output denominator and every canonical rational equality is proved.
No invertibility, rational inverse or conic classification is asserted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Geometry.Distinct.AnalyticConicRationalAffine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open AnalyticConicAffine (read pack6 encode decode read_congr read_pack6_0 read_pack6_1 read_pack6_2 read_pack6_3 read_pack6_4 read_pack6_5)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed normalize_well_formed)
open LeanProofs.IPRA.Analysis.RationalArithmetic (represents multiply multiply_guard)
open LeanProofs.IPRA.Analysis.RationalRepresentations (represents_multiply)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def numerators (r : PTm n) : PTm n := fstT r
def denominator (r : PTm n) : PTm n := sndT r
def valid (r : PTm n) : Fm PTm n := le one (denominator r)
def record (c D : PTm n) : PTm n := pairT c D

def lift (c E : PTm n) : PTm n := pack6 (read 0 c) (read 1 c) (read 2 c)
  (ZT.ofNat E*read 3 c) (ZT.ofNat E*read 4 c) (ZT.ofNat E*ZT.ofNat E*read 5 c)
def homogeneous (c : PTm n) (x y : ZT n) (F : PTm n) : ZT n :=
  read 0 c*x*x+read 1 c*x*y+read 2 c*y*y+
    read 3 c*x*ZT.ofNat F+read 4 c*y*ZT.ofNat F+read 5 c*ZT.ofNat F*ZT.ofNat F

def pullback (c m : PTm n) : PTm n := record
  (ap2 AnalyticConicAffine.pullbackF (lift (numerators c) (denominator m)) (numerators m))
  (denominator c*(denominator m*denominator m))
def imageX (m p : PTm n) : ZT n := read 0 (numerators m)*read 0 (numerators p)+read 1 (numerators m)*read 1 (numerators p)+
  read 4 (numerators m)*ZT.ofNat (denominator p)
def imageY (m p : PTm n) : ZT n := read 2 (numerators m)*read 0 (numerators p)+read 3 (numerators m)*read 1 (numerators p)+
  read 5 (numerators m)*ZT.ofNat (denominator p)
def image (m p : PTm n) : PTm n := record
  (pack6 (imageX m p) (imageY m p) (ZT.natLit 0) (ZT.natLit 0) (ZT.natLit 0) (ZT.natLit 0))
  (denominator m*denominator p)
def evaluationNumerator (c p : PTm n) : ZT n :=
  homogeneous (numerators c) (read 0 (numerators p)) (read 1 (numerators p)) (denominator p)
def evaluationDenominator (c p : PTm n) : PTm n := denominator c*(denominator p*denominator p)
def evaluate (c p : PTm n) : PTm n := normalize (evaluationNumerator c p) (evaluationDenominator c p)
def discriminant (c : PTm n) : PTm n := normalize (AnalyticConicAffine.discriminant (numerators c)) (denominator c*denominator c)
def determinant (m : PTm n) : PTm n := normalize (AnalyticConicAffine.determinant (numerators m)) (denominator m*denominator m)

@[simp] theorem subst_numerators {j : ℕ} (σ : Fin n → PTm j) (r : PTm n) : Syn.subst σ (numerators r) = numerators (Syn.subst σ r) := by simp [numerators]
@[simp] theorem subst_denominator {j : ℕ} (σ : Fin n → PTm j) (r : PTm n) : Syn.subst σ (denominator r) = denominator (Syn.subst σ r) := by simp [denominator]
@[simp] theorem subst_valid {j : ℕ} (σ : Fin n → PTm j) (r : PTm n) : (valid r).subst σ = valid (Syn.subst σ r) := by simp [valid]
@[simp] theorem subst_record {j : ℕ} (σ : Fin n → PTm j) (c D : PTm n) : Syn.subst σ (record c D) = record (Syn.subst σ c) (Syn.subst σ D) := by simp [record]
@[simp] theorem subst_lift {j : ℕ} (σ : Fin n → PTm j) (c E : PTm n) : Syn.subst σ (lift c E) = lift (Syn.subst σ c) (Syn.subst σ E) := by simp [lift]
@[simp] theorem subst_homogeneous {j : ℕ} (σ : Fin n → PTm j) (c : PTm n) (x y : ZT n) (F : PTm n) :
    (homogeneous c x y F).subst σ = homogeneous (Syn.subst σ c) (x.subst σ) (y.subst σ) (Syn.subst σ F) := by simp [homogeneous]
@[simp] theorem subst_pullback {j : ℕ} (σ : Fin n → PTm j) (c m : PTm n) : Syn.subst σ (pullback c m) = pullback (Syn.subst σ c) (Syn.subst σ m) := by simp [pullback]
@[simp] theorem subst_imageX {j : ℕ} (σ : Fin n → PTm j) (m p : PTm n) : (imageX m p).subst σ = imageX (Syn.subst σ m) (Syn.subst σ p) := by simp [imageX]
@[simp] theorem subst_imageY {j : ℕ} (σ : Fin n → PTm j) (m p : PTm n) : (imageY m p).subst σ = imageY (Syn.subst σ m) (Syn.subst σ p) := by simp [imageY]
@[simp] theorem subst_image {j : ℕ} (σ : Fin n → PTm j) (m p : PTm n) : Syn.subst σ (image m p) = image (Syn.subst σ m) (Syn.subst σ p) := by simp [image]
@[simp] theorem subst_evaluationNumerator {j : ℕ} (σ : Fin n → PTm j) (c p : PTm n) : (evaluationNumerator c p).subst σ = evaluationNumerator (Syn.subst σ c) (Syn.subst σ p) := by simp [evaluationNumerator]
@[simp] theorem subst_evaluationDenominator {j : ℕ} (σ : Fin n → PTm j) (c p : PTm n) : Syn.subst σ (evaluationDenominator c p) = evaluationDenominator (Syn.subst σ c) (Syn.subst σ p) := by simp [evaluationDenominator]
@[simp] theorem subst_evaluate {j : ℕ} (σ : Fin n → PTm j) (c p : PTm n) : Syn.subst σ (evaluate c p) = evaluate (Syn.subst σ c) (Syn.subst σ p) := by simp [evaluate]
@[simp] theorem subst_discriminant {j : ℕ} (σ : Fin n → PTm j) (c : PTm n) : Syn.subst σ (discriminant c) = discriminant (Syn.subst σ c) := by simp [discriminant]
@[simp] theorem subst_determinant {j : ℕ} (σ : Fin n → PTm j) (c : PTm n) : Syn.subst σ (determinant c) = determinant (Syn.subst σ c) := by simp [determinant]

theorem record_numerators (c D : PTm n) : Γ ⊢[PRAAx] numerators (record c D) ≐ c := fst_pair _ _
theorem record_denominator (c D : PTm n) : Γ ⊢[PRAAx] denominator (record c D) ≐ D := snd_pair _ _
theorem pullback_denominator (c m : PTm n) : Γ ⊢[PRAAx]
    denominator (pullback c m) ≐ denominator c*(denominator m*denominator m) := record_denominator _ _
theorem image_denominator (m p : PTm n) : Γ ⊢[PRAAx]
    denominator (image m p) ≐ denominator m*denominator p := record_denominator _ _
theorem pullback_valid (c m : PTm n) (hc : Γ ⊢[PRAAx] valid c) (hm : Γ ⊢[PRAAx] valid m) : Γ ⊢[PRAAx] valid (pullback c m) :=
  le_congr (.eqRefl _) (pullback_denominator c m).eqSymm
    (Analysis.RationalAlgebra.positive_product hc (Analysis.RationalAlgebra.positive_product hm hm))
theorem image_valid (m p : PTm n) (hm : Γ ⊢[PRAAx] valid m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx] valid (image m p) :=
  le_congr (.eqRefl _) (image_denominator m p).eqSymm (Analysis.RationalAlgebra.positive_product hm hp)
theorem evaluation_denominator_positive (c p : PTm n) (hc : Γ ⊢[PRAAx] valid c) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx] le one (evaluationDenominator c p) :=
  Analysis.RationalAlgebra.positive_product hc (Analysis.RationalAlgebra.positive_product hp hp)

theorem pullback_read_value (c m : PTm n) (k : ℕ) : ZT.toZ Γ (read k (numerators (pullback c m))) =
    ZT.toZ Γ (read k (AnalyticConicAffine.pullback (lift (numerators c) (denominator m)) (numerators m))) :=
  read_congr k ((record_numerators _ _).eqTrans (AnalyticConicAffine.pullback_at _ _))
theorem image_x_value (m p : PTm n) : ZT.toZ Γ (read 0 (numerators (image m p))) = ZT.toZ Γ (imageX m p) :=
  (read_congr 0 (record_numerators _ _)).trans (read_pack6_0 _ _ _ _ _ _)
theorem image_y_value (m p : PTm n) : ZT.toZ Γ (read 1 (numerators (image m p))) = ZT.toZ Γ (imageY m p) :=
  (read_congr 1 (record_numerators _ _)).trans (read_pack6_1 _ _ _ _ _ _)

/-- The exact cleared numerator identity; no denominator positivity is
needed for this polynomial stage. -/
theorem numerator_covariance (c m p : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (evaluationNumerator (pullback c m) p) (evaluationNumerator c (image m p)) := by
  apply ZT.derive
  have den := natEq (image_denominator (Γ := Γ) m p)
  simp only [evaluationNumerator,homogeneous,ZT.toZ_add,ZT.toZ_mul,pullback_read_value,image_x_value,image_y_value]
  simp only [AnalyticConicAffine.pullback,read_pack6_0,read_pack6_1,read_pack6_2,read_pack6_3,read_pack6_4,read_pack6_5,
    AnalyticConicAffine.evaluate,lift,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_natLit,ZT.toZ_ofNat,imageX,imageY]
  ipra_simps
  rw [den]
  ring

theorem denominator_covariance (c m p : PTm n) : Γ ⊢[PRAAx]
    evaluationDenominator (pullback c m) p ≐ evaluationDenominator c (image m p) := by
  apply deriveNat
  have left := natEq (pullback_denominator (Γ := Γ) c m)
  have right := natEq (image_denominator (Γ := Γ) m p)
  dsimp only [evaluationDenominator]
  ipra_simps
  rw [left,right]
  ring

theorem evaluate_value (c p : PTm n) (hc : Γ ⊢[PRAAx] valid c) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    represents (evaluate c p) (evaluationNumerator c p) (evaluationDenominator c p) :=
  normalize_preserves_value _ _ (evaluation_denominator_positive c p hc hp)
theorem evaluate_canonical (c p : PTm n) (hc : Γ ⊢[PRAAx] valid c) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    wellFormed (evaluate c p) := normalize_well_formed _ _ (evaluation_denominator_positive c p hc hp)

theorem rational_evaluation_covariance (c m p : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] valid m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    evaluate (pullback c m) p ≐ evaluate c (image m p) := by
  have ht := pullback_valid c m hc hm
  have hi := image_valid m p hm hp
  apply Analysis.RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (evaluate_canonical _ _ ht hp) (evaluate_canonical _ _ hc hi)
    (evaluate_value _ _ ht hp) (evaluate_value _ _ hc hi)
    (evaluation_denominator_positive _ _ ht hp) (evaluation_denominator_positive _ _ hc hi)
  apply ZT.derive
  have num := ZT.toZ_eq (numerator_covariance (Γ := Γ) c m p)
  have den := natEq (denominator_covariance (Γ := Γ) c m p)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [num,den]

theorem native_discriminant_covariance (c m : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (AnalyticConicAffine.discriminant (numerators (pullback c m)))
      ((AnalyticConicAffine.determinant (numerators m)).sq*AnalyticConicAffine.discriminant (numerators c)) := by
  apply ZT.derive
  simp only [AnalyticConicAffine.discriminant,AnalyticConicAffine.determinant,ZT.toZ_sq,ZT.toZ_sub,ZT.toZ_mul,pullback_read_value]
  simp only [AnalyticConicAffine.pullback,lift,read_pack6_0,read_pack6_1,read_pack6_2,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_natLit]
  ring

theorem discriminant_value (c : PTm n) (hc : Γ ⊢[PRAAx] valid c) : Γ ⊢[PRAAx]
    represents (discriminant c) (AnalyticConicAffine.discriminant (numerators c)) (denominator c*denominator c) :=
  normalize_preserves_value _ _ (Analysis.RationalAlgebra.positive_product hc hc)
theorem determinant_value (m : PTm n) (hm : Γ ⊢[PRAAx] valid m) : Γ ⊢[PRAAx]
    represents (determinant m) (AnalyticConicAffine.determinant (numerators m)) (denominator m*denominator m) :=
  normalize_preserves_value _ _ (Analysis.RationalAlgebra.positive_product hm hm)

theorem rational_discriminant_covariance (c m : PTm n) (hc : Γ ⊢[PRAAx] valid c) (hm : Γ ⊢[PRAAx] valid m) : Γ ⊢[PRAAx]
    discriminant (pullback c m) ≐ multiply (multiply (determinant m) (determinant m)) (discriminant c) := by
  let a := AnalyticConicAffine.discriminant (numerators (pullback c m))
  let b := AnalyticConicAffine.determinant (numerators m)
  let d := AnalyticConicAffine.discriminant (numerators c)
  let E := denominator m*denominator m
  let D := denominator c*denominator c
  have hE : Γ ⊢[PRAAx] le one E := Analysis.RationalAlgebra.positive_product hm hm
  have hD : Γ ⊢[PRAAx] le one D := Analysis.RationalAlgebra.positive_product hc hc
  have hp := pullback_valid c m hc hm
  have left := discriminant_value (pullback c m) hp
  have square : Γ ⊢[PRAAx] represents (multiply (determinant m) (determinant m)) (b*b) (E*E) :=
    represents_multiply _ _ _ _ _ _ (determinant_value m hm) (determinant_value m hm)
  have right : Γ ⊢[PRAAx] represents (multiply (multiply (determinant m) (determinant m)) (discriminant c)) ((b*b)*d) ((E*E)*D) :=
    represents_multiply _ _ _ _ _ _ square (discriminant_value c hc)
  apply Analysis.RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (normalize_well_formed _ _ (Analysis.RationalAlgebra.positive_product hp hp)) (multiply_guard _ _) left right
    (Analysis.RationalAlgebra.positive_product hp hp)
    (Analysis.RationalAlgebra.positive_product (Analysis.RationalAlgebra.positive_product hE hE) hD)
  apply ZT.derive
  have num := ZT.toZ_eq (native_discriminant_covariance (Γ := Γ) c m)
  have den := natEq (pullback_denominator (Γ := Γ) c m)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_sq] at num ⊢
  dsimp only [a,b,d,E,D]
  ipra_simps
  rw [num,den]
  ring

/-- The canonical rational coefficient read from an actual common-denominator record. -/
def coefficient (k : ℕ) (c : PTm n) : PTm n := normalize (read k (numerators c)) (denominator c)
theorem coefficient_value (k : ℕ) (c : PTm n) (hc : Γ ⊢[PRAAx] valid c) : Γ ⊢[PRAAx]
    represents (coefficient k c) (read k (numerators c)) (denominator c) := normalize_preserves_value _ _ hc

def pullbackF : PR 2 := PTm.toPR (pullback (var 0) (var 1))
def imageF : PR 2 := PTm.toPR (image (var 0) (var 1))
def evaluateF : PR 2 := PTm.toPR (evaluate (var 0) (var 1))
def discriminantF : PR 1 := PTm.toPR (discriminant (var 0))
def determinantF : PR 1 := PTm.toPR (determinant (var 0))

theorem pullback_at (c m : PTm n) : Γ ⊢[PRAAx] ap2 pullbackF c m ≐ pullback c m := by
  simpa only [ap2,pullbackF,subst_pullback,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (pullback (var 0) (var 1) : PTm 2) ![c,m]
theorem image_at (m p : PTm n) : Γ ⊢[PRAAx] ap2 imageF m p ≐ image m p := by
  simpa only [ap2,imageF,subst_image,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (image (var 0) (var 1) : PTm 2) ![m,p]
theorem evaluate_at (c p : PTm n) : Γ ⊢[PRAAx] ap2 evaluateF c p ≐ evaluate c p := by
  simpa only [ap2,evaluateF,subst_evaluate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (evaluate (var 0) (var 1) : PTm 2) ![c,p]
theorem discriminant_at (c : PTm n) : Γ ⊢[PRAAx] ap1 discriminantF c ≐ discriminant c := by
  simpa only [ap1,discriminantF,subst_discriminant,Syn.subst_var,Matrix.cons_val_zero,Matrix.head_cons] using
    toPR_eq (Γ := Γ) (discriminant (var 0) : PTm 1) ![c]
theorem determinant_at (m : PTm n) : Γ ⊢[PRAAx] ap1 determinantF m ≐ determinant m := by
  simpa only [ap1,determinantF,subst_determinant,Syn.subst_var,Matrix.cons_val_zero,Matrix.head_cons] using
    toPR_eq (Γ := Γ) (determinant (var 0) : PTm 1) ![m]

theorem actual_evaluation_covariance (c m p : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] valid m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    ap2 evaluateF (ap2 pullbackF c m) p ≐ ap2 evaluateF c (ap2 imageF m p) := by
  have left := (congrAp2 evaluateF (pullback_at (Γ := Γ) c m) (.eqRefl p)).eqTrans (evaluate_at (pullback c m) p)
  have right := (congrAp2 evaluateF (.eqRefl c) (image_at (Γ := Γ) m p)).eqTrans (evaluate_at c (image m p))
  exact left.eqTrans ((rational_evaluation_covariance c m p hc hm hp).eqTrans right.eqSymm)

theorem actual_discriminant_covariance (c m : PTm n) (hc : Γ ⊢[PRAAx] valid c) (hm : Γ ⊢[PRAAx] valid m) : Γ ⊢[PRAAx]
    ap1 discriminantF (ap2 pullbackF c m) ≐
      multiply (multiply (ap1 determinantF m) (ap1 determinantF m)) (ap1 discriminantF c) := by
  have left := (congrAp1 discriminantF (pullback_at (Γ := Γ) c m)).eqTrans (discriminant_at (pullback c m))
  have right := Analysis.RationalAlgebra.multiply_congr
    (Analysis.RationalAlgebra.multiply_congr (determinant_at (Γ := Γ) m) (determinant_at m)) (discriminant_at c)
  exact left.eqTrans ((rational_discriminant_covariance c m hc hm).eqTrans right.eqSymm)

theorem actual_output_guards (c m p : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] valid m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    valid (ap2 pullbackF c m) ⋏ valid (ap2 imageF m p) := .andI
  (le_congr (.eqRefl _) (congrSnd (pullback_at c m)).eqSymm (pullback_valid c m hc hm))
  (le_congr (.eqRefl _) (congrSnd (image_at m p)).eqSymm (image_valid m p hm hp))

theorem rational_affine_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((valid (var 0) ⋏ (valid (var 1) ⋏ valid (var 2))) ⟶
      ap2 evaluateF (ap2 pullbackF (var 0) (var 1)) (var 2) ≐ ap2 evaluateF (var 0) (ap2 imageF (var 1) (var 2))) :=
  closeUniv 3 (.impI (actual_evaluation_covariance _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem rational_discriminant_covariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((valid (var 0) ⋏ valid (var 1)) ⟶ ap1 discriminantF (ap2 pullbackF (var 0) (var 1)) ≐
      multiply (multiply (ap1 determinantF (var 1)) (ap1 determinantF (var 1))) (ap1 discriminantF (var 0))) :=
  closeUniv 2 (.impI (actual_discriminant_covariance _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem rational_affine_output_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((valid (var 0) ⋏ (valid (var 1) ⋏ valid (var 2))) ⟶ valid (ap2 pullbackF (var 0) (var 1)) ⋏ valid (ap2 imageF (var 1) (var 2))) :=
  closeUniv 3 (.impI (actual_output_guards _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Geometry.Distinct.AnalyticConicRationalAffine
