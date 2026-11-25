import IPRADerivations.Geometry.Distinct.AnalyticConicRationalAffine
import IPRADerivations.Foundations.GapDecision
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Actual rational inverse of an affine conic substitution

Source: `con:covariance` in the analytic geometry packet of 22 November.
For a map with common positive denominator E and native determinant delta,
use the positive inverse denominator |delta|^2. The numerator record is
E*delta times the linear adjugate, with the corresponding negative
adjugate translation. Both actual image roundtrips recover the original
canonical rational coordinate codes. Raw records need not be canonical.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Geometry.Distinct.AnalyticConicRationalInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open AnalyticConicAffine (read pack6 read_congr read_pack6_0 read_pack6_1 read_pack6_2 read_pack6_3 read_pack6_4 read_pack6_5)
open AnalyticConicRationalAffine (numerators denominator record valid coefficient image imageX imageY
  record_numerators record_denominator image_denominator image_x_value image_y_value image_valid)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalNormalForm (normalize_well_formed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def nativeDeterminant (m : PTm n) : ZT n := AnalyticConicAffine.determinant (numerators m)
def pivot (m : PTm n) : PTm n := zabs (nativeDeterminant m)*zabs (nativeDeterminant m)
def source (m : PTm n) : Fm PTm n := valid m ⋏ neg (ZT.eq (nativeDeterminant m) (ZT.natLit 0))
def inverseNumerators (m : PTm n) : PTm n :=
  let d := nativeDeterminant m
  let E := ZT.ofNat (denominator m)
  let a := read 0 (numerators m)
  let b := read 1 (numerators m)
  let c := read 2 (numerators m)
  let e := read 3 (numerators m)
  let t := read 4 (numerators m)
  let u := read 5 (numerators m)
  pack6 (E*d*e) (-(E*d*b)) (-(E*d*c)) (E*d*a) (d*(b*u-e*t)) (d*(c*t-a*u))
def inverse (m : PTm n) : PTm n := record (inverseNumerators m) (pivot m)
def multiplier (m : PTm n) : PTm n := denominator m*pivot m

def canonicalPoint (p : PTm n) : PTm n := pairT (coefficient 0 p) (coefficient 1 p)

@[simp] theorem subst_nativeDeterminant {j : ℕ} (σ : Fin n → PTm j) (m : PTm n) :
    (nativeDeterminant m).subst σ = nativeDeterminant (Syn.subst σ m) := by simp [nativeDeterminant]
@[simp] theorem subst_pivot {j : ℕ} (σ : Fin n → PTm j) (m : PTm n) : Syn.subst σ (pivot m) = pivot (Syn.subst σ m) := by simp only [pivot,PTm.subst_mul,Foundations.GapDecision.subst_zabs,subst_nativeDeterminant]
@[simp] theorem subst_source {j : ℕ} (σ : Fin n → PTm j) (m : PTm n) : (source m).subst σ = source (Syn.subst σ m) := by simp [source]
@[simp] theorem subst_inverseNumerators {j : ℕ} (σ : Fin n → PTm j) (m : PTm n) :
    Syn.subst σ (inverseNumerators m) = inverseNumerators (Syn.subst σ m) := by simp [inverseNumerators]
@[simp] theorem subst_inverse {j : ℕ} (σ : Fin n → PTm j) (m : PTm n) : Syn.subst σ (inverse m) = inverse (Syn.subst σ m) := by simp [inverse]
@[simp] theorem subst_multiplier {j : ℕ} (σ : Fin n → PTm j) (m : PTm n) : Syn.subst σ (multiplier m) = multiplier (Syn.subst σ m) := by simp [multiplier]
@[simp] theorem subst_coefficient {j : ℕ} (σ : Fin n → PTm j) (k : ℕ) (p : PTm n) :
    Syn.subst σ (coefficient k p) = coefficient k (Syn.subst σ p) := by simp [coefficient]
@[simp] theorem subst_canonicalPoint {j : ℕ} (σ : Fin n → PTm j) (p : PTm n) :
    Syn.subst σ (canonicalPoint p) = canonicalPoint (Syn.subst σ p) := by simp [canonicalPoint]

/-- Derive a positive integer pivot from the explicit nonzero signed
value, rather than requiring an additional apartness certificate. -/
theorem absolute_positive (d : ZT n) (hd : Γ ⊢[PRAAx] neg (ZT.eq d (ZT.natLit 0))) : Γ ⊢[PRAAx] le one (zabs d) := by
  refine .orE (zero_or_succ (zabs d)) ?_ ?_
  · have equal : ((zabs d ≐ zero) :: Γ) ⊢[PRAAx] d.pos ≐ d.neg :=
      le_antisymm (add_eq_zero_left Prf.hyp0) (add_eq_zero_left ((add_comm _ _).eqTrans Prf.hyp0))
    have bad : ((zabs d ≐ zero) :: Γ) ⊢[PRAAx] ZT.eq d (ZT.natLit 0) := by
      apply ZT.derive
      have e := natEq equal
      simp only [ZT.toZ,ZT.natLit,ZT.ofNat]
      ipra_simps
      linear_combination e
    exact .botE _ (.impE hd.wk bad)
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)

theorem pivot_positive (m : PTm n) (h : Γ ⊢[PRAAx] source m) : Γ ⊢[PRAAx] le one (pivot m) :=
  Analysis.RationalAlgebra.positive_product (absolute_positive _ h.andE₂) (absolute_positive _ h.andE₂)
theorem inverse_denominator (m : PTm n) : Γ ⊢[PRAAx] denominator (inverse m) ≐ pivot m := record_denominator _ _
theorem inverse_valid (m : PTm n) (h : Γ ⊢[PRAAx] source m) : Γ ⊢[PRAAx] valid (inverse m) :=
  le_congr (.eqRefl _) (inverse_denominator m).eqSymm (pivot_positive m h)
theorem inverse_read_value (m : PTm n) (k : ℕ) :
    ZT.toZ Γ (read k (numerators (inverse m))) = ZT.toZ Γ (read k (inverseNumerators m)) := read_congr k (record_numerators _ _)
theorem image_denominator_value (m p : PTm n) :
    𝔞(denominator (image m p)) = 𝔞(denominator m)*𝔞(denominator p) := by
  rw [natEq (image_denominator (Γ := Γ) m p)]
  ipra_simps

theorem inverse_denominator_value (m : PTm n) : 𝔞(denominator (inverse m)) = 𝔞(pivot m) := natEq (inverse_denominator m)

theorem native_roundtrips (m p : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (read 0 (numerators (image (inverse m) (image m p)))) (ZT.ofNat (multiplier m)*read 0 (numerators p)) ⋏
    (ZT.eq (read 1 (numerators (image (inverse m) (image m p)))) (ZT.ofNat (multiplier m)*read 1 (numerators p)) ⋏
    (ZT.eq (read 0 (numerators (image m (image (inverse m) p)))) (ZT.ofNat (multiplier m)*read 0 (numerators p)) ⋏
      ZT.eq (read 1 (numerators (image m (image (inverse m) p)))) (ZT.ofNat (multiplier m)*read 1 (numerators p)))) := by
  refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
  all_goals
    apply ZT.derive
    have sq := zabs_sq (Γ := Γ) (nativeDeterminant m)
    change 𝔞(pivot m) = _ at sq
    simp only [nativeDeterminant,AnalyticConicAffine.determinant,ZT.toZ_sub,ZT.toZ_mul] at sq
    simp only [image_x_value,image_y_value,imageX,imageY,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,
      image_denominator_value,inverse_denominator_value,inverse_read_value]
    simp only [inverseNumerators,read_pack6_0,read_pack6_1,read_pack6_2,read_pack6_3,read_pack6_4,read_pack6_5,
      ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat,nativeDeterminant,AnalyticConicAffine.determinant,multiplier]
    ipra_simps
    rw [sq]
    ring

theorem roundtrip_denominators (m p : PTm n) : Γ ⊢[PRAAx]
    (denominator (image (inverse m) (image m p)) ≐ multiplier m*denominator p) ⋏
      (denominator (image m (image (inverse m) p)) ≐ multiplier m*denominator p) := by
  refine .andI ?_ ?_
  all_goals
    ipra_lc [image_denominator_value, inverse_denominator_value, multiplier]

private theorem coordinate_rescaling (k : ℕ) (p q L : PTm n) (hp : Γ ⊢[PRAAx] valid p) (hq : Γ ⊢[PRAAx] valid q)
    (hn : Γ ⊢[PRAAx] ZT.eq (read k (numerators q)) (ZT.ofNat L*read k (numerators p)))
    (hd : Γ ⊢[PRAAx] denominator q ≐ L*denominator p) : Γ ⊢[PRAAx] coefficient k q ≐ coefficient k p := by
  apply Analysis.RationalFiniteSum.canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hq) (normalize_well_formed _ _ hp)
    (AnalyticConicRationalAffine.coefficient_value k q hq) (AnalyticConicRationalAffine.coefficient_value k p hp) hq hp
  apply ZT.derive
  have num := ZT.toZ_eq hn
  have den := natEq hd
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at num ⊢
  rw [num,den]
  ipra_simps
  ring

private alias pair_congr := Common.congrPairT

theorem canonical_roundtrips (m p : PTm n) (hm : Γ ⊢[PRAAx] source m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    (canonicalPoint (image (inverse m) (image m p)) ≐ canonicalPoint p) ⋏
      (canonicalPoint (image m (image (inverse m) p)) ≐ canonicalPoint p) := by
  have hi := inverse_valid m hm
  have hp1 := image_valid m p hm.andE₁ hp
  have hp2 := image_valid (inverse m) p hi hp
  have hq1 := image_valid (inverse m) (image m p) hi hp1
  have hq2 := image_valid m (image (inverse m) p) hm.andE₁ hp2
  have native := native_roundtrips (Γ := Γ) m p
  have den := roundtrip_denominators (Γ := Γ) m p
  exact .andI
    (pair_congr (coordinate_rescaling 0 p _ _ hp hq1 native.andE₁ den.andE₁)
      (coordinate_rescaling 1 p _ _ hp hq1 native.andE₂.andE₁ den.andE₁))
    (pair_congr (coordinate_rescaling 0 p _ _ hp hq2 native.andE₂.andE₂.andE₁ den.andE₂)
      (coordinate_rescaling 1 p _ _ hp hq2 native.andE₂.andE₂.andE₂ den.andE₂))

private theorem evaluate_rescaling (c p q L : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hp : Γ ⊢[PRAAx] valid p) (hq : Γ ⊢[PRAAx] valid q)
    (hx : Γ ⊢[PRAAx] ZT.eq (read 0 (numerators q)) (ZT.ofNat L*read 0 (numerators p)))
    (hy : Γ ⊢[PRAAx] ZT.eq (read 1 (numerators q)) (ZT.ofNat L*read 1 (numerators p)))
    (hd : Γ ⊢[PRAAx] denominator q ≐ L*denominator p) : Γ ⊢[PRAAx]
    AnalyticConicRationalAffine.evaluate c q ≐ AnalyticConicRationalAffine.evaluate c p := by
  apply Analysis.RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (AnalyticConicRationalAffine.evaluate_canonical c q hc hq) (AnalyticConicRationalAffine.evaluate_canonical c p hc hp)
    (AnalyticConicRationalAffine.evaluate_value c q hc hq) (AnalyticConicRationalAffine.evaluate_value c p hc hp)
    (AnalyticConicRationalAffine.evaluation_denominator_positive c q hc hq)
    (AnalyticConicRationalAffine.evaluation_denominator_positive c p hc hp)
  apply ZT.derive
  have x := ZT.toZ_eq hx
  have y := ZT.toZ_eq hy
  have d := natEq hd
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at x y
  simp only [AnalyticConicRationalAffine.evaluationNumerator,AnalyticConicRationalAffine.evaluationDenominator,
    AnalyticConicRationalAffine.homogeneous,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  rw [x,y]
  ipra_simps
  rw [d]
  ring

theorem evaluation_roundtrips (c m p : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] source m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    (AnalyticConicRationalAffine.evaluate c (image (inverse m) (image m p)) ≐ AnalyticConicRationalAffine.evaluate c p) ⋏
      (AnalyticConicRationalAffine.evaluate c (image m (image (inverse m) p)) ≐ AnalyticConicRationalAffine.evaluate c p) := by
  have hi := inverse_valid m hm
  have hq1 := image_valid (inverse m) (image m p) hi (image_valid m p hm.andE₁ hp)
  have hq2 := image_valid m (image (inverse m) p) hm.andE₁ (image_valid (inverse m) p hi hp)
  have native := native_roundtrips (Γ := Γ) m p
  have den := roundtrip_denominators (Γ := Γ) m p
  exact .andI (evaluate_rescaling c p _ _ hc hp hq1 native.andE₁ native.andE₂.andE₁ den.andE₁)
    (evaluate_rescaling c p _ _ hc hp hq2 native.andE₂.andE₂.andE₁ native.andE₂.andE₂.andE₂ den.andE₂)

theorem inverse_evaluation (c m p : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] source m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    AnalyticConicRationalAffine.evaluate (AnalyticConicRationalAffine.pullback c m) (image (inverse m) p) ≐ AnalyticConicRationalAffine.evaluate c p :=
  (AnalyticConicRationalAffine.rational_evaluation_covariance c m (image (inverse m) p) hc hm.andE₁
    (image_valid (inverse m) p (inverse_valid m hm) hp)).eqTrans (evaluation_roundtrips c m p hc hm hp).andE₂

theorem inverse_pullback_evaluation (c m p : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] source m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    AnalyticConicRationalAffine.evaluate
      (AnalyticConicRationalAffine.pullback (AnalyticConicRationalAffine.pullback c m) (inverse m)) p ≐
      AnalyticConicRationalAffine.evaluate c p :=
  (AnalyticConicRationalAffine.rational_evaluation_covariance (AnalyticConicRationalAffine.pullback c m) (inverse m) p
    (AnalyticConicRationalAffine.pullback_valid c m hc hm.andE₁) (inverse_valid m hm) hp).eqTrans (inverse_evaluation c m p hc hm hp)

def inverseF : PR 1 := PTm.toPR (inverse (var 0))
def pointF : PR 1 := PTm.toPR (canonicalPoint (var 0))
theorem inverse_at (m : PTm n) : Γ ⊢[PRAAx] ap1 inverseF m ≐ inverse m := by
  simpa only [ap1,inverseF,subst_inverse,Syn.subst_var,Matrix.cons_val_zero,Matrix.head_cons] using
    toPR_eq (Γ := Γ) (inverse (var 0) : PTm 1) ![m]
theorem point_at (p : PTm n) : Γ ⊢[PRAAx] ap1 pointF p ≐ canonicalPoint p := by
  simpa only [ap1,pointF,subst_canonicalPoint,Syn.subst_var,Matrix.cons_val_zero,Matrix.head_cons] using
    toPR_eq (Γ := Γ) (canonicalPoint (var 0) : PTm 1) ![p]

theorem actual_inverse_guard (m : PTm n) (h : Γ ⊢[PRAAx] source m) : Γ ⊢[PRAAx] valid (ap1 inverseF m) :=
  le_congr (.eqRefl _) (congrSnd (inverse_at m)).eqSymm (inverse_valid m h)

theorem actual_coordinate_roundtrips (m p : PTm n) (hm : Γ ⊢[PRAAx] source m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    (ap1 pointF (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF m) (ap2 AnalyticConicRationalAffine.imageF m p)) ≐ ap1 pointF p) ⋏
      (ap1 pointF (ap2 AnalyticConicRationalAffine.imageF m (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF m) p)) ≐ ap1 pointF p) := by
  have first : Γ ⊢[PRAAx] ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF m) (ap2 AnalyticConicRationalAffine.imageF m p) ≐
      image (inverse m) (image m p) :=
    (congrAp2 AnalyticConicRationalAffine.imageF (inverse_at m) (AnalyticConicRationalAffine.image_at m p)).eqTrans
      (AnalyticConicRationalAffine.image_at _ _)
  have second : Γ ⊢[PRAAx] ap2 AnalyticConicRationalAffine.imageF m (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF m) p) ≐
      image m (image (inverse m) p) :=
    (congrAp2 AnalyticConicRationalAffine.imageF (.eqRefl m)
      ((congrAp2 AnalyticConicRationalAffine.imageF (inverse_at m) (.eqRefl p)).eqTrans (AnalyticConicRationalAffine.image_at _ _))).eqTrans
      (AnalyticConicRationalAffine.image_at _ _)
  have round := canonical_roundtrips m p hm hp
  exact .andI ((congrAp1 pointF first).eqTrans ((point_at _).eqTrans (round.andE₁.eqTrans (point_at p).eqSymm)))
    ((congrAp1 pointF second).eqTrans ((point_at _).eqTrans (round.andE₂.eqTrans (point_at p).eqSymm)))

theorem actual_inverse_evaluation (c m p : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] source m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    ap2 AnalyticConicRationalAffine.evaluateF (ap2 AnalyticConicRationalAffine.pullbackF c m)
      (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF m) p) ≐ ap2 AnalyticConicRationalAffine.evaluateF c p := by
  have arg : Γ ⊢[PRAAx] ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF m) p ≐ image (inverse m) p :=
    (congrAp2 AnalyticConicRationalAffine.imageF (inverse_at m) (.eqRefl p)).eqTrans (AnalyticConicRationalAffine.image_at _ _)
  exact (congrAp2 AnalyticConicRationalAffine.evaluateF (AnalyticConicRationalAffine.pullback_at c m) arg).eqTrans
    ((AnalyticConicRationalAffine.evaluate_at _ _).eqTrans
      ((inverse_evaluation c m p hc hm hp).eqTrans (AnalyticConicRationalAffine.evaluate_at c p).eqSymm))

theorem actual_inverse_zero_locus (c m p a : PTm n) (hc : Γ ⊢[PRAAx] valid c)
    (hm : Γ ⊢[PRAAx] source m) (hp : Γ ⊢[PRAAx] valid p) : Γ ⊢[PRAAx]
    Fm.iff (ap2 AnalyticConicRationalAffine.evaluateF (ap2 AnalyticConicRationalAffine.pullbackF c m)
      (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF m) p) ≐ a)
      (ap2 AnalyticConicRationalAffine.evaluateF c p ≐ a) := by
  have eq := actual_inverse_evaluation c m p hc hm hp
  exact .iffI (.impI (eq.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (eq.wk.eqTrans Prf.hyp0))

theorem actual_rational_affine_inverse_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (source (var 0) ⟶ valid (ap1 inverseF (var 0))) := closeUniv 1 (.impI (actual_inverse_guard _ Prf.hyp0))
theorem actual_rational_affine_coordinate_roundtrips_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((source (var 0) ⋏ valid (var 1)) ⟶
      ((ap1 pointF (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF (var 0)) (ap2 AnalyticConicRationalAffine.imageF (var 0) (var 1))) ≐ ap1 pointF (var 1)) ⋏
        (ap1 pointF (ap2 AnalyticConicRationalAffine.imageF (var 0) (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF (var 0)) (var 1))) ≐ ap1 pointF (var 1)))) :=
  closeUniv 2 (.impI (actual_coordinate_roundtrips _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_rational_conic_inverse_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((valid (var 0) ⋏ (source (var 1) ⋏ valid (var 2))) ⟶
      ap2 AnalyticConicRationalAffine.evaluateF (ap2 AnalyticConicRationalAffine.pullbackF (var 0) (var 1))
        (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF (var 1)) (var 2)) ≐ ap2 AnalyticConicRationalAffine.evaluateF (var 0) (var 2)) :=
  closeUniv 3 (.impI (actual_inverse_evaluation _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_rational_conic_inverse_zero_locus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((valid (var 0) ⋏ (source (var 1) ⋏ valid (var 2))) ⟶
      Fm.iff (ap2 AnalyticConicRationalAffine.evaluateF (ap2 AnalyticConicRationalAffine.pullbackF (var 0) (var 1))
        (ap2 AnalyticConicRationalAffine.imageF (ap1 inverseF (var 1)) (var 2)) ≐ var 3)
        (ap2 AnalyticConicRationalAffine.evaluateF (var 0) (var 2) ≐ var 3)) :=
  closeUniv 4 (.impI (actual_inverse_zero_locus _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Geometry.Distinct.AnalyticConicRationalInverse
