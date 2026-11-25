import IPRADerivations.Analysis.GaussianRationalGridRounding
import IPRADerivations.Analysis.GaussianRationalDirectionNormalizer
import IPRADerivations.Foundations.MasterCertificate
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination

/-!
# Actual signed square grids and nearest Gaussian points

All radii, mesh denominators and original raw Gaussian points are numerical
inputs. Original disk bounds derive the two coordinate boxes needed by the
actual nearest quotient. The grid is an actual stored sequence; its cover
witness is a computed index, not a supplied point or rounding law.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSquareGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalL1 (rawDen rawGaussian raw_represents raw_den_positive)
open GaussianRationalHorner (ofGaussian represents represents_congr represents_rescale positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open ComplexLogarithmRemainder (code re im scale normSq)
open GaussianRootAlgebra (sub re_sub im_sub re_scale im_scale)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq zabs_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def side (R M : PTm n) : PTm n := succ (two*R*M)
def nativePoint (R M i j : PTm n) : PTm n :=
  code (ZT.ofNat i-ZT.ofNat (R*M)) (ZT.ofNat j-ZT.ofNat (R*M))
def point (R M i j : PTm n) : PTm n := ofGaussian (nativePoint R M i j) M
def data (R M : PTm n) : PTm n := pairT R M
def gridBody : PTm 2 := point (fstT (var 1)) (sndT (var 1))
  (quo (var 0) (side (fstT (var 1)) (sndT (var 1))))
  (rem (var 0) (side (fstT (var 1)) (sndT (var 1))))
def grid (R M : PTm n) : PTm n := sequence gridBody (side R M*side R M) (data R M)
def nearestX (R M z : PTm n) : PTm n := GaussianRationalGridRounding.index
  (re (rawGaussian z)).pos (re (rawGaussian z)).neg (rawDen z) R M
def nearestY (R M z : PTm n) : PTm n := GaussianRationalGridRounding.index
  (im (rawGaussian z)).pos (im (rawGaussian z)).neg (rawDen z) R M
def nearest (R M z : PTm n) : PTm n := point R M (nearestX R M z) (nearestY R M z)
def nearestIndex (R M z : PTm n) : PTm n := nearestX R M z*side R M+nearestY R M z

def nativeError (R M z : PTm n) : PTm n := sub (scale M (rawGaussian z))
  (scale (rawDen z) (nativePoint R M (nearestX R M z) (nearestY R M z)))
@[simp] theorem subst_side {l : ℕ} (σ : Fin n → PTm l) (R M : PTm n) :
    Syn.subst σ (side R M) = side (Syn.subst σ R) (Syn.subst σ M) := by simp [side]
@[simp] theorem subst_nativePoint {l : ℕ} (σ : Fin n → PTm l) (R M i j : PTm n) :
    Syn.subst σ (nativePoint R M i j) = nativePoint (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ i) (Syn.subst σ j) := by simp [nativePoint]
@[simp] theorem subst_point {l : ℕ} (σ : Fin n → PTm l) (R M i j : PTm n) :
    Syn.subst σ (point R M i j) = point (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ i) (Syn.subst σ j) := by simp [point]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (R M : PTm n) :
    Syn.subst σ (data R M) = data (Syn.subst σ R) (Syn.subst σ M) := by simp [data]
@[simp] theorem subst_grid {l : ℕ} (σ : Fin n → PTm l) (R M : PTm n) :
    Syn.subst σ (grid R M) = grid (Syn.subst σ R) (Syn.subst σ M) := by simp [grid]
@[simp] theorem subst_nearestX {l : ℕ} (σ : Fin n → PTm l) (R M z : PTm n) :
    Syn.subst σ (nearestX R M z) = nearestX (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ z) := by
  simp only [nearestX,GaussianRationalGridRounding.subst_index,GaussianRationalL1.subst_rawDen]
  change GaussianRationalGridRounding.index ((re (rawGaussian z)).subst σ).pos ((re (rawGaussian z)).subst σ).neg
    (rawDen (Syn.subst σ z)) (Syn.subst σ R) (Syn.subst σ M) = _
  simp
@[simp] theorem subst_nearestY {l : ℕ} (σ : Fin n → PTm l) (R M z : PTm n) :
    Syn.subst σ (nearestY R M z) = nearestY (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ z) := by
  simp only [nearestY,GaussianRationalGridRounding.subst_index,GaussianRationalL1.subst_rawDen]
  change GaussianRationalGridRounding.index ((im (rawGaussian z)).subst σ).pos ((im (rawGaussian z)).subst σ).neg
    (rawDen (Syn.subst σ z)) (Syn.subst σ R) (Syn.subst σ M) = _
  simp
@[simp] theorem subst_nearest {l : ℕ} (σ : Fin n → PTm l) (R M z : PTm n) :
    Syn.subst σ (nearest R M z) = nearest (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ z) := by simp [nearest]
@[simp] theorem subst_nearestIndex {l : ℕ} (σ : Fin n → PTm l) (R M z : PTm n) :
    Syn.subst σ (nearestIndex R M z) = nearestIndex (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ z) := by simp [nearestIndex]
@[simp] theorem subst_nativeError {l : ℕ} (σ : Fin n → PTm l) (R M z : PTm n) :
    Syn.subst σ (nativeError R M z) = nativeError (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ z) := by simp [nativeError]

theorem side_positive (R M : PTm n) : Γ ⊢[PRAAx] le one (side R M) := zero_lt_succ _
theorem point_canonical (R M i j : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (point R M i j) := GaussianRationalHorner.ofGaussian_canonical _ _ hM
theorem point_represents (R M i j : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    represents (point R M i j) (nativePoint R M i j) M := GaussianRationalHorner.ofGaussian_represents _ _ hM

theorem original_norm_bound (R z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    le (normSq (rawGaussian z)) ((R*rawDen z)*(R*rawDen z)) :=
  le_congr (by ipra_ring) (by ipra_ring) (GaussianRationalMetric.bounded_to_cleared z _ _ R one
    (raw_den_positive z) (le_refl one) (raw_represents z) h)

theorem original_coordinates (R z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    le (zabs (re (rawGaussian z))) (R*rawDen z) ⋏ le (zabs (im (rawGaussian z))) (R*rawDen z) := by
  have norm := GaussianRationalDirectionNormalizer.norm_absolute (Γ := Γ) z
  have original := original_norm_bound R z h
  have left := le_congr (.eqRefl _) norm.eqSymm (le_add_right
    (zabs (re (rawGaussian z))*zabs (re (rawGaussian z))) (zabs (im (rawGaussian z))*zabs (im (rawGaussian z))))
  have right := le_congr (.eqRefl _) norm.eqSymm (le_add_left
    (zabs (im (rawGaussian z))*zabs (im (rawGaussian z))) (zabs (re (rawGaussian z))*zabs (re (rawGaussian z))))
  exact .andI (nat_sqrt_mono (le_trans left original)) (nat_sqrt_mono (le_trans right original))

theorem parts_absolute (a : ZT n) : Γ ⊢[PRAAx] zabs (ZT.ofNat a.pos-ZT.ofNat a.neg) ≐ zabs a := by
  apply zabs_congr
  simp only [ZT.toZ_sub,ZT.toZ_ofNat] <;> rfl

theorem original_boxes (R z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    GaussianRationalGridRounding.box (re (rawGaussian z)).pos (re (rawGaussian z)).neg (rawDen z) R ⋏
      GaussianRationalGridRounding.box (im (rawGaussian z)).pos (im (rawGaussian z)).neg (rawDen z) R := by
  have coord := original_coordinates R z h
  exact .andI (GaussianRationalGridRounding.box_of_absolute _ _ _ _
    (le_congr (parts_absolute _).eqSymm (.eqRefl _) (.andE₁ coord)))
    (GaussianRationalGridRounding.box_of_absolute _ _ _ _
      (le_congr (parts_absolute _).eqSymm (.eqRefl _) (.andE₂ coord)))

theorem nearest_coordinates (R M z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    le (nearestX R M z) (two*R*M) ⋏ le (nearestY R M z) (two*R*M) := by
  have boxes := original_boxes R z h
  exact .andI (GaussianRationalGridRounding.index_bound _ _ _ _ _ (raw_den_positive z) (.andE₁ boxes))
    (GaussianRationalGridRounding.index_bound _ _ _ _ _ (raw_den_positive z) (.andE₂ boxes))

theorem native_error_norm (R M z : PTm n) : Γ ⊢[PRAAx]
    normSq (nativeError R M z) ≐
      zabs (GaussianRationalGridRounding.error (re (rawGaussian z)).pos (re (rawGaussian z)).neg (rawDen z) R M)*
        zabs (GaussianRationalGridRounding.error (re (rawGaussian z)).pos (re (rawGaussian z)).neg (rawDen z) R M)+
      zabs (GaussianRationalGridRounding.error (im (rawGaussian z)).pos (im (rawGaussian z)).neg (rawDen z) R M)*
        zabs (GaussianRationalGridRounding.error (im (rawGaussian z)).pos (im (rawGaussian z)).neg (rawDen z) R M) := by
  have rx := zabs_sq (Γ := Γ) (GaussianRationalGridRounding.error (re (rawGaussian z)).pos (re (rawGaussian z)).neg (rawDen z) R M)
  have ry := zabs_sq (Γ := Γ) (GaussianRationalGridRounding.error (im (rawGaussian z)).pos (im (rawGaussian z)).neg (rawDen z) R M)
  apply deriveNat
  simp only [ComplexLogarithmRemainder.normSq_eval,nativeError,re_sub,im_sub,re_scale,im_scale,nativePoint,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
    GaussianRationalGridRounding.error,GaussianRationalGridRounding.coordinate] at rx ry ⊢
  ipra_simps
  rw [rx,ry]
  simp only [nearestX,nearestY,ZT.toZ] at * <;> ring

theorem native_error_bound (R M z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    le (normSq (nativeError R M z)) (rawDen z*rawDen z) := by
  have boxes := original_boxes R z h
  have x := GaussianRationalGridRounding.error_square _ _ _ R M (raw_den_positive z) (.andE₁ boxes)
  have y := GaussianRationalGridRounding.error_square _ _ _ R M (raw_den_positive z) (.andE₂ boxes)
  let X := zabs (GaussianRationalGridRounding.error (re (rawGaussian z)).pos (re (rawGaussian z)).neg (rawDen z) R M)
  let Y := zabs (GaussianRationalGridRounding.error (im (rawGaussian z)).pos (im (rawGaussian z)).neg (rawDen z) R M)
  apply RationalValueBounds.positive_cancel (le_succ_self one)
  apply le_of_eq_add (d := monus (rawDen z*rawDen z) ((two*two)*(X*X))+
    monus (rawDen z*rawDen z) ((two*two)*(Y*Y))+two*normSq (nativeError R M z))
  ipra_lc [X, Y] natEq (eq_add_of_le x)+natEq (eq_add_of_le y)-4*natEq (native_error_norm (Γ := Γ) R M z)

theorem nearest_difference_represents (R M z : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    represents (GaussianRationalMetric.qsub z (nearest R M z)) (nativeError R M z) (rawDen z*M) := by
  have source := represents_rescale z (rawGaussian z) (rawDen z) M (raw_represents (Γ := Γ) z)
  have target := represents_rescale (nearest R M z) (nativePoint R M (nearestX R M z) (nearestY R M z)) M
    (rawDen z) (point_represents (Γ := Γ) R M _ _ hM)
  exact GaussianRationalMetric.qsub_represents _ _ _ _ _ (positive_product _ _ (raw_den_positive z) hM) source
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _) target)

theorem nearest_distance (R M z : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx] distanceBounded z (nearest R M z) one M := by
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (positive_product _ _ (raw_den_positive z) hM)
    hM (nearest_difference_represents R M z hM)
  exact le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right (M*M) (native_error_bound R M z h))

theorem side_congr {R S M K : PTm n} (hR : Γ ⊢[PRAAx] R ≐ S) (hM : Γ ⊢[PRAAx] M ≐ K) : Γ ⊢[PRAAx]
    side R M ≐ side S K := congrSucc (congrMul (congrMul (.eqRefl two) hR) hM)
theorem point_congr {R S M K i u j v : PTm n} (hR : Γ ⊢[PRAAx] R ≐ S) (hM : Γ ⊢[PRAAx] M ≐ K)
    (hi : Γ ⊢[PRAAx] i ≐ u) (hj : Γ ⊢[PRAAx] j ≐ v) : Γ ⊢[PRAAx] point R M i j ≐ point S K u v := by
  ipra_congr (point (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hR, hM, hi, hj]

theorem grid_length (R M : PTm n) : Γ ⊢[PRAAx] length (grid R M) ≐ side R M*side R M := sequence_length _ _ _
theorem grid_body_at (R M r : PTm n) : Γ ⊢[PRAAx]
    inst2 gridBody r (data R M) ≐ point R M (quo r (side R M)) (rem r (side R M)) := by
  simp only [gridBody,inst2,subst_point,subst_fstT,subst_sndT,subst_ap2,subst_side,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact point_congr (fst_pair _ _) (snd_pair _ _)
    (congrAp2 quoF (.eqRefl _) (side_congr (fst_pair _ _) (snd_pair _ _)))
    (congrAp2 remF (.eqRefl _) (side_congr (fst_pair _ _) (snd_pair _ _)))
theorem grid_lookup (R M r : PTm n) (hr : Γ ⊢[PRAAx] lt r (side R M*side R M)) : Γ ⊢[PRAAx]
    entry (grid R M) r ≐ point R M (quo r (side R M)) (rem r (side R M)) :=
  (sequence_decode gridBody hr).eqTrans (grid_body_at R M r)
theorem grid_indices (R M r : PTm n) (hr : Γ ⊢[PRAAx] lt r (side R M*side R M)) : Γ ⊢[PRAAx]
    lt (quo r (side R M)) (side R M) ⋏ lt (rem r (side R M)) (side R M) :=
  .andI (LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative.quo_lt
    (RationalIntegerNormalization.positive_form (side_positive R M)) hr)
    (LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative.rem_lt'
      (RationalIntegerNormalization.positive_form (side_positive R M)) r)

def pointIndex (R M i j : PTm n) : PTm n := i*side R M+j
@[simp] theorem subst_pointIndex {l : ℕ} (σ : Fin n → PTm l) (R M i j : PTm n) :
    Syn.subst σ (pointIndex R M i j) = pointIndex (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ i) (Syn.subst σ j) := by simp [pointIndex]
theorem point_index_range (R M i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (side R M)) (hj : Γ ⊢[PRAAx] lt j (side R M)) : Γ ⊢[PRAAx]
    lt (pointIndex R M i j) (side R M*side R M) := by
  have first : Γ ⊢[PRAAx] le (succ (pointIndex R M i j)) (succ i*side R M) :=
    le_congr (by unfold pointIndex; ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (i*side R M)) hj)
  exact le_trans first (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hi (le_refl _))
theorem point_index_decode (R M i j : PTm n) (hj : Γ ⊢[PRAAx] lt j (side R M)) : Γ ⊢[PRAAx]
    (quo (pointIndex R M i j) (side R M) ≐ i) ⋏ (rem (pointIndex R M i j) (side R M) ≐ j) := by
  have positive := RationalIntegerNormalization.positive_form (side_positive (Γ := Γ) R M)
  have eq : Γ ⊢[PRAAx] pointIndex R M i j ≐ succ (PTm.pred (side R M))*i+j :=
    (by unfold pointIndex; ipra_ring : Γ ⊢[PRAAx] pointIndex R M i j ≐ side R M*i+j).eqTrans
      (congrAdd (congrMul positive (.eqRefl _)) (.eqRefl _))
  have actual := div_mod_unique eq (lt_congr (.eqRefl _) positive hj)
  exact .andI ((congrAp2 quoF (.eqRefl _) positive).eqTrans (.andE₁ actual))
    ((congrAp2 remF (.eqRefl _) positive).eqTrans (.andE₂ actual))
theorem point_listed (R M i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (side R M)) (hj : Γ ⊢[PRAAx] lt j (side R M)) : Γ ⊢[PRAAx]
    entry (grid R M) (pointIndex R M i j) ≐ point R M i j :=
  (grid_lookup R M _ (point_index_range R M i j hi hj)).eqTrans
    (point_congr (.eqRefl _) (.eqRefl _) (.andE₁ (point_index_decode R M i j hj)) (.andE₂ (point_index_decode R M i j hj)))

theorem coordinate_square (i K : PTm n) (hi : Γ ⊢[PRAAx] le i (two*K)) : Γ ⊢[PRAAx]
    le (zabs (ZT.ofNat i-ZT.ofNat K)*zabs (ZT.ofNat i-ZT.ofNat K)) (K*K) := by
  have square := zabs_sq (Γ := Γ) (ZT.ofNat i-ZT.ofNat K)
  have bound := natEq (eq_add_of_le hi)
  apply le_of_eq_add (d := i*monus (two*K) i)
  apply deriveNat
  ipra_simps
  rw [square]
  linear_combination 𝔞(i)*bound
theorem native_point_norm (R M i j : PTm n) : Γ ⊢[PRAAx]
    normSq (nativePoint R M i j) ≐
      zabs (ZT.ofNat i-ZT.ofNat (R*M))*zabs (ZT.ofNat i-ZT.ofNat (R*M))+
        zabs (ZT.ofNat j-ZT.ofNat (R*M))*zabs (ZT.ofNat j-ZT.ofNat (R*M)) := by
  have rx := zabs_sq (Γ := Γ) (ZT.ofNat i-ZT.ofNat (R*M))
  have ry := zabs_sq (Γ := Γ) (ZT.ofNat j-ZT.ofNat (R*M))
  apply deriveNat
  simp only [ComplexLogarithmRemainder.normSq_eval,nativePoint,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code]
  ipra_simps
  rw [rx,ry]
  ring

theorem point_bounded (R M i j : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] lt i (side R M)) (hj : Γ ⊢[PRAAx] lt j (side R M)) : Γ ⊢[PRAAx] bounded (point R M i j) (two*R) one := by
  have ix : Γ ⊢[PRAAx] le i (two*(R*M)) := le_congr (.eqRefl _) (by ipra_ring)
    ((succ_monus_succ i (two*R*M)).eqSymm.eqTrans hi)
  have iy : Γ ⊢[PRAAx] le j (two*(R*M)) := le_congr (.eqRefl _) (by ipra_ring)
    ((succ_monus_succ j (two*R*M)).eqSymm.eqTrans hj)
  have norm : Γ ⊢[PRAAx] le (normSq (nativePoint R M i j)) ((R*M)*(R*M)+(R*M)*(R*M)) :=
    le_congr (native_point_norm R M i j).eqSymm (.eqRefl _) (add_le_add₂ (coordinate_square i _ ix) (coordinate_square j _ iy))
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hM (le_refl one) (point_represents R M i j hM)
  exact le_congr (by ipra_ring) (.eqRefl _)
    (le_trans norm (le_of_eq_add (d := two*(R*M)*(R*M)) (by ipra_ring)))

theorem nearest_index_bound (R M z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    lt (nearestIndex R M z) (length (grid R M)) := by
  have bounds := nearest_coordinates R M z h
  exact lt_congr (.eqRefl _) (grid_length R M).eqSymm
    (point_index_range R M _ _ ((succ_monus_succ _ _).eqTrans (.andE₁ bounds)) ((succ_monus_succ _ _).eqTrans (.andE₂ bounds)))
theorem nearest_lookup (R M z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    entry (grid R M) (nearestIndex R M z) ≐ nearest R M z := by
  have bounds := nearest_coordinates R M z h
  exact point_listed R M _ _ ((succ_monus_succ _ _).eqTrans (.andE₁ bounds)) ((succ_monus_succ _ _).eqTrans (.andE₂ bounds))
theorem covering (R M z : PTm n) (hM : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    lt (nearestIndex R M z) (length (grid R M)) ⋏
      distanceBounded z (entry (grid R M) (nearestIndex R M z)) one M :=
  .andI (nearest_index_bound R M z h) (GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (nearest_lookup R M z h).eqSymm
    (.eqRefl _) (.eqRefl _) (nearest_distance R M z hM h))

theorem grid_nonempty (R M : PTm n) : Γ ⊢[PRAAx] le one (length (grid R M)) :=
  le_congr (.eqRefl _) (grid_length R M).eqSymm (positive_product _ _ (side_positive R M) (side_positive R M))
theorem grid_entry_canonical (R M r : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hr : Γ ⊢[PRAAx] lt r (length (grid R M))) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (entry (grid R M) r) :=
  GaussianRationalHorner.canonical_congr (grid_lookup R M r (lt_congr (.eqRefl _) (grid_length R M) hr))
    (point_canonical _ _ _ _ hM)
theorem grid_entry_bound (R M r : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hr : Γ ⊢[PRAAx] lt r (length (grid R M))) : Γ ⊢[PRAAx] bounded (entry (grid R M) r) (two*R) one := by
  have range := lt_congr (.eqRefl _) (grid_length R M) hr
  have indices := grid_indices R M r range
  exact GaussianRationalReciprocal.bound_congr (grid_lookup R M r range).eqSymm (.eqRefl _) (.eqRefl _)
    (point_bounded R M _ _ hM (.andE₁ indices) (.andE₂ indices))
theorem nearest_canonical (R M z : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (nearest R M z) := point_canonical _ _ _ _ hM
theorem nearest_bound (R M z : PTm n) (hM : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    bounded (nearest R M z) (two*R) one :=
  GaussianRationalReciprocal.bound_congr (nearest_lookup R M z h) (.eqRefl _) (.eqRefl _)
    (grid_entry_bound R M _ hM (nearest_index_bound R M z h))

def output (R M z : PTm n) : PTm n := pairT (grid R M) (pairT (nearestIndex R M z) (pairT (nearest R M z) (side R M)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (R M z : PTm n) : PTm n := ap3 outputF R M z
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (R M z : PTm n) :
    Syn.subst σ (output R M z) = output (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (R M z : PTm n) :
    Syn.subst σ (run R M z) = run (Syn.subst σ R) (Syn.subst σ M) (Syn.subst σ z) := by simp [run]
theorem program_at (R M z : PTm n) : Γ ⊢[PRAAx] run R M z ≐ output R M z := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![R,M,z]
theorem returned_grid (R M z : PTm n) : Γ ⊢[PRAAx] fstT (run R M z) ≐ grid R M :=
  (congrFst (program_at R M z)).eqTrans (fst_pair _ _)
theorem returned_index (R M z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run R M z)) ≐ nearestIndex R M z :=
  (congrFst (congrSnd (program_at R M z))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
theorem returned_point (R M z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run R M z))) ≐ nearest R M z := by
  have t1 := (congrSnd (program_at (Γ := Γ) R M z)).eqTrans (snd_pair _ _)
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  exact (congrFst t2).eqTrans (fst_pair _ _)
theorem returned_side (R M z : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run R M z))) ≐ side R M := by
  have t1 := (congrSnd (program_at (Γ := Γ) R M z)).eqTrans (snd_pair _ _)
  have t2 := (congrSnd t1).eqTrans (snd_pair _ _)
  exact (congrSnd t2).eqTrans (snd_pair _ _)
theorem returned_cover (R M z : PTm n) (hM : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    lt (fstT (sndT (run R M z))) (length (fstT (run R M z))) ⋏
      distanceBounded z (fstT (sndT (sndT (run R M z)))) one M :=
  .andI (lt_congr (returned_index R M z).eqSymm (congrFst (returned_grid R M z)).eqSymm (nearest_index_bound R M z h))
    (GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (returned_point R M z).eqSymm
      (.eqRefl _) (.eqRefl _) (nearest_distance R M z hM h))
theorem returned_lookup (R M z : PTm n) (h : Γ ⊢[PRAAx] bounded z R one) : Γ ⊢[PRAAx]
    entry (fstT (run R M z)) (fstT (sndT (run R M z))) ≐ fstT (sndT (sndT (run R M z))) :=
  (entry_congr (returned_grid R M z) (returned_index R M z)).eqTrans ((nearest_lookup R M z h).eqTrans (returned_point R M z).eqSymm)

theorem actual_square_grid_geometry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (grid (var 0) (var 1)) ≐ side (var 0) (var 1)*side (var 0) (var 1)) ⋏ le one (length (grid (var 0) (var 1)))) :=
  closeUniv 2 (.andI (grid_length _ _) (grid_nonempty _ _))
theorem actual_square_grid_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (side (var 0) (var 1)*side (var 0) (var 1)) ⟶ entry (grid (var 0) (var 1)) (var 2) ≐
      point (var 0) (var 1) (quo (var 2) (side (var 0) (var 1))) (rem (var 2) (side (var 0) (var 1)))) :=
  closeUniv 3 (.impI (grid_lookup _ _ _ Prf.hyp0))
theorem actual_original_disk_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ bounded (var 2) (var 0) one ⟶
      (lt (nearestIndex (var 0) (var 1) (var 2)) (length (grid (var 0) (var 1))) ⋏
        distanceBounded (var 2) (entry (grid (var 0) (var 1)) (nearestIndex (var 0) (var 1) (var 2))) one (var 1))) :=
  closeUniv 3 (.impI (.impI (covering _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_grid_entry_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ lt (var 2) (length (grid (var 0) (var 1))) ⟶
      (GaussianRationalHorner.canonical (entry (grid (var 0) (var 1)) (var 2)) ⋏
        bounded (entry (grid (var 0) (var 1)) (var 2)) (two*var 0) one)) :=
  closeUniv 3 (.impI (.impI (.andI (grid_entry_canonical _ _ _ Prf.hyp1 Prf.hyp0) (grid_entry_bound _ _ _ Prf.hyp1 Prf.hyp0))))
theorem actual_nearest_point_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ bounded (var 2) (var 0) one ⟶
      (GaussianRationalHorner.canonical (nearest (var 0) (var 1) (var 2)) ⋏ bounded (nearest (var 0) (var 1) (var 2)) (two*var 0) one)) :=
  closeUniv 3 (.impI (.impI (.andI (nearest_canonical _ _ _ Prf.hyp1) (nearest_bound _ _ _ Prf.hyp1 Prf.hyp0))))
theorem actual_square_grid_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_disk_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ bounded (var 2) (var 0) one ⟶
      (lt (fstT (sndT (run (var 0) (var 1) (var 2)))) (length (fstT (run (var 0) (var 1) (var 2)))) ⋏
        distanceBounded (var 2) (fstT (sndT (sndT (run (var 0) (var 1) (var 2))))) one (var 1))) :=
  closeUniv 3 (.impI (.impI (returned_cover _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_grid_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (bounded (var 2) (var 0) one ⟶ entry (fstT (run (var 0) (var 1) (var 2))) (fstT (sndT (run (var 0) (var 1) (var 2)))) ≐
      fstT (sndT (sndT (run (var 0) (var 1) (var 2))))) := closeUniv 3 (.impI (returned_lookup _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalSquareGrid
