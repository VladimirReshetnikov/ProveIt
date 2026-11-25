import IPRADerivations.Analysis.RationalAlgebra
import IPRADerivations.Analysis.RationalValueBounds
import IPRADerivations.Analysis.RationalPointDistance
import IPRADerivations.Analysis.RationalHausdorffConcat
import IPRADerivations.Foundations.RuntimeWordAppend
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination

/-!
# Actual dyadic cube grids in numerical dimension

The source finite-net infimum theorem uses all (2^t+1)^d dyadic points
of the rational unit cube. Both dimensions and precisions are numerical.
Coordinates read reversed little-endian places, giving a fixed lexicographic
order. The rounding word is the actual mixed-radix code of the computed
coordinate quotients. No host-dimensional tuple or grid law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalSupMetric (numeratorOf denominatorOf rationalCode)
open RationalIntegerNormalization (normalize positivePart)
open RationalArithmetic (represents)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (digit)
open LeanProofs.IPRA.Foundations.RuntimeWordAppend (divide_spec power_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def scale (t : PTm k) : PTm k := pw two t
def radix (t : PTm k) : PTm k := succ (scale t)
def count (d t : PTm k) : PTm k := pw (radix t) d
def reflected (d i : PTm k) : PTm k := monus d (succ i)
def fraction (j t : PTm k) : PTm k := normalize (ZT.ofNat j) (scale t)
def interval (q : PTm k) : Fm PTm k := le (numeratorOf q).neg (numeratorOf q).pos ⋏
  le (numeratorOf q).pos ((numeratorOf q).neg+denominatorOf q)
def cube (x d : PTm k) : Fm PTm k := length x ≐ d ⋏ .all (lt (var 0) (Syn.shift d) ⟶ interval (entry (Syn.shift x) (var 0)))
def pointData (d t w : PTm k) : PTm k := pairT d (pairT t w)
def coordinateBody : PTm 2 := fraction (digit (radix (fstT (sndT (var 1)))) (sndT (sndT (var 1)))
  (reflected (fstT (var 1)) (var 0))) (fstT (sndT (var 1)))
def point (d t w : PTm k) : PTm k := sequence coordinateBody d (pointData d t w)
def gridBody : PTm 2 := point (fstT (var 1)) (sndT (var 1)) (var 0)
def grid (d t : PTm k) : PTm k := sequence gridBody (count d t) (pairT d t)

@[simp] theorem subst_scale {l : ℕ} (σ : Fin k → PTm l) (t : PTm k) : Syn.subst σ (scale t) = scale (Syn.subst σ t) := by simp [scale]
@[simp] theorem subst_radix {l : ℕ} (σ : Fin k → PTm l) (t : PTm k) : Syn.subst σ (radix t) = radix (Syn.subst σ t) := by simp [radix]
@[simp] theorem subst_count {l : ℕ} (σ : Fin k → PTm l) (d t : PTm k) : Syn.subst σ (count d t) = count (Syn.subst σ d) (Syn.subst σ t) := by simp [count]
@[simp] theorem subst_reflected {l : ℕ} (σ : Fin k → PTm l) (d i : PTm k) : Syn.subst σ (reflected d i) = reflected (Syn.subst σ d) (Syn.subst σ i) := by simp [reflected]
@[simp] theorem subst_fraction {l : ℕ} (σ : Fin k → PTm l) (j t : PTm k) : Syn.subst σ (fraction j t) = fraction (Syn.subst σ j) (Syn.subst σ t) := by simp [fraction]
@[simp] theorem subst_interval {l : ℕ} (σ : Fin k → PTm l) (q : PTm k) :
    (interval q).subst σ = interval (Syn.subst σ q) := by simp [interval,numeratorOf]
@[simp] theorem subst_cube {l : ℕ} (σ : Fin k → PTm l) (x d : PTm k) :
    (cube x d).subst σ = cube (Syn.subst σ x) (Syn.subst σ d) := by simp [cube,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_pointData {l : ℕ} (σ : Fin k → PTm l) (d t w : PTm k) : Syn.subst σ (pointData d t w) = pointData (Syn.subst σ d) (Syn.subst σ t) (Syn.subst σ w) := by simp [pointData]
@[simp] theorem subst_point {l : ℕ} (σ : Fin k → PTm l) (d t w : PTm k) : Syn.subst σ (point d t w) = point (Syn.subst σ d) (Syn.subst σ t) (Syn.subst σ w) := by simp [point]
@[simp] theorem subst_grid {l : ℕ} (σ : Fin k → PTm l) (d t : PTm k) : Syn.subst σ (grid d t) = grid (Syn.subst σ d) (Syn.subst σ t) := by simp [grid]

theorem scale_positive (t : PTm k) : Γ ⊢[PRAAx] le one (scale t) := power_positive two t (le_succ_self one)
theorem count_positive (d t : PTm k) : Γ ⊢[PRAAx] le one (count d t) := power_positive (radix t) d (zero_lt_succ _)
theorem count_zero (t : PTm k) : Γ ⊢[PRAAx] count zero t ≐ one := pw_zero _
theorem reflected_balance (d i : PTm k) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx] succ i+reflected d i ≐ d := (eq_add_of_le hi).eqSymm
theorem reflected_bound (d i : PTm k) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx] lt (reflected d i) d := by
  apply le_of_eq_add (d := i)
  ipra_lc -natEq (reflected_balance d i hi)

theorem reflected_twice (d i : PTm k) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx] reflected d (reflected d i) ≐ i := by
  have e : Γ ⊢[PRAAx] d ≐ succ (reflected d i)+i := (reflected_balance d i hi).eqSymm.eqTrans (by ipra_ring)
  exact (congrMonus e (.eqRefl _)).eqTrans (add_monus' i (succ (reflected d i)))

theorem point_data_at (d t w : PTm k) : Γ ⊢[PRAAx]
    fstT (pointData d t w) ≐ d ⋏ (fstT (sndT (pointData d t w)) ≐ t ⋏ sndT (sndT (pointData d t w)) ≐ w) :=
  .andI (fst_pair _ _) (.andI ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
theorem coordinate_body_at (d t w i : PTm k) : Γ ⊢[PRAAx]
    inst2 coordinateBody i (pointData d t w) ≐ fraction (digit (radix t) w (reflected d i)) t := by
  have e := point_data_at (Γ := Γ) d t w
  simp only [coordinateBody,inst2,subst_fraction,Foundations.RuntimePermutationWords.subst_digit,subst_radix,
    subst_reflected,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (fraction (digit (radix (var 1)) (var 2) (reflected (var 0) (var 3))) (var 1) : PTm 4) with
    [.andE₁ e, .andE₁ (.andE₂ e), .andE₂ (.andE₂ e), .eqRefl i]
theorem point_length (d t w : PTm k) : Γ ⊢[PRAAx] length (point d t w) ≐ d := sequence_length _ _ _
theorem point_lookup (d t w i : PTm k) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    entry (point d t w) i ≐ fraction (digit (radix t) w (reflected d i)) t :=
  (sequence_decode coordinateBody hi).eqTrans (coordinate_body_at _ _ _ _)
theorem grid_body_at (d t w : PTm k) : Γ ⊢[PRAAx] inst2 gridBody w (pairT d t) ≐ point d t w := by
  simp only [gridBody,inst2,subst_point,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (point (var 0) (var 1) (var 2) : PTm 3) with [fst_pair _ _, snd_pair _ _, .eqRefl w]
theorem grid_length (d t : PTm k) : Γ ⊢[PRAAx] length (grid d t) ≐ count d t := sequence_length _ _ _
theorem grid_lookup (d t w : PTm k) (hw : Γ ⊢[PRAAx] lt w (count d t)) : Γ ⊢[PRAAx] entry (grid d t) w ≐ point d t w :=
  (sequence_decode gridBody hw).eqTrans (grid_body_at _ _ _)

/-- The actual scalar coordinate quotient used by downward rounding. -/
def roundedDigit (q t : PTm k) : PTm k := quo (scale t*positivePart (numeratorOf q)) (denominatorOf q)
def roundedBody : PTm 2 := roundedDigit (entry (fstT (sndT (var 1))) (reflected (fstT (var 1)) (var 0))) (sndT (sndT (var 1)))
def roundedDigits (x d t : PTm k) : PTm k := sequence roundedBody d (pairT d (pairT x t))
def encode (P d b : PTm k) : PTm k := Foundations.MixedRadix.Cd Foundations.RuntimePermutationWords.radixBody
  Foundations.RuntimePermutationWords.vectorBody d (Foundations.RuntimePermutationWords.data b P)
def roundIndex (x d t : PTm k) : PTm k := encode (roundedDigits x d t) d (radix t)

@[simp] theorem subst_roundedDigit {l : ℕ} (σ : Fin k → PTm l) (q t : PTm k) :
    Syn.subst σ (roundedDigit q t) = roundedDigit (Syn.subst σ q) (Syn.subst σ t) := by simp [roundedDigit]
@[simp] theorem subst_roundedDigits {l : ℕ} (σ : Fin k → PTm l) (x d t : PTm k) :
    Syn.subst σ (roundedDigits x d t) = roundedDigits (Syn.subst σ x) (Syn.subst σ d) (Syn.subst σ t) := by simp [roundedDigits]
@[simp] theorem subst_encode {l : ℕ} (σ : Fin k → PTm l) (P d b : PTm k) :
    Syn.subst σ (encode P d b) = encode (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ b) := by simp [encode]
@[simp] theorem subst_roundIndex {l : ℕ} (σ : Fin k → PTm l) (x d t : PTm k) :
    Syn.subst σ (roundIndex x d t) = roundIndex (Syn.subst σ x) (Syn.subst σ d) (Syn.subst σ t) := by simp [roundIndex]

theorem cube_at (x d i : PTm k) (h : Γ ⊢[PRAAx] cube x d) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx] interval (entry x i) := by
  have rule : Γ ⊢[PRAAx] lt i d ⟶ interval (entry x i) := by simpa [cube] using (Prf.andE₂ h).allE i
  exact .impE rule hi
theorem positive_part_bound (q : PTm k) (h : Γ ⊢[PRAAx] interval q) : Γ ⊢[PRAAx] le (positivePart (numeratorOf q)) (denominatorOf q) := by
  apply le_of_eq_add (d := monus ((numeratorOf q).neg+denominatorOf q) (numeratorOf q).pos)
  ipra_lc [positivePart] natEq (eq_add_of_le (.andE₂ h))+natEq (eq_add_of_le (.andE₁ h))

theorem rounded_digit_bound (q t : PTm k) (h : Γ ⊢[PRAAx] interval q) : Γ ⊢[PRAAx] le (roundedDigit q t) (scale t) := by
  let D := denominatorOf q
  let P := positivePart (numeratorOf q)
  have div := divide_spec (Γ := Γ) D (scale t*P) (RationalArgmin.denominator_positive q)
  have first : Γ ⊢[PRAAx] le (D*roundedDigit q t) (scale t*P) := le_of_eq_add (.andE₁ div)
  have next : Γ ⊢[PRAAx] le (scale t*P) (scale t*D) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (scale t) (positive_part_bound q h))
  have bound := le_trans first next
  exact RationalValueBounds.positive_cancel (RationalArgmin.denominator_positive q) (le_congr (.eqRefl _) (mul_comm _ _) bound)

def digitsBelow (P d b : PTm k) : Fm PTm k := .all (lt (var 0) (Syn.shift d) ⟶ lt (entry (Syn.shift P) (var 0)) (Syn.shift b))
@[simp] theorem subst_digitsBelow {l : ℕ} (σ : Fin k → PTm l) (P d b : PTm k) :
    (digitsBelow P d b).subst σ = digitsBelow (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ b) := by
  simp [digitsBelow,Syn.subst_shift,Syn.shift_subst]
theorem digits_below_at (P d b i : PTm k) (h : Γ ⊢[PRAAx] digitsBelow P d b) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] lt (entry P i) b := by
  have rule : Γ ⊢[PRAAx] lt i d ⟶ lt (entry P i) b := by simpa [digitsBelow] using h.allE i
  exact .impE rule hi

theorem encode_bound (P d b : PTm k) (h : Γ ⊢[PRAAx] digitsBelow P d b) : Γ ⊢[PRAAx] lt (encode P d b) (pw b d) := by
  have all : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift d) ⟶
      lt (inst2 Foundations.RuntimePermutationWords.vectorBody (var 0) (Syn.shift (Foundations.RuntimePermutationWords.data b P)))
        (inst2 Foundations.RuntimePermutationWords.radixBody (var 0) (Syn.shift (Foundations.RuntimePermutationWords.data b P)))) := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] digitsBelow (Syn.shift P) (Syn.shift d) (Syn.shift b) := by
      simpa only [Fm.shift,subst_digitsBelow,Syn.shift] using h.shift
    simpa only [Syn.shift,Foundations.RuntimePermutationWords.subst_data] using
      lt_congr (Foundations.RuntimePermutationWords.vector_at _ _ _).eqSymm (Foundations.RuntimePermutationWords.radix_at _ _ _).eqSymm
        (digits_below_at _ _ _ _ hs.wk Prf.hyp0)
  exact lt_congr (.eqRefl _) (Foundations.RuntimePermutationWords.places b P d) (Foundations.MixedRadix.code_lt _ _ _ _ all)

theorem encode_digit (P d b i : PTm k) (h : Γ ⊢[PRAAx] digitsBelow P d b) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] digit b (encode P d b) i ≐ entry P i := by
  let t := reflected d i
  have span : Γ ⊢[PRAAx] succ i+t ≐ d := reflected_balance d i hi
  have all : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ i+t)) ⟶
      lt (inst2 Foundations.RuntimePermutationWords.vectorBody (var 0) (Syn.shift (Foundations.RuntimePermutationWords.data b P)))
        (inst2 Foundations.RuntimePermutationWords.radixBody (var 0) (Syn.shift (Foundations.RuntimePermutationWords.data b P)))) := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] digitsBelow (Syn.shift P) (Syn.shift d) (Syn.shift b) := by
      simpa only [Fm.shift,subst_digitsBelow,Syn.shift] using h.shift
    have ss : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (succ i+t) ≐ Syn.shift d := by
      simpa only [Fm.shift,Fm.subst_eq,Syn.shift,t] using span.shift
    simpa only [Syn.shift,Foundations.RuntimePermutationWords.subst_data] using
      lt_congr (Foundations.RuntimePermutationWords.vector_at _ _ _).eqSymm (Foundations.RuntimePermutationWords.radix_at _ _ _).eqSymm
        (digits_below_at _ _ _ _ hs.wk (lt_congr (.eqRefl _) ss.wk Prf.hyp0))
  have codeEq : Γ ⊢[PRAAx] Foundations.MixedRadix.Cd Foundations.RuntimePermutationWords.radixBody
      Foundations.RuntimePermutationWords.vectorBody (succ i+t) (Foundations.RuntimePermutationWords.data b P) ≐ encode P d b :=
    congrAp2 (sumF (Foundations.MixedRadix.dP Foundations.RuntimePermutationWords.radixBody Foundations.RuntimePermutationWords.vectorBody)) span (.eqRefl _)
  have e := Foundations.MixedRadix.decode all
  exact (congrAp2 remF (congrAp2 quoF codeEq (Foundations.RuntimePermutationWords.places b P i))
    (Foundations.RuntimePermutationWords.radix_at b P i)).eqSymm.eqTrans (e.eqTrans (Foundations.RuntimePermutationWords.vector_at _ _ _))

theorem rounded_body_at (x d t i : PTm k) : Γ ⊢[PRAAx] inst2 roundedBody i (pairT d (pairT x t)) ≐ roundedDigit (entry x (reflected d i)) t := by
  have e := point_data_at (Γ := Γ) d x t
  simp only [roundedBody,inst2,subst_roundedDigit,subst_reflected,subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (roundedDigit (entry (var 1) (reflected (var 0) (var 3))) (var 2) : PTm 4) with
    [.andE₁ e, .andE₁ (.andE₂ e), .andE₂ (.andE₂ e), .eqRefl i] using [pointData]
theorem rounded_digits_length (x d t : PTm k) : Γ ⊢[PRAAx] length (roundedDigits x d t) ≐ d := sequence_length _ _ _
theorem rounded_digits_lookup (x d t i : PTm k) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    entry (roundedDigits x d t) i ≐ roundedDigit (entry x (reflected d i)) t :=
  (sequence_decode roundedBody hi).eqTrans (rounded_body_at _ _ _ _)
theorem rounded_digits_below (x d t : PTm k) (h : Γ ⊢[PRAAx] cube x d) : Γ ⊢[PRAAx] digitsBelow (roundedDigits x d t) d (radix t) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] cube (Syn.shift x) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift d) := Prf.hyp0
  have valid := cube_at (Syn.shift x) (Syn.shift d) (reflected (Syn.shift d) (var 0)) hs.wk (reflected_bound _ _ hi)
  have top : Δ ⊢[PRAAx] lt (roundedDigit (entry (Syn.shift x) (reflected (Syn.shift d) (var 0))) (Syn.shift t)) (radix (Syn.shift t)) :=
    lt_of_le_of_lt (rounded_digit_bound _ _ valid) (le_refl _)
  simpa only [Δ,Syn.shift,subst_roundedDigits,subst_radix] using
    lt_congr (rounded_digits_lookup _ _ _ _ hi).eqSymm (.eqRefl _) top

theorem round_index_bound (x d t : PTm k) (h : Γ ⊢[PRAAx] cube x d) : Γ ⊢[PRAAx] lt (roundIndex x d t) (count d t) :=
  encode_bound _ _ _ (rounded_digits_below x d t h)
theorem rounded_digit_congr {q q' t t' : PTm k} (hq : Γ ⊢[PRAAx] q ≐ q') (ht : Γ ⊢[PRAAx] t ≐ t') :
    Γ ⊢[PRAAx] roundedDigit q t ≐ roundedDigit q' t' := by
  ipra_congr (roundedDigit (var 0) (var 1) : PTm 2) with [hq, ht]
theorem round_index_digit (x d t i : PTm k) (h : Γ ⊢[PRAAx] cube x d) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    digit (radix t) (roundIndex x d t) (reflected d i) ≐ roundedDigit (entry x i) t :=
  (encode_digit (roundedDigits x d t) d (radix t) (reflected d i) (rounded_digits_below x d t h) (reflected_bound d i hi)).eqTrans
    ((rounded_digits_lookup x d t (reflected d i) (reflected_bound d i hi)).eqTrans
      (rounded_digit_congr (entry_congr (.eqRefl _) (reflected_twice d i hi)) (.eqRefl _)))

theorem fraction_represents (j t : PTm k) : Γ ⊢[PRAAx] represents (fraction j t) (ZT.ofNat j) (scale t) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (scale_positive t)
theorem fraction_canonical (j t : PTm k) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (fraction j t) :=
  RationalNormalForm.normalize_well_formed _ _ (scale_positive t)
theorem fraction_negative_zero (j t : PTm k) : Γ ⊢[PRAAx] (numeratorOf (fraction j t)).neg ≐ zero := by
  have e := Prf.andE₂ (RationalNormalForm.code_parts (Γ := Γ)
    (RationalIntegerNormalization.reducedNumerator (ZT.ofNat j) (scale t))
    (RationalIntegerNormalization.reducedDenominator (ZT.ofNat j) (scale t)))
  exact e.eqTrans ((congrAp2 quoF (zero_monus j) (.eqRefl _)).eqTrans (quo_zero _))

theorem fraction_interval (j t : PTm k) (hj : Γ ⊢[PRAAx] le j (scale t)) : Γ ⊢[PRAAx] interval (fraction j t) := by
  have hn := fraction_negative_zero (Γ := Γ) j t
  have clear : Γ ⊢[PRAAx] scale t*(numeratorOf (fraction j t)).pos ≐ j*denominatorOf (fraction j t) := by
    have e := ZT.toZ_eq (fraction_represents (Γ := Γ) j t)
    have z := natEq hn
    apply deriveNat
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e
    simp only [ZT.toZ] at e
    ipra_simps
    linear_combination -e+𝔞(scale t)*z
  have upper : Γ ⊢[PRAAx] le (numeratorOf (fraction j t)).pos (denominatorOf (fraction j t)) :=
    RationalValueBounds.positive_cancel (scale_positive t)
      (le_congr clear.eqSymm (.eqRefl _) (mul_le_mul_right (denominatorOf (fraction j t)) hj))
  exact .andI (le_congr hn.eqSymm (.eqRefl _) (zero_le _))
    (le_congr (.eqRefl _) ((congrAdd hn (.eqRefl _)).eqTrans (zero_add _)).eqSymm upper)

theorem interval_congr {q q' : PTm k} (e : Γ ⊢[PRAAx] q ≐ q') (h : Γ ⊢[PRAAx] interval q) : Γ ⊢[PRAAx] interval q' := by
  have proof := Prf.eqSubst (interval (var 0) : Fm PTm 1) ![q] ![q'] (fun i => by fin_cases i; exact e)
    (by simpa using h)
  simpa using proof

theorem grid_digit_bound (t w i : PTm k) : Γ ⊢[PRAAx] le (digit (radix t) w i) (scale t) :=
  (succ_monus_succ (digit (radix t) w i) (scale t)).eqSymm.eqTrans (.andE₂ (divide_spec (radix t) (quo w (pw (radix t) i)) (zero_lt_succ _)))
theorem point_cube (d t w : PTm k) : Γ ⊢[PRAAx] cube (point d t w) d := by
  refine .andI (point_length _ _ _) (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift d) := Prf.hyp0
  simpa only [Δ,Syn.shift,subst_point] using interval_congr (point_lookup (Syn.shift d) (Syn.shift t) (Syn.shift w) (var 0) hi).eqSymm
    (fraction_interval _ _ (grid_digit_bound (Syn.shift t) (Syn.shift w) (reflected (Syn.shift d) (var 0))))

private theorem abs_scale (c : PTm k) (u : ZT k) : Γ ⊢[PRAAx] zabs (ZT.ofNat c*u) ≐ c*zabs u := by
  have e : ZT.toZ Γ (ZT.ofNat c*u) = ZT.toZ Γ (⟨c*u.pos,c*u.neg⟩ : ZT k) := by
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    simp only [ZT.toZ,Q.mk_mul,map_mul]
    ring
  exact (zabs_congr e).eqTrans (Probability.MedianWeighted.ad_mul c u.pos u.neg)

/-- Clear arbitrary true representatives, canceling only their positive denominators. -/
theorem radius_of_representations (q r : PTm k) (a b : ZT k) (A B P Q : PTm k)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a A) (hr : Γ ⊢[PRAAx] represents r b B)
    (h : Γ ⊢[PRAAx] le (Q*zabs (a*ZT.ofNat B-b*ZT.ofNat A)) (P*A*B)) :
    Γ ⊢[PRAAx] RationalValueBounds.radius q r P Q := by
  have e : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (A*B)*RationalValueBounds.cross q r)
      (ZT.ofNat (denominatorOf q*denominatorOf r)*(a*ZT.ofNat B-b*ZT.ofNat A)) := by
    ipra_lc [RationalValueBounds.cross] -𝔞(B)*𝔞(denominatorOf r)*ZT.toZ_eq hq+𝔞(A)*𝔞(denominatorOf q)*ZT.toZ_eq hr
  have abs : Γ ⊢[PRAAx] (A*B)*zabs (RationalValueBounds.cross q r) ≐
      (denominatorOf q*denominatorOf r)*zabs (a*ZT.ofNat B-b*ZT.ofNat A) :=
    (abs_scale _ _).eqSymm.eqTrans ((zabs_congr (ZT.toZ_eq e)).eqTrans (abs_scale _ _))
  apply RationalValueBounds.positive_cancel (RationalAlgebra.positive_product hA hB)
  have lifted := mul_le_mul_right (denominatorOf q*denominatorOf r) h
  exact le_congr (by have v := natEq abs; apply deriveNat; ipra_simps; linear_combination -𝔞(Q)*v)
    (by ipra_ring) lifted

theorem positive_part_represents (q : PTm k) (h : Γ ⊢[PRAAx] interval q) : Γ ⊢[PRAAx]
    represents q (ZT.ofNat (positivePart (numeratorOf q))) (denominatorOf q) := by
  have e := natEq (eq_add_of_le (.andE₁ h))
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ,positivePart]
  ipra_simps
  linear_combination -𝔞(denominatorOf q)*e

theorem rounded_scalar_radius (q t : PTm k) (h : Γ ⊢[PRAAx] interval q) : Γ ⊢[PRAAx]
    RationalValueBounds.radius q (fraction (roundedDigit q t) t) one (scale t) := by
  let D := denominatorOf q
  let P := positivePart (numeratorOf q)
  let R := rem (scale t*P) D
  have div := divide_spec (Γ := Γ) D (scale t*P) (RationalArgmin.denominator_positive q)
  have cross : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat P*ZT.ofNat (scale t)-ZT.ofNat (roundedDigit q t)*ZT.ofNat D) (ZT.ofNat R) := by
    change Γ ⊢[PRAAx] ZT.eq (ZT.ofNat P*ZT.ofNat (scale t)-ZT.ofNat (quo (scale t*P) D)*ZT.ofNat D) (ZT.ofNat R)
    ipra_lc natEq (.andE₁ div)
  have abs : Γ ⊢[PRAAx] zabs (ZT.ofNat P*ZT.ofNat (scale t)-ZT.ofNat (roundedDigit q t)*ZT.ofNat D) ≐ R :=
    (zabs_congr (ZT.toZ_eq cross)).eqTrans ((congrAdd (monus_zero R) (zero_monus R)).eqTrans (add_zero R))
  apply radius_of_representations q _ _ _ D (scale t) one (scale t) (RationalArgmin.denominator_positive q) (scale_positive t)
    (positive_part_represents q h) (fraction_represents _ _)
  exact le_congr (congrMul (.eqRefl _) abs).eqSymm (by ipra_ring)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (scale t) (le_of_lt (.andE₂ div))))

theorem fraction_congr {j j' t t' : PTm k} (hj : Γ ⊢[PRAAx] j ≐ j') (ht : Γ ⊢[PRAAx] t ≐ t') :
    Γ ⊢[PRAAx] fraction j t ≐ fraction j' t' := by
  ipra_congr (fraction (var 0) (var 1) : PTm 2) with [hj, ht]
theorem rounded_point_lookup (x d t i : PTm k) (h : Γ ⊢[PRAAx] cube x d) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    entry (point d t (roundIndex x d t)) i ≐ fraction (roundedDigit (entry x i) t) t :=
  (point_lookup _ _ _ _ hi).eqTrans (fraction_congr (round_index_digit _ _ _ _ h hi) (.eqRefl _))
theorem rounded_coordinate_radius (x d t i : PTm k) (h : Γ ⊢[PRAAx] cube x d) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx]
    RationalHausdorff.coordinateRadius x (point d t (roundIndex x d t)) i one (scale t) := by
  have bound : Γ ⊢[PRAAx] RationalValueBounds.radius (entry x i) (entry (point d t (roundIndex x d t)) i) one (scale t) :=
    RationalValueBounds.radius_congr (.eqRefl _) (rounded_point_lookup x d t i h hi).eqSymm (.eqRefl _) (.eqRefl _)
      (rounded_scalar_radius _ t (cube_at _ _ _ h hi))
  exact le_congr (.eqRefl _) (mul_assoc _ _ _) bound
theorem rounded_point_radius (x d t : PTm k) (h : Γ ⊢[PRAAx] cube x d) : Γ ⊢[PRAAx]
    RationalHausdorff.pointRadius x (point d t (roundIndex x d t)) d one (scale t) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] cube (Syn.shift x) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_point,subst_roundIndex,subst_scale,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    rounded_coordinate_radius (Syn.shift x) (Syn.shift d) (Syn.shift t) (var 0) hs.wk Prf.hyp0

theorem rounded_grid_radius (x d t : PTm k) (h : Γ ⊢[PRAAx] cube x d) : Γ ⊢[PRAAx]
    RationalHausdorff.pointRadius x (entry (grid d t) (roundIndex x d t)) d one (scale t) :=
  RationalHausdorffConcat.pointRadius_congr (.eqRefl _) (grid_lookup _ _ _ (round_index_bound x d t h)).eqSymm (rounded_point_radius x d t h)
theorem grid_coverage (x d t : PTm k) (h : Γ ⊢[PRAAx] cube x d) : Γ ⊢[PRAAx]
    RationalPointDistance.pointHit x (grid d t) d one (scale t) :=
  RationalPointDistance.pointHit_intro _ _ _ _ _ (roundIndex x d t)
    (lt_congr (.eqRefl _) (grid_length d t).eqSymm (round_index_bound x d t h)) (rounded_grid_radius x d t h)

theorem point_zero_dimension (t w : PTm k) : Γ ⊢[PRAAx] point zero t w ≐ Foundations.SequenceComposition.empty :=
  congrPairT (.eqRefl _) (Foundations.MasterCertificate.stack_zero _ _)
theorem round_index_zero_dimension (x t : PTm k) : Γ ⊢[PRAAx] roundIndex x zero t ≐ zero := sum_zero _ _

def output (x d t : PTm k) : PTm k := pairT (grid d t) (pairT (roundIndex x d t)
  (pairT (point d t (roundIndex x d t)) (pairT (scale t) (count d t))))
def gridF : PR 2 := PTm.toPR (grid (var 0) (var 1))
def roundIndexF : PR 3 := PTm.toPR (roundIndex (var 0) (var 1) (var 2))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (x d t : PTm k) : PTm k := app outputF ![x,d,t]
@[simp] theorem subst_output {l : ℕ} (σ : Fin k → PTm l) (x d t : PTm k) :
    Syn.subst σ (output x d t) = output (Syn.subst σ x) (Syn.subst σ d) (Syn.subst σ t) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin k → PTm l) (x d t : PTm k) :
    Syn.subst σ (run x d t) = run (Syn.subst σ x) (Syn.subst σ d) (Syn.subst σ t) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem grid_program_at (d t : PTm k) : Γ ⊢[PRAAx] app gridF ![d,t] ≐ grid d t := by
  simpa [gridF] using toPR_eq (Γ := Γ) (grid (var 0) (var 1) : PTm 2) ![d,t]
theorem round_index_program_at (x d t : PTm k) : Γ ⊢[PRAAx] app roundIndexF ![x,d,t] ≐ roundIndex x d t := by
  simpa [roundIndexF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (roundIndex (var 0) (var 1) (var 2) : PTm 3) ![x,d,t]
theorem program_at (x d t : PTm k) : Γ ⊢[PRAAx] run x d t ≐ output x d t := by
  simpa [run,outputF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![x,d,t]
theorem returned_grid (x d t : PTm k) : Γ ⊢[PRAAx] fstT (run x d t) ≐ grid d t :=
  (congrFst (program_at x d t)).eqTrans (fst_pair _ _)
theorem returned_index (x d t : PTm k) : Γ ⊢[PRAAx] fstT (sndT (run x d t)) ≐ roundIndex x d t :=
  (congrFst ((congrSnd (program_at x d t)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
private theorem returned_tail (x d t : PTm k) : Γ ⊢[PRAAx] sndT (sndT (run x d t)) ≐
    pairT (point d t (roundIndex x d t)) (pairT (scale t) (count d t)) :=
  (congrSnd ((congrSnd (program_at x d t)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_point (x d t : PTm k) : Γ ⊢[PRAAx] fstT (sndT (sndT (run x d t))) ≐ point d t (roundIndex x d t) :=
  (congrFst (returned_tail x d t)).eqTrans (fst_pair _ _)
theorem returned_scale (x d t : PTm k) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run x d t)))) ≐ scale t :=
  (congrFst ((congrSnd (returned_tail x d t)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_count (x d t : PTm k) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run x d t)))) ≐ count d t :=
  (congrSnd ((congrSnd (returned_tail x d t)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_radius (x d t : PTm k) (h : Γ ⊢[PRAAx] cube x d) : Γ ⊢[PRAAx]
    RationalHausdorff.pointRadius x (fstT (sndT (sndT (run x d t)))) d one (scale t) :=
  RationalHausdorffConcat.pointRadius_congr (.eqRefl _) (returned_point x d t).eqSymm (rounded_point_radius x d t h)

theorem actual_dyadic_cube_grid_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (grid (var 0) (var 1)) ≐ count (var 0) (var 1)) := closeUniv 2 (grid_length _ _)
theorem actual_dyadic_cube_grid_count_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (count (var 0) (var 1))) := closeUniv 2 (count_positive _ _)
theorem actual_dyadic_cube_point_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (point (var 0) (var 1) (var 2)) ≐ var 0) := closeUniv 3 (point_length _ _ _)
theorem actual_dyadic_cube_coordinate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 0) ⟶ entry (point (var 0) (var 1) (var 2)) (var 3) ≐
      fraction (digit (radix (var 1)) (var 2) (reflected (var 0) (var 3))) (var 1)) :=
  closeUniv 4 (.impI (point_lookup _ _ _ _ Prf.hyp0))
theorem actual_dyadic_cube_point_valid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cube (point (var 0) (var 1) (var 2)) (var 0)) := closeUniv 3 (point_cube _ _ _)
theorem actual_cube_rounding_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cube (var 0) (var 1) ⟶ lt (roundIndex (var 0) (var 1) (var 2)) (count (var 1) (var 2))) :=
  closeUniv 3 (.impI (round_index_bound _ _ _ Prf.hyp0))
theorem actual_cube_rounded_coordinate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (cube (var 0) (var 1) ⟶ lt (var 3) (var 1) ⟶
      entry (point (var 1) (var 2) (roundIndex (var 0) (var 1) (var 2))) (var 3) ≐
        fraction (roundedDigit (entry (var 0) (var 3)) (var 2)) (var 2)) :=
  closeUniv 4 (.impI (.impI (rounded_point_lookup _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cube_rounding_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cube (var 0) (var 1) ⟶ RationalHausdorff.pointRadius (var 0)
      (point (var 1) (var 2) (roundIndex (var 0) (var 1) (var 2))) (var 1) one (scale (var 2))) :=
  closeUniv 3 (.impI (rounded_point_radius _ _ _ Prf.hyp0))
theorem actual_cube_grid_coverage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cube (var 0) (var 1) ⟶ RationalPointDistance.pointHit (var 0) (grid (var 1) (var 2)) (var 1) one (scale (var 2))) :=
  closeUniv 3 (.impI (grid_coverage _ _ _ Prf.hyp0))
theorem actual_zero_dimensional_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point zero (var 1) (var 0) ≐ Foundations.SequenceComposition.empty ⋏
      (roundIndex (var 0) zero (var 1) ≐ zero ⋏ count zero (var 1) ≐ one)) :=
  closeUniv 2 (.andI (point_zero_dimension _ _) (.andI (round_index_zero_dimension _ _) (count_zero _)))
theorem actual_cube_grid_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_cube_grid_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cube (var 0) (var 1) ⟶ RationalHausdorff.pointRadius (var 0)
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2))))) (var 1) one (scale (var 2))) :=
  closeUniv 3 (.impI (returned_radius _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalCubeGrid
