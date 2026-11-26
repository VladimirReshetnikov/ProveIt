import IPRADerivations.Analysis.RationalArithmetic.RationalNormalForm
import IPRADerivations.Analysis.Optimization.RationalArgmin
import IPRADerivations.Analysis.RationalArithmetic.RationalValueBounds

/-!
# Actual canonical rational arithmetic and signed interval endpoints

This is the scalar arithmetic needed by the numerical rational-slab
specialization of Minkowski's certificate theorem.  Operations are actual
gcd-normalizing programs on independently denominated signed rational codes.
Cross-value and positive-denominator proofs connect the programs to rational
order.  The min/max programs compare the original cross products and return
canonical codes.  All scalar data are object-language inputs.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalArithmetic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed normalize_well_formed)
open LeanProofs.IPRA.Analysis.RationalArgmin (left rationalLE rationalEq denominator_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_le sg_lt)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def represents (c : PTm n) (a : ZT n) (D : PTm n) : Fm PTm n :=
  ZT.eq (a*ZT.ofNat (denominatorOf c)) (numeratorOf c*ZT.ofNat D)

def productDenominator (a b : PTm n) : PTm n := denominatorOf a*denominatorOf b
def addNumerator (a b : PTm n) : ZT n :=
  numeratorOf a*ZT.ofNat (denominatorOf b)+numeratorOf b*ZT.ofNat (denominatorOf a)
def add (a b : PTm n) : PTm n := normalize (addNumerator a b) (productDenominator a b)
def multiply (a b : PTm n) : PTm n := normalize (numeratorOf a*numeratorOf b) (productDenominator a b)
def negative (a : PTm n) : PTm n := normalize (-numeratorOf a) (denominatorOf a)
def recode (a : PTm n) : PTm n := normalize (numeratorOf a) (denominatorOf a)

@[simp] theorem subst_represents {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) (a : ZT n) (D : PTm n) :
    (represents c a D).subst σ = represents (Syn.subst σ c) (a.subst σ) (Syn.subst σ D) := by
  simp [represents]
@[simp] theorem subst_productDenominator {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (productDenominator a b) = productDenominator (Syn.subst σ a) (Syn.subst σ b) := by
  simp [productDenominator]
@[simp] theorem subst_addNumerator {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (addNumerator a b).subst σ = addNumerator (Syn.subst σ a) (Syn.subst σ b) := by simp [addNumerator]
@[simp] theorem subst_add {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (add a b) = add (Syn.subst σ a) (Syn.subst σ b) := by simp [add]
@[simp] theorem subst_multiply {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (multiply a b) = multiply (Syn.subst σ a) (Syn.subst σ b) := by simp [multiply]
@[simp] theorem subst_negative {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (negative a) = negative (Syn.subst σ a) := by simp [negative]
@[simp] theorem subst_recode {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (recode a) = recode (Syn.subst σ a) := by simp [recode]

theorem product_denominator_positive (a b : PTm n) : Γ ⊢[PRAAx] le one (productDenominator a b) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono (denominator_positive a) (denominator_positive b))

theorem add_value (a b : PTm n) : Γ ⊢[PRAAx] represents (add a b) (addNumerator a b) (productDenominator a b) :=
  normalize_preserves_value _ _ (product_denominator_positive a b)
theorem multiply_value (a b : PTm n) : Γ ⊢[PRAAx] represents (multiply a b) (numeratorOf a*numeratorOf b) (productDenominator a b) :=
  normalize_preserves_value _ _ (product_denominator_positive a b)
theorem negative_value (a : PTm n) : Γ ⊢[PRAAx] represents (negative a) (-numeratorOf a) (denominatorOf a) :=
  normalize_preserves_value _ _ (denominator_positive a)
theorem recode_value (a : PTm n) : Γ ⊢[PRAAx] represents (recode a) (numeratorOf a) (denominatorOf a) :=
  normalize_preserves_value _ _ (denominator_positive a)

theorem add_guard (a b : PTm n) : Γ ⊢[PRAAx] wellFormed (add a b) :=
  normalize_well_formed _ _ (product_denominator_positive a b)
theorem multiply_guard (a b : PTm n) : Γ ⊢[PRAAx] wellFormed (multiply a b) :=
  normalize_well_formed _ _ (product_denominator_positive a b)
theorem negative_guard (a : PTm n) : Γ ⊢[PRAAx] wellFormed (negative a) :=
  normalize_well_formed _ _ (denominator_positive a)
theorem recode_guard (a : PTm n) : Γ ⊢[PRAAx] wellFormed (recode a) :=
  normalize_well_formed _ _ (denominator_positive a)

theorem value_equality (a b : PTm n)
    (h : Γ ⊢[PRAAx] ZT.eq (numeratorOf a*ZT.ofNat (denominatorOf b))
      (numeratorOf b*ZT.ofNat (denominatorOf a))) : Γ ⊢[PRAAx] rationalEq a b := by
  have e := ZT.toZ_eq h
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e
  simp only [ZT.toZ] at e
  unfold left
  ipra_simps
  linear_combination e

theorem recode_equal (a : PTm n) : Γ ⊢[PRAAx] rationalEq (recode a) a := by
  apply value_equality
  apply ZT.derive
  exact (ZT.toZ_eq (recode_value (Γ := Γ) a)).symm

/-- Comparison against raw numerator/denominator representatives is
transported through proved value equations. Only positive A and B are
cancelled, not any signed numerator. -/
theorem order_of_representations (c d : PTm n) (a b : ZT n) (A B : PTm n)
    (hc : Γ ⊢[PRAAx] represents c a A) (hd : Γ ⊢[PRAAx] represents d b B)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] zle (a*ZT.ofNat B) (b*ZT.ofNat A)) : Γ ⊢[PRAAx] rationalLE c d := by
  have g := zle_toZ h
  have ec := ZT.toZ_eq hc
  have ed := ZT.toZ_eq hd
  have scaled : Γ ⊢[PRAAx] le ((A*B)*left c d) ((A*B)*left d c) := by
    refine le_of_eq_add (d := denominatorOf c*denominatorOf d*
      monus ((b*ZT.ofNat A).pos+(a*ZT.ofNat B).neg)
        ((a*ZT.ofNat B).pos+(b*ZT.ofNat A).neg)) ?_
    apply deriveNat
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at g ec ed
    simp only [ZT.toZ] at g ec ed
    unfold left
    ipra_simps
    linear_combination 𝔞(B)*𝔞(denominatorOf d)*ec-𝔞(A)*𝔞(denominatorOf c)*ed-
      𝔞(denominatorOf c)*𝔞(denominatorOf d)*g
  exact RationalValueBounds.positive_cancel
    (le_congr (one_mul one) (.eqRefl _) (le_mul_mono hA hB)) scaled

def orderBit (a b : PTm n) : PTm n := sg (monus (left a b) (left b a))
def select (bit a b : PTm n) : PTm n := bit*b+monus one bit*a
def minimum (a b : PTm n) : PTm n := select (orderBit a b) (recode a) (recode b)
def maximum (a b : PTm n) : PTm n := select (orderBit a b) (recode b) (recode a)

@[simp] theorem subst_orderBit {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (orderBit a b) = orderBit (Syn.subst σ a) (Syn.subst σ b) := by simp [orderBit,sg]
@[simp] theorem subst_select {m : ℕ} (σ : Fin n → PTm m) (bit a b : PTm n) :
    Syn.subst σ (select bit a b) = select (Syn.subst σ bit) (Syn.subst σ a) (Syn.subst σ b) := by simp [select]
@[simp] theorem subst_minimum {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (minimum a b) = minimum (Syn.subst σ a) (Syn.subst σ b) := by simp [minimum]
@[simp] theorem subst_maximum {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (maximum a b) = maximum (Syn.subst σ a) (Syn.subst σ b) := by simp [maximum]

theorem select_zero (bit a b : PTm n) (h : Γ ⊢[PRAAx] bit ≐ zero) : Γ ⊢[PRAAx] select bit a b ≐ a :=
  (congrAdd (congrMul h (.eqRefl _)) (congrMul ((congrMonus (.eqRefl one) h).eqTrans (monus_zero _)) (.eqRefl _))).eqTrans
    (by ipra_ring)
theorem select_one (bit a b : PTm n) (h : Γ ⊢[PRAAx] bit ≐ one) : Γ ⊢[PRAAx] select bit a b ≐ b :=
  (congrAdd (congrMul h (.eqRefl _)) (congrMul ((congrMonus (.eqRefl one) h).eqTrans (monus_self _)) (.eqRefl _))).eqTrans
    (by ipra_ring)

theorem minimum_left (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx] minimum a b ≐ recode a :=
  select_zero _ _ _ (sg_le h)
theorem maximum_right (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx] maximum a b ≐ recode b :=
  select_zero _ _ _ (sg_le h)
theorem minimum_right (a b : PTm n) (h : Γ ⊢[PRAAx] lt (left b a) (left a b)) : Γ ⊢[PRAAx] minimum a b ≐ recode b :=
  select_one _ _ _ (sg_lt h)
theorem maximum_left (a b : PTm n) (h : Γ ⊢[PRAAx] lt (left b a) (left a b)) : Γ ⊢[PRAAx] maximum a b ≐ recode a :=
  select_one _ _ _ (sg_lt h)

theorem minimum_bounds (a b : PTm n) : Γ ⊢[PRAAx] rationalLE (minimum a b) a ⋏ rationalLE (minimum a b) b := by
  refine .orE (lt_or_le (left b a) (left a b)) ?_ ?_
  · have e := minimum_right (Γ := lt (left b a) (left a b) :: Γ) a b Prf.hyp0
    have eb := RationalArgmin.eq_le (recode_equal (Γ := lt (left b a) (left a b) :: Γ) b)
    have ba : lt (left b a) (left a b) :: Γ ⊢[PRAAx] rationalLE b a := le_trans (le_succ_self _) Prf.hyp0
    exact .andI (RationalArgmin.rationalLE_congr e.eqSymm (.eqRefl _) (RationalArgmin.transitive eb ba))
      (RationalArgmin.rationalLE_congr e.eqSymm (.eqRefl _) eb)
  · have e := minimum_left (Γ := le (left a b) (left b a) :: Γ) a b Prf.hyp0
    have ea := RationalArgmin.eq_le (recode_equal (Γ := le (left a b) (left b a) :: Γ) a)
    exact .andI (RationalArgmin.rationalLE_congr e.eqSymm (.eqRefl _) ea)
      (RationalArgmin.rationalLE_congr e.eqSymm (.eqRefl _) (RationalArgmin.transitive ea Prf.hyp0))

theorem maximum_bounds (a b : PTm n) : Γ ⊢[PRAAx] rationalLE a (maximum a b) ⋏ rationalLE b (maximum a b) := by
  refine .orE (lt_or_le (left b a) (left a b)) ?_ ?_
  · have e := maximum_left (Γ := lt (left b a) (left a b) :: Γ) a b Prf.hyp0
    have ea := RationalArgmin.eq_le (recode_equal (Γ := lt (left b a) (left a b) :: Γ) a).eqSymm
    have ba : lt (left b a) (left a b) :: Γ ⊢[PRAAx] rationalLE b a := le_trans (le_succ_self _) Prf.hyp0
    exact .andI (RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm ea)
      (RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm (RationalArgmin.transitive ba ea))
  · have e := maximum_right (Γ := le (left a b) (left b a) :: Γ) a b Prf.hyp0
    have eb := RationalArgmin.eq_le (recode_equal (Γ := le (left a b) (left b a) :: Γ) b).eqSymm
    exact .andI (RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm (RationalArgmin.transitive Prf.hyp0 eb))
      (RationalArgmin.rationalLE_congr (.eqRefl _) e.eqSymm eb)

theorem multiply_monotone (c a b : PTm n)
    (hc : Γ ⊢[PRAAx] le (numeratorOf c).neg (numeratorOf c).pos)
    (h : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx] rationalLE (multiply c a) (multiply c b) := by
  apply order_of_representations _ _ _ _ _ _ (multiply_value c a) (multiply_value c b)
    (product_denominator_positive c a) (product_denominator_positive c b)
  let gap : PTm n := monus (left b a) (left a b)
  apply zle_of_toZ (denominatorOf c*monus (numeratorOf c).pos (numeratorOf c).neg*
    gap)
  have co := natEq (eq_add_of_le hc)
  have order : Γ ⊢[PRAAx] left b a ≐ left a b+gap := eq_add_of_le h
  have ab := natEq order
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at ab
  unfold productDenominator
  ipra_simps
  linear_combination -𝔞(denominatorOf c)*(𝔞((numeratorOf c).pos)-𝔞((numeratorOf c).neg))*ab-
    𝔞(denominatorOf c)*𝔞(gap)*co

theorem multiply_antitone (c a b : PTm n)
    (hc : Γ ⊢[PRAAx] le (numeratorOf c).pos (numeratorOf c).neg)
    (h : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx] rationalLE (multiply c b) (multiply c a) := by
  apply order_of_representations _ _ _ _ _ _ (multiply_value c b) (multiply_value c a)
    (product_denominator_positive c b) (product_denominator_positive c a)
  let gap : PTm n := monus (left b a) (left a b)
  apply zle_of_toZ (denominatorOf c*monus (numeratorOf c).neg (numeratorOf c).pos*
    gap)
  have co := natEq (eq_add_of_le hc)
  have order : Γ ⊢[PRAAx] left b a ≐ left a b+gap := eq_add_of_le h
  have ab := natEq order
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at ab
  unfold productDenominator
  ipra_simps
  linear_combination 𝔞(denominatorOf c)*(𝔞((numeratorOf c).pos)-𝔞((numeratorOf c).neg))*ab-
    𝔞(denominatorOf c)*𝔞(gap)*co

/-- The scalar interval used in the actual slab-box checker. The coefficient
can have either sign and neither endpoint denominator is a supplied scale. -/
theorem multiply_interval (c l u q : PTm n) (hl : Γ ⊢[PRAAx] rationalLE l q)
    (hu : Γ ⊢[PRAAx] rationalLE q u) :
    Γ ⊢[PRAAx] rationalLE (minimum (multiply c l) (multiply c u)) (multiply c q) ⋏
      rationalLE (multiply c q) (maximum (multiply c l) (multiply c u)) := by
  refine .orE (le_total (numeratorOf c).neg (numeratorOf c).pos) ?_ ?_
  · have lower := multiply_monotone (Γ := le (numeratorOf c).neg (numeratorOf c).pos :: Γ) c l q Prf.hyp0 hl.wk
    have upper := multiply_monotone (Γ := le (numeratorOf c).neg (numeratorOf c).pos :: Γ) c q u Prf.hyp0 hu.wk
    exact .andI (RationalArgmin.transitive (Prf.andE₁ (minimum_bounds _ _)) lower)
      (RationalArgmin.transitive upper (Prf.andE₂ (maximum_bounds _ _)))
  · have lower := multiply_antitone (Γ := le (numeratorOf c).pos (numeratorOf c).neg :: Γ) c q u Prf.hyp0 hu.wk
    have upper := multiply_antitone (Γ := le (numeratorOf c).pos (numeratorOf c).neg :: Γ) c l q Prf.hyp0 hl.wk
    exact .andI (RationalArgmin.transitive (Prf.andE₂ (minimum_bounds _ _)) lower)
      (RationalArgmin.transitive upper (Prf.andE₁ (maximum_bounds _ _)))

theorem guard_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b)
    (hb : Γ ⊢[PRAAx] wellFormed b) : Γ ⊢[PRAAx] wellFormed a := by
  have e := Prf.eqSubst (wellFormed (var 0) : Fm PTm 1) ![b] ![a]
    (fun i => by fin_cases i; exact h.eqSymm) (by simpa using hb)
  simpa using e

theorem minimum_guard (a b : PTm n) : Γ ⊢[PRAAx] wellFormed (minimum a b) := by
  refine .orE (lt_or_le (left b a) (left a b)) ?_ ?_
  · exact guard_congr (minimum_right a b Prf.hyp0) (recode_guard b)
  · exact guard_congr (minimum_left a b Prf.hyp0) (recode_guard a)
theorem maximum_guard (a b : PTm n) : Γ ⊢[PRAAx] wellFormed (maximum a b) := by
  refine .orE (lt_or_le (left b a) (left a b)) ?_ ?_
  · exact guard_congr (maximum_left a b Prf.hyp0) (recode_guard a)
  · exact guard_congr (maximum_right a b Prf.hyp0) (recode_guard b)

def addF : PR 2 := PTm.toPR (add (var 0) (var 1))
def multiplyF : PR 2 := PTm.toPR (multiply (var 0) (var 1))
def negativeF : PR 1 := PTm.toPR (negative (var 0))
def minimumF : PR 2 := PTm.toPR (minimum (var 0) (var 1))
def maximumF : PR 2 := PTm.toPR (maximum (var 0) (var 1))

theorem add_at (a b : PTm n) : Γ ⊢[PRAAx] ap2 addF a b ≐ add a b := by
  simpa only [addF,ap2,subst_add,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (add (var 0) (var 1) : PTm 2) ![a,b]
theorem multiply_at (a b : PTm n) : Γ ⊢[PRAAx] ap2 multiplyF a b ≐ multiply a b := by
  simpa only [multiplyF,ap2,subst_multiply,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (multiply (var 0) (var 1) : PTm 2) ![a,b]
theorem negative_at (a : PTm n) : Γ ⊢[PRAAx] ap1 negativeF a ≐ negative a := by
  simpa only [negativeF,ap1,subst_negative,Syn.subst_var,Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (negative (var 0) : PTm 1) ![a]
theorem minimum_at (a b : PTm n) : Γ ⊢[PRAAx] ap2 minimumF a b ≐ minimum a b := by
  simpa only [minimumF,ap2,subst_minimum,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (minimum (var 0) (var 1) : PTm 2) ![a,b]
theorem maximum_at (a b : PTm n) : Γ ⊢[PRAAx] ap2 maximumF a b ≐ maximum a b := by
  simpa only [maximumF,ap2,subst_maximum,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (maximum (var 0) (var 1) : PTm 2) ![a,b]

theorem interval_multiply_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rationalLE (var 1) (var 3) ⟶ rationalLE (var 3) (var 2) ⟶
      (rationalLE (minimum (multiply (var 0) (var 1)) (multiply (var 0) (var 2))) (multiply (var 0) (var 3)) ⋏
        rationalLE (multiply (var 0) (var 3)) (maximum (multiply (var 0) (var 1)) (multiply (var 0) (var 2))))) :=
  closeUniv 4 (.impI (.impI (multiply_interval _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem arithmetic_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (represents (add (var 0) (var 1)) (addNumerator (var 0) (var 1)) (productDenominator (var 0) (var 1)) ⋏
      (represents (multiply (var 0) (var 1)) (numeratorOf (var 0)*numeratorOf (var 1)) (productDenominator (var 0) (var 1)) ⋏
        (represents (negative (var 0)) (-numeratorOf (var 0)) (denominatorOf (var 0)) ⋏
          rationalEq (recode (var 0)) (var 0)))) :=
  closeUniv 2 (.andI (add_value _ _) (.andI (multiply_value _ _) (.andI (negative_value _) (recode_equal _))))

theorem minmax_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((rationalLE (minimum (var 0) (var 1)) (var 0) ⋏ rationalLE (minimum (var 0) (var 1)) (var 1)) ⋏
      (rationalLE (var 0) (maximum (var 0) (var 1)) ⋏ rationalLE (var 1) (maximum (var 0) (var 1)))) :=
  closeUniv 2 (.andI (minimum_bounds _ _) (maximum_bounds _ _))

theorem arithmetic_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (wellFormed (add (var 0) (var 1)) ⋏ (wellFormed (multiply (var 0) (var 1)) ⋏
      (wellFormed (negative (var 0)) ⋏ (wellFormed (minimum (var 0) (var 1)) ⋏ wellFormed (maximum (var 0) (var 1)))))) :=
  closeUniv 2 (.andI (add_guard _ _) (.andI (multiply_guard _ _)
    (.andI (negative_guard _) (.andI (minimum_guard _ _) (maximum_guard _ _)))))

theorem arithmetic_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 addF (var 0) (var 1) ≐ add (var 0) (var 1)) ⋏
      ((ap2 multiplyF (var 0) (var 1) ≐ multiply (var 0) (var 1)) ⋏
        ((ap1 negativeF (var 0) ≐ negative (var 0)) ⋏
          ((ap2 minimumF (var 0) (var 1) ≐ minimum (var 0) (var 1)) ⋏
            (ap2 maximumF (var 0) (var 1) ≐ maximum (var 0) (var 1)))))) :=
  closeUniv 2 (.andI (add_at _ _) (.andI (multiply_at _ _) (.andI (negative_at _)
    (.andI (minimum_at _ _) (maximum_at _ _)))))

end LeanProofs.IPRA.Analysis.RationalArithmetic
