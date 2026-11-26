import IPRADerivations.DiophantineNumberTheory.MinkowskiContentSum
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalNormalForm
import IPRADerivations.Analysis.Optimization.RationalArgmin
import IPRADerivations.Analysis.RationalArithmetic.RationalArithmetic

/-!
# Actual finite sums of independently denominated signed rationals

A fixed term body returns a rational code at the runtime index and persistent
data. Positive and negative numerator accumulators each use the actual
recurrence E'=E*q+p*D, sharing the actual product denominator. Final output
is gcd-normalized into the proved canonical rational representation.

The finite monotonicity proof uses a quantifier-free prefix invariant on
cross numerators of two independently computed denominator products. Only
termwise original rational inequalities are assumptions. This is numerical
sum arithmetic for the Minkowski slab frontend, not a supplied global sum
law or a complete geometric slab theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalFiniteSum

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf subst_numeratorOf subst_denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization
  (normalize normalize_preserves_value integerCode normalize_integer)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed normalize_well_formed well_formed_unique)
open LeanProofs.IPRA.Analysis.RationalArgmin (left rationalLE rationalEq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Actual independently denominated term of the fixed family. -/
def term (A : PTm 2) (i x : PTm n) : PTm n := inst2 A i x
def positiveBody (A : PTm 2) : PTm 2 := (numeratorOf A).pos
def negativeBody (A : PTm 2) : PTm 2 := (numeratorOf A).neg
def denominatorBody (A : PTm 2) : PTm 2 := denominatorOf A

def positive (A : PTm 2) (N x : PTm n) : PTm n :=
  DiophantineNumberTheory.MinkowskiContentSum.numerator (positiveBody A) (denominatorBody A) N x
def negative (A : PTm 2) (N x : PTm n) : PTm n :=
  DiophantineNumberTheory.MinkowskiContentSum.numerator (negativeBody A) (denominatorBody A) N x
def denominator (A : PTm 2) (N x : PTm n) : PTm n :=
  DiophantineNumberTheory.MinkowskiContentSum.denominator (denominatorBody A) N x
def numerator (A : PTm 2) (N x : PTm n) : ZT n := ⟨positive A N x,negative A N x⟩
def sum (A : PTm 2) (N x : PTm n) : PTm n := normalize (numerator A N x) (denominator A N x)

@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (A : PTm 2) (i x : PTm n) :
    Syn.subst σ (term A i x) = term A (Syn.subst σ i) (Syn.subst σ x) := subst_inst2 _ _ _ _
@[simp] theorem subst_positive {l : ℕ} (σ : Fin n → PTm l) (A : PTm 2) (N x : PTm n) :
    Syn.subst σ (positive A N x) = positive A (Syn.subst σ N) (Syn.subst σ x) := subst_ap2 _ _ _ _
@[simp] theorem subst_negative {l : ℕ} (σ : Fin n → PTm l) (A : PTm 2) (N x : PTm n) :
    Syn.subst σ (negative A N x) = negative A (Syn.subst σ N) (Syn.subst σ x) := subst_ap2 _ _ _ _
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (A : PTm 2) (N x : PTm n) :
    Syn.subst σ (denominator A N x) = denominator A (Syn.subst σ N) (Syn.subst σ x) := subst_ap2 _ _ _ _
ipra_subst numerator [ZT.subst, subst_positive, subst_negative]
ipra_subst sum

@[simp] theorem positiveBody_at (A : PTm 2) (i x : PTm n) :
    inst2 (positiveBody A) i x = (numeratorOf (term A i x)).pos := by
  simp only [positiveBody, term, inst2, numeratorOf, subst_fstT]
@[simp] theorem negativeBody_at (A : PTm 2) (i x : PTm n) :
    inst2 (negativeBody A) i x = (numeratorOf (term A i x)).neg := by
  simp only [negativeBody, term, inst2, numeratorOf, subst_fstT, subst_sndT]
@[simp] theorem denominatorBody_at (A : PTm 2) (i x : PTm n) :
    inst2 (denominatorBody A) i x = denominatorOf (term A i x) := by
  simp only [denominatorBody, term, inst2, denominatorOf, ConciseIPRA.PTm.subst_succ, subst_sndT]

theorem positive_zero (A : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] positive A zero x ≐ zero :=
  DiophantineNumberTheory.MinkowskiContentSum.numerator_zero _ _ _
theorem negative_zero (A : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] negative A zero x ≐ zero :=
  DiophantineNumberTheory.MinkowskiContentSum.numerator_zero _ _ _
theorem denominator_zero (A : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] denominator A zero x ≐ one := prod_zero _ _

theorem positive_succ (A : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] positive A (succ N) x ≐ positive A N x*denominatorOf (term A N x)+
      (numeratorOf (term A N x)).pos*denominator A N x := by
  simpa only [positive, denominator, positiveBody_at, denominatorBody_at] using
    DiophantineNumberTheory.MinkowskiContentSum.numerator_succ (Γ := Γ) (positiveBody A) (denominatorBody A) N x

theorem negative_succ (A : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] negative A (succ N) x ≐ negative A N x*denominatorOf (term A N x)+
      (numeratorOf (term A N x)).neg*denominator A N x := by
  simpa only [negative, denominator, negativeBody_at, denominatorBody_at] using
    DiophantineNumberTheory.MinkowskiContentSum.numerator_succ (Γ := Γ) (negativeBody A) (denominatorBody A) N x

theorem denominator_succ (A : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] denominator A (succ N) x ≐ denominator A N x*denominatorOf (term A N x) := by
  have h : Γ ⊢[PRAAx] denominator A (succ N) x ≐ denominator A N x*inst2 (denominatorBody A) N x :=
    prod_succ (denominatorBody A) N x
  simpa only [denominatorBody_at] using h

theorem denominator_positive (A : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] le one (denominator A N x) := by
  have pos : Γ ⊢[PRAAx] denominator A N x ≐ succ (PTm.pred (denominator A N x)) := by
    apply prod_pos_bounded (denominatorBody A) x N
    refine .allI (.impI ?_)
    rw [denominatorBody_at]
    exact RationalIntegerNormalization.positive_form (RationalArgmin.denominator_positive _)
  exact le_congr (.eqRefl _) pos.eqSymm (zero_lt_succ _)

/-- The actual signed numerator has the ordinary rational addition recurrence. -/
theorem numerator_succ (A : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (numerator A (succ N) x)
      (numerator A N x*ZT.ofNat (denominatorOf (term A N x))+
        numeratorOf (term A N x)*ZT.ofNat (denominator A N x)) := by
  apply ZT.derive
  have p := natEq (positive_succ (Γ := Γ) A N x)
  have q := natEq (negative_succ (Γ := Γ) A N x)
  rw [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_ofNat]
  simp only [numerator, ZT.toZ]
  ipra_simps
  linear_combination p-q

/-- Cross equality identifies the actual canonical output with its computed
signed numerator and independent product denominator. -/
theorem sum_value (A : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (numerator A N x*ZT.ofNat (denominatorOf (sum A N x)))
      (numeratorOf (sum A N x)*ZT.ofNat (denominator A N x)) :=
  normalize_preserves_value _ _ (denominator_positive A N x)

theorem sum_well_formed (A : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] wellFormed (sum A N x) :=
  normalize_well_formed _ _ (denominator_positive A N x)

/-- Successor value is the actual new rational term added to the accumulated
raw fraction; this equality includes all denominator factors explicitly. -/
theorem sum_succ_value (A : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ZT.eq
      ((numerator A N x*ZT.ofNat (denominatorOf (term A N x))+
        numeratorOf (term A N x)*ZT.ofNat (denominator A N x))*ZT.ofNat (denominatorOf (sum A (succ N) x)))
      (numeratorOf (sum A (succ N) x)*ZT.ofNat (denominator A N x*denominatorOf (term A N x))) := by
  apply ZT.derive
  have value := ZT.toZ_eq (sum_value (Γ := Γ) A (succ N) x)
  simp only [ZT.toZ_mul, ZT.toZ_ofNat] at value ⊢
  rw [ZT.toZ_eq (numerator_succ (Γ := Γ) A N x),natEq (denominator_succ (Γ := Γ) A N x)] at value
  simpa only [Q.mk_mul,map_mul] using value

/-- Empty sums return the literal canonical zero code. -/
theorem sum_zero (A : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] sum A zero x ≐ integerCode (ZT.natLit 0) := by
  apply normalize_integer _ _ _ (denominator_positive A zero x)
  apply ZT.derive
  have p := natEq (positive_zero (Γ := Γ) A x)
  have q := natEq (negative_zero (Γ := Γ) A x)
  rw [ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit]
  simp only [numerator,ZT.toZ]
  ipra_simps
  linear_combination p-q

/-- The actual cross numerator for two independently accumulated sums. -/
def rawLeft (A B : PTm 2) (N x y : PTm n) : PTm n :=
  positive A N x*denominator B N y+negative B N y*denominator A N x

def rawOrder (A B : PTm 2) (N x y : PTm n) : Fm PTm n :=
  le (rawLeft A B N x y) (rawLeft B A N y x)

def termwiseLE (A B : PTm 2) (N x y : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ rationalLE
    (term A (var 0) (Syn.shift x)) (term B (var 0) (Syn.shift y)))

ipra_subst rawLeft
ipra_subst rawOrder
ipra_subst termwiseLE [Fm.subst_all, Fm.subst_imp, subst_lt, RationalArgmin.subst_rationalLE, subst_term,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem termwise_at (A B : PTm 2) (N x y i : PTm n)
    (h : Γ ⊢[PRAAx] termwiseLE A B N x y) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] rationalLE (term A i x) (term B i y) := by
  have inst : Γ ⊢[PRAAx] lt i N ⟶ rationalLE (term A i x) (term B i y) := by
    simpa only [Fm.subst_imp,subst_lt,RationalArgmin.subst_rationalLE,subst_term,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE inst hi

/-- The successor cross numerator separates the old comparison and new term. -/
theorem rawLeft_succ (A B : PTm 2) (N x y : PTm n) : Γ ⊢[PRAAx]
    rawLeft A B (succ N) x y ≐
      (denominatorOf (term A N x)*denominatorOf (term B N y))*rawLeft A B N x y+
      (denominator A N x*denominator B N y)*left (term A N x) (term B N y) := by
  have p := natEq (positive_succ (Γ := Γ) A N x)
  have m := natEq (negative_succ (Γ := Γ) B N y)
  have d := natEq (denominator_succ (Γ := Γ) A N x)
  have e := natEq (denominator_succ (Γ := Γ) B N y)
  unfold rawLeft left
  apply deriveNat
  ipra_simps
  rw [p,m,d,e]
  ring

/-- The proof step needs only the preceding cross comparison and actual new
term comparison; neither product denominator is replaced by a common scale. -/
theorem rawOrder_succ (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] rawOrder A B N x y)
    (ht : Γ ⊢[PRAAx] rationalLE (term A N x) (term B N y)) :
    Γ ⊢[PRAAx] rawOrder A B (succ N) x y := by
  have old := natEq (eq_add_of_le h)
  have new := natEq (eq_add_of_le ht)
  have a := natEq (rawLeft_succ (Γ := Γ) A B N x y)
  have b := natEq (rawLeft_succ (Γ := Γ) B A N y x)
  refine le_of_eq_add (d :=
    (denominatorOf (term A N x)*denominatorOf (term B N y))*
      PTm.monus (rawLeft B A N y x) (rawLeft A B N x y)+
    (denominator A N x*denominator B N y)*
      PTm.monus (left (term B N y) (term A N x)) (left (term A N x) (term B N y))) ?_
  apply deriveNat
  ipra_simps
  rw [a,b]
  linear_combination
    𝔞(denominatorOf (term A N x))*𝔞(denominatorOf (term B N y))*old+
    𝔞(denominator A N x)*𝔞(denominator B N y)*new

/-- Quantifier-free induction proves the finite sum comparison from just the
bounded original rational term inequalities. -/
theorem raw_monotone (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] termwiseLE A B N x y) : Γ ⊢[PRAAx] rawOrder A B N x y := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      rawOrder A B (var 0) (Syn.shift x) (Syn.shift y)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_le, subst_rawOrder]
    · refine .impI ?_
      have p := positive_zero (Γ := Γ) A x
      have m := negative_zero (Γ := Γ) B y
      have p' := positive_zero (Γ := Γ) B y
      have m' := negative_zero (Γ := Γ) A x
      have a : Γ ⊢[PRAAx] rawLeft A B zero x y ≐ zero :=
        (congrAdd (congrMul p (.eqRefl _)) (congrMul m (.eqRefl _))).eqTrans (by ipra_ring)
      have b : Γ ⊢[PRAAx] rawLeft B A zero y x ≐ zero :=
        (congrAdd (congrMul p' (.eqRefl _)) (congrMul m' (.eqRefl _))).eqTrans (by ipra_ring)
      exact (le_congr a.eqSymm b.eqSymm (le_refl zero)).wk
    · refine .impI ?_
      let IH : Fm PTm (n+1) := le (var 0) (Syn.shift N) ⟶ rawOrder A B (var 0) (Syn.shift x) (Syn.shift y)
      let Δ : List (Fm PTm (n+1)) := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] rawOrder A B (var 0) (Syn.shift x) (Syn.shift y) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have contract : Γ.map Fm.shift ⊢[PRAAx] termwiseLE A B (Syn.shift N) (Syn.shift x) (Syn.shift y) := by
        simpa only [Fm.shift,subst_termwiseLE,Syn.shift] using h.shift
      exact rawOrder_succ A B _ _ _ ih (termwise_at A B _ _ _ _ contract.wk.wk Prf.hyp0)
  have out : Γ ⊢[PRAAx] le N N ⟶ rawOrder A B N x y := by
    simpa only [Fm.subst_imp,subst_le,subst_rawOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE out (le_refl _)

/-- The signed cross comparison is exactly the natural prefix invariant. -/
theorem rawOrder_to_zle (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] rawOrder A B N x y) : Γ ⊢[PRAAx]
    zle (numerator A N x*ZT.ofNat (denominator B N y))
      (numerator B N y*ZT.ofNat (denominator A N x)) := by
  apply zle_of_toZ (PTm.monus (rawLeft B A N y x) (rawLeft A B N x y))
  have eq := natEq (eq_add_of_le h)
  rw [ZT.toZ_mul,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  unfold rawLeft at eq ⊢
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at eq
  linear_combination -eq

/-- Finite monotonicity for the actual normalized sum outputs. -/
theorem sum_monotone (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] termwiseLE A B N x y) :
    Γ ⊢[PRAAx] rationalLE (sum A N x) (sum B N y) :=
  RationalArithmetic.order_of_representations _ _ _ _ _ _
    (sum_value A N x) (sum_value B N y)
    (denominator_positive A N x) (denominator_positive B N y)
    (rawOrder_to_zle A B N x y (raw_monotone A B N x y h))

/-- Equality of raw values transports to literal canonical code equality.
The denominator guards are numerical positivity only. -/
theorem canonical_equal (c d : PTm n) (a b : ZT n) (A B : PTm n)
    (hc : Γ ⊢[PRAAx] wellFormed c) (hd : Γ ⊢[PRAAx] wellFormed d)
    (hcv : Γ ⊢[PRAAx] RationalArithmetic.represents c a A)
    (hdv : Γ ⊢[PRAAx] RationalArithmetic.represents d b B)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (heq : Γ ⊢[PRAAx] ZT.eq (a*ZT.ofNat B) (b*ZT.ofNat A)) : Γ ⊢[PRAAx] c ≐ d := by
  have forward : Γ ⊢[PRAAx] zle (a*ZT.ofNat B) (b*ZT.ofNat A) := by
    apply zle_of_toZ zero
    simpa only [Q.mk_zero,map_zero,_root_.add_zero] using ZT.toZ_eq heq
  have reverse : Γ ⊢[PRAAx] zle (b*ZT.ofNat A) (a*ZT.ofNat B) := by
    apply zle_of_toZ zero
    have h := (ZT.toZ_eq heq).symm
    simpa only [Q.mk_zero,map_zero,_root_.add_zero] using h
  have eq := RationalArgmin.antisymm
    (RationalArithmetic.order_of_representations c d a b A B hcv hdv hA hB forward)
    (RationalArithmetic.order_of_representations d c b a B A hdv hcv hB hA reverse)
  apply well_formed_unique c d hc hd
  apply ZT.derive
  have e := natEq eq
  rw [ZT.toZ_mul,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at e
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at e
  linear_combination e

/-- The actual sum program performs canonical rational addition at every
successor, including arbitrary signed terms and the empty prefix. -/
theorem sum_succ (A : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    sum A (succ N) x ≐ RationalArithmetic.add (sum A N x) (term A N x) := by
  apply canonical_equal _ _ _ _ _ _ (sum_well_formed A (succ N) x)
    (RationalArithmetic.add_guard _ _) (sum_value A (succ N) x)
    (RationalArithmetic.add_value _ _) (denominator_positive A (succ N) x)
    (RationalArithmetic.product_denominator_positive _ _)
  apply ZT.derive
  have step := ZT.toZ_eq (numerator_succ (Γ := Γ) A N x)
  have value := ZT.toZ_eq (sum_value (Γ := Γ) A N x)
  have den := natEq (denominator_succ (Γ := Γ) A N x)
  simp only [RationalArithmetic.productDenominator,RationalArithmetic.addNumerator,
    ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at step value ⊢
  simp only [Q.mk_mul,map_mul] at den ⊢
  rw [step,den]
  linear_combination 𝔞(denominatorOf (term A N x))*𝔞(denominatorOf (term A N x))*value

/-- Original value equality of terms, without requiring identical input
codes or common denominators. -/
def termwiseEq (A B : PTm 2) (N x y : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ rationalEq
    (term A (var 0) (Syn.shift x)) (term B (var 0) (Syn.shift y)))

ipra_subst termwiseEq [Fm.subst_all, Fm.subst_imp, subst_lt, RationalArgmin.subst_rationalEq, subst_term,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem termwiseEq_forward (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] termwiseEq A B N x y) : Γ ⊢[PRAAx] termwiseLE A B N x y := by
  refine .allI (.impI ?_)
  exact RationalArgmin.eq_le (.impE h.allOpen.wk Prf.hyp0)

theorem termwiseEq_reverse (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] termwiseEq A B N x y) : Γ ⊢[PRAAx] termwiseLE B A N y x := by
  refine .allI (.impI ?_)
  have eq := Prf.impE h.allOpen.wk Prf.hyp0
  exact RationalArgmin.eq_le eq.eqSymm

/-- Termwise rational equality gives literal equality of the computed
canonical outputs, including independent denominator products. -/
theorem sum_ext (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] termwiseEq A B N x y) : Γ ⊢[PRAAx] sum A N x ≐ sum B N y := by
  have eq := RationalArgmin.antisymm
    (sum_monotone A B N x y (termwiseEq_forward A B N x y h))
    (sum_monotone B A N y x (termwiseEq_reverse A B N x y h))
  apply well_formed_unique _ _ (sum_well_formed A N x) (sum_well_formed B N y)
  apply ZT.derive
  have e := natEq eq
  rw [ZT.toZ_mul,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at e
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at e
  linear_combination e

/-- Actual PR2 output program, with runtime horizon and persistent data. -/
def sumCodeF (A : PTm 2) : PR 2 := PTm.toPR (sum A (var 0) (var 1))

theorem sum_at (A : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumCodeF A) N x ≐ sum A N x := by
  simpa only [sumCodeF,ap2,subst_sum,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (sum A (var 0) (var 1) : PTm 2) ![N,x]

theorem sum_value_closed (A : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ZT.eq (numerator A (var 0) (var 1)*ZT.ofNat (denominatorOf (sum A (var 0) (var 1))))
      (numeratorOf (sum A (var 0) (var 1))*ZT.ofNat (denominator A (var 0) (var 1)))) :=
  closeUniv 2 (sum_value A _ _)

theorem sum_producer_closed (A : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (denominator A (var 0) (var 1)) ⋏
      (wellFormed (sum A (var 0) (var 1)) ⋏
        (ap2 (sumCodeF A) (var 0) (var 1) ≐ sum A (var 0) (var 1)))) :=
  closeUniv 2 (.andI (denominator_positive A _ _) (.andI (sum_well_formed A _ _) (sum_at A _ _)))

theorem raw_monotone_closed (A B : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (termwiseLE A B (var 0) (var 1) (var 2) ⟶ rawOrder A B (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (raw_monotone A B _ _ _ Prf.hyp0))

theorem sum_monotone_closed (A B : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (termwiseLE A B (var 0) (var 1) (var 2) ⟶ rationalLE
      (sum A (var 0) (var 1)) (sum B (var 0) (var 2))) :=
  closeUniv 3 (.impI (sum_monotone A B _ _ _ Prf.hyp0))

theorem sum_succ_closed (A : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum A (succ (var 0)) (var 1) ≐ RationalArithmetic.add
      (sum A (var 0) (var 1)) (term A (var 0) (var 1))) :=
  closeUniv 2 (sum_succ A _ _)

theorem sum_ext_closed (A B : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (termwiseEq A B (var 0) (var 1) (var 2) ⟶
      (sum A (var 0) (var 1) ≐ sum B (var 0) (var 2))) :=
  closeUniv 3 (.impI (sum_ext A B _ _ _ Prf.hyp0))

theorem sum_zero_closed (A : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (sum A zero (var 0) ≐ integerCode (ZT.natLit 0)) :=
  closeUniv 1 (sum_zero A _)

end LeanProofs.IPRA.Analysis.RationalFiniteSum
