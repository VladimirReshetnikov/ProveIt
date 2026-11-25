import IPRADerivations.Analysis.ComplexLogarithmCauchy
import IPRADerivations.Foundations.GapDecision
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Primitive-recursive dyadic observations of finite complex log tails

Signed coordinates are rounded by two actual natural quotients. The error is
the difference of their actual remainders, so it is proved from `div_mod`.
The actual PR symbol `observationF(p,z,R,N)` observes truncation `p+4` with
dyadic denominator `2^(p+4)`. At arbitrary ordered internal precisions `p≤q`,
the coded discrepancy `O_q-2^(q-p)O_p` has norm at most `5·2^(q-p)`.
Consequently the dyadic rational observations differ by at most
`5·2^(-p-4) ≤ 2^(-p)`, with no adjacent rounding-motion assumption.
The observations concern the Taylor tail starting in degree three; neither
an infinite logarithm nor its functional laws are assumed here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.DyadicComplexLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq zabs_congr)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of)
open LeanProofs.IPRA.Analysis.LogarithmRemainder (denominator denominator_positive)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im code add scale normSq bounded series bounded_scale bounded_add bounded_neg
    bounded_mono normSq_eval normSq_code eval_re_code eval_im_code)
open LeanProofs.IPRA.Analysis.ComplexLogarithmCauchy (eval_re_congr eval_im_congr power_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def roundedCoordinate (x : ZT n) (D A : PTm n) : ZT n :=
  ⟨quo (A * x.pos) D, quo (A * x.neg) D⟩

def remainderCoordinate (x : ZT n) (D A : PTm n) : ZT n :=
  ⟨rem (A * x.neg) D, rem (A * x.pos) D⟩

def rounded (c D A : PTm n) : PTm n :=
  code (roundedCoordinate (re c) D A) (roundedCoordinate (im c) D A)

def roundingError (c D A : PTm n) : PTm n :=
  add (scale D (rounded c D A)) (ComplexLogarithmRemainder.neg (scale A c))

@[simp] theorem subst_roundedCoordinate {m : ℕ} (σ : Fin n → PTm m) (x : ZT n) (D A : PTm n) :
    (roundedCoordinate x D A).subst σ =
      roundedCoordinate (x.subst σ) (Syn.subst σ D) (Syn.subst σ A) := by
  simp [roundedCoordinate, ZT.subst]

@[simp] theorem subst_rounded {m : ℕ} (σ : Fin n → PTm m) (c D A : PTm n) :
    Syn.subst σ (rounded c D A) = rounded (Syn.subst σ c) (Syn.subst σ D) (Syn.subst σ A) := by
  simp [rounded]

@[simp] theorem subst_roundingError {m : ℕ} (σ : Fin n → PTm m) (c D A : PTm n) :
    Syn.subst σ (roundingError c D A) =
      roundingError (Syn.subst σ c) (Syn.subst σ D) (Syn.subst σ A) := by
  simp [roundingError]

theorem positive_division (x D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] (x ≐ D * quo x D + rem x D) ⋏ lt (rem x D) D := by
  have h : Γ ⊢[PRAAx] D ≐ succ (monus D one) :=
    (eq_add_of_le hD).eqTrans (by ipra_ring)
  exact div_mod_at h

/-- Exact signed quotient-rounding error, before any norm estimate. -/
theorem coordinate_error (x : ZT n) (D A : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    𝔞(D) * ZT.toZ Γ (roundedCoordinate x D A) - 𝔞(A) * ZT.toZ Γ x =
      ZT.toZ Γ (remainderCoordinate x D A) := by
  have p := natEq (Prf.andE₁ (positive_division (A * x.pos) D hD))
  have q := natEq (Prf.andE₁ (positive_division (A * x.neg) D hD))
  simp only [roundedCoordinate, remainderCoordinate, ZT.toZ, Q.mk_add, Q.mk_mul,
    map_add, map_mul] at p q ⊢
  linear_combination -p + q

theorem remainder_bound (x : ZT n) (D A : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le (zabs (remainderCoordinate x D A)) D := by
  have p := le_of_lt (Prf.andE₂ (positive_division (A * x.pos) D hD))
  have q := le_of_lt (Prf.andE₂ (positive_division (A * x.neg) D hD))
  exact ad_le_of (le_trans q (le_add_left D (rem (A * x.pos) D)))
    (le_trans p (le_add_left D (rem (A * x.neg) D)))

theorem bounded_code_abs (x y : ZT n) (a b : PTm n)
    (hx : Γ ⊢[PRAAx] le (zabs x) a) (hy : Γ ⊢[PRAAx] le (zabs y) b) :
    Γ ⊢[PRAAx] bounded (code x y) (a + b) := by
  have e : Γ ⊢[PRAAx] normSq (code x y) ≐ zabs x * zabs x + zabs y * zabs y := by
    have p := zabs_sq (Γ := Γ) x
    have q := zabs_sq (Γ := Γ) y
    apply deriveNat
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul] at p q ⊢
    rw [normSq_code]
    linear_combination -p - q
  exact le_trans (le_congr e.eqSymm (.eqRefl _)
      (add_le_add₂ (le_mul_mono hx hx) (le_mul_mono hy hy)))
    (le_of_eq_add (d := two * a * b) (by ipra_ring))

theorem eval_rounding_error_re (c D A : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    ZT.toZ Γ (re (roundingError c D A)) = ZT.toZ Γ (remainderCoordinate (re c) D A) := by
  simp only [roundingError, rounded, add, scale, ComplexLogarithmRemainder.neg,
    eval_re_code, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  linear_combination coordinate_error (Γ := Γ) (re c) D A hD

theorem eval_rounding_error_im (c D A : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    ZT.toZ Γ (im (roundingError c D A)) = ZT.toZ Γ (remainderCoordinate (im c) D A) := by
  simp only [roundingError, rounded, add, scale, ComplexLogarithmRemainder.neg,
    eval_im_code, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat]
  linear_combination coordinate_error (Γ := Γ) (im c) D A hD

/-- Gaussian rational-to-dyadic rounding, derived from actual quotient remainders. -/
theorem rounding_bound (c D A : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (roundingError c D A) (two * D) := by
  have h := bounded_code_abs (remainderCoordinate (re c) D A) (remainderCoordinate (im c) D A)
    D D (remainder_bound _ _ _ hD) (remainder_bound _ _ _ hD)
  have e : Γ ⊢[PRAAx] normSq (roundingError c D A) ≐
      normSq (code (remainderCoordinate (re c) D A) (remainderCoordinate (im c) D A)) := by
    apply deriveNat
    rw [normSq_eval, normSq_code, eval_rounding_error_re _ _ _ hD, eval_rounding_error_im _ _ _ hD]
  exact le_congr e.eqSymm (by ipra_ring) h

/-- Variables `0 = c`, `1 = D`, `2 = A`. -/
def roundingFormula : Fm PTm 3 :=
  le one (var 1) ⟶ bounded (roundingError (var 0) (var 1) (var 2)) (two * var 1)

theorem signed_gaussian_quotient_rounding :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 roundingFormula :=
  closeUniv 3 (.impI (rounding_bound _ _ _ Prf.hyp0))

#print axioms signed_gaussian_quotient_rounding

/-! ## Comparing two genuinely rounded rational observations -/

def crossDifference (a b D E : PTm n) : PTm n :=
  add (scale D b) (ComplexLogarithmRemainder.neg (scale E a))

def roundedDifference (a b D E A B : PTm n) : PTm n :=
  add (rounded b E (A * B))
    (ComplexLogarithmRemainder.neg (scale B (rounded a D A)))

def errorDecomposition (a b D E A B : PTm n) : PTm n :=
  add (add (scale D (roundingError b E (A * B)))
      (ComplexLogarithmRemainder.neg (scale (B * E) (roundingError a D A))))
    (scale B (scale A (crossDifference a b D E)))

theorem comparison_identity (a b D E A B : PTm n) :
    Γ ⊢[PRAAx] normSq (scale (D * E) (roundedDifference a b D E A B)) ≐
      normSq (errorDecomposition a b D E A B) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [errorDecomposition, roundedDifference, crossDifference, roundingError,
    add, scale, ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  ring

private alias cancel_positive := Common.mul_cancel_le

theorem cancel_bounded_scale {C a R : PTm n} (hC : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] bounded (scale C a) (C * R)) : Γ ⊢[PRAAx] bounded a R := by
  have s : Γ ⊢[PRAAx] le (C * (C * normSq a)) (C * (C * (R * R))) :=
    le_congr ((ComplexLogarithmRemainder.normSq_scale C a).eqTrans (by ipra_ring))
      (by ipra_ring) h
  exact cancel_positive hC (cancel_positive hC s)

/-- Rounding closeness is derived here from actual quotient observations;
the only approximation premise concerns the exact rational input samples. -/
theorem rounded_comparison (a b D E A B : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hE : Γ ⊢[PRAAx] le one E)
    (hs : Γ ⊢[PRAAx] bounded (scale A (crossDifference a b D E)) (D * E)) :
    Γ ⊢[PRAAx] bounded (roundedDifference a b D E A B) (two + num 3 * B) := by
  have first := bounded_scale D (rounding_bound b E (A * B) hE)
  have second := bounded_neg (bounded_scale (B * E) (rounding_bound a D A hD))
  have third := bounded_scale B hs
  have sum := bounded_add (bounded_add first second) third
  have total : Γ ⊢[PRAAx]
      bounded (scale (D * E) (roundedDifference a b D E A B))
        ((D * E) * (two + num 3 * B)) :=
    le_congr (comparison_identity _ _ _ _ _ _).eqSymm (by ipra_ring) sum
  have positive : Γ ⊢[PRAAx] le one (D * E) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hD hE)
  exact cancel_bounded_scale positive total

/-- Variables `0=a`, `1=b`, `2=D`, `3=E`, `4=A`, `5=B`. -/
def comparisonFormula : Fm PTm 6 :=
  le one (var 2) ⟶ le one (var 3) ⟶
    bounded (scale (var 4) (crossDifference (var 0) (var 1) (var 2) (var 3))) (var 2 * var 3) ⟶
      bounded (roundedDifference (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (two + num 3 * var 5)

theorem genuine_rounded_rational_comparison :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 comparisonFormula :=
  closeUniv 6 (.impI (.impI (.impI (rounded_comparison _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

#print axioms genuine_rounded_rational_comparison

/-! ## The actual primitive-recursive dyadic observations -/

def precision (p : PTm n) : PTm n := p + num 4
def unit (p : PTm n) : PTm n := pw two (precision p)

def observationTerm (p z _R N : PTm n) : PTm n :=
  rounded (series z N (precision p)) (denominator N (precision p)) (unit p)

/-- An actual PR symbol on `p,z,R,N`; `R` supplies the domain certificate and
does not change evaluation of a fixed `z,N` sample. -/
def observationF : PR 4 := PTm.toPR (observationTerm (var 0) (var 1) (var 2) (var 3))

def observation (p z R N : PTm n) : PTm n :=
  ComplexLogarithmCauchy.ap4 observationF p z R N

@[simp] theorem subst_precision {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (precision p) = precision (Syn.subst σ p) := by simp [precision]
@[simp] theorem subst_unit {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (unit p) = unit (Syn.subst σ p) := by simp [unit]
@[simp] theorem subst_observationTerm {m : ℕ} (σ : Fin n → PTm m) (p z R N : PTm n) :
    Syn.subst σ (observationTerm p z R N) =
      observationTerm (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [observationTerm]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R N : PTm n) :
    Syn.subst σ (observation p z R N) =
      observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [observation]

theorem observation_compute (p z R N : PTm n) :
    Γ ⊢[PRAAx] observation p z R N ≐ observationTerm p z R N := by
  have h := toPR_eq (Γ := Γ) (observationTerm (var 0) (var 1) (var 2) (var 3)) ![p, z, R, N]
  simpa [observation, observationF, ComplexLogarithmCauchy.ap4] using h

theorem congr_rounded {c c' D D' A A' : PTm n}
    (hc : Γ ⊢[PRAAx] c ≐ c') (hD : Γ ⊢[PRAAx] D ≐ D') (hA : Γ ⊢[PRAAx] A ≐ A') :
    Γ ⊢[PRAAx] rounded c D A ≐ rounded c' D' A' := by
  have h : Γ ⊢[PRAAx] Syn.subst ![c, D, A] (rounded (var 0) (var 1) (var 2)) ≐
      Syn.subst ![c', D', A'] (rounded (var 0) (var 1) (var 2)) :=
    Prf.eqCongr _ (fun i => by fin_cases i <;> assumption)
  simpa only [subst_rounded, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem congr_add {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] add a b ≐ add a' b' := by
  have h : Γ ⊢[PRAAx] Syn.subst ![a, b] (add (var 0) (var 1)) ≐
      Syn.subst ![a', b'] (add (var 0) (var 1)) :=
    Prf.eqCongr _ (fun i => by fin_cases i <;> assumption)
  simpa only [ComplexLogarithmRemainder.subst_add, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

theorem congr_scale {C a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] scale C a ≐ scale C b := by
  have e : Γ ⊢[PRAAx] Syn.subst ![C, a] (scale (var 0) (var 1)) ≐
      Syn.subst ![C, b] (scale (var 0) (var 1)) :=
    Prf.eqCongr _ (fun i => by fin_cases i; exact .eqRefl _; exact h)
  simpa only [ComplexLogarithmRemainder.subst_scale, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using e

theorem congr_neg {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.neg a ≐ ComplexLogarithmRemainder.neg b := by
  have e := Prf.eqCongr (ComplexLogarithmRemainder.neg (var 0 : PTm 1)) (fun _ => h)
  simpa only [ComplexLogarithmRemainder.subst_neg, Syn.subst_var] using e

theorem precision_add (p k : PTm n) : Γ ⊢[PRAAx] precision (p + k) ≐ precision p + k := by
  unfold precision
  ipra_ring

theorem unit_add (p k : PTm n) : Γ ⊢[PRAAx] unit (p + k) ≐ unit p * pw two k :=
  (congrAp2 powF (precision_add p k) (.eqRefl two)).eqTrans (pw_add two (precision p) k)

theorem observation_later (p k z R N : PTm n) :
    Γ ⊢[PRAAx] observation (p + k) z R N ≐
      rounded (series z N (precision p + k)) (denominator N (precision p + k)) (unit p * pw two k) :=
  (observation_compute _ _ _ _).eqTrans
    (congr_rounded
      (congrAp3 ComplexLogarithmRemainder.seriesF (precision_add p k) (.eqRefl z) (.eqRefl N))
      (ComplexLogarithmCauchy.congr_denominator (precision_add p k)) (unit_add p k))

def discrepancy (p k z R N : PTm n) : PTm n :=
  add (observation (p + k) z R N)
    (ComplexLogarithmRemainder.neg (scale (pw two k) (observation p z R N)))

@[simp] theorem subst_discrepancy {m : ℕ} (σ : Fin n → PTm m) (p k z R N : PTm n) :
    Syn.subst σ (discrepancy p k z R N) = discrepancy (Syn.subst σ p) (Syn.subst σ k)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [discrepancy]

theorem discrepancy_compute (p k z R N : PTm n) :
    Γ ⊢[PRAAx] discrepancy p k z R N ≐
      roundedDifference (series z N (precision p)) (series z N (precision p + k))
        (denominator N (precision p)) (denominator N (precision p + k)) (unit p) (pw two k) :=
  congr_add (observation_later p k z R N)
    (congr_neg (congr_scale (C := pw two k) (observation_compute p z R N)))

theorem regular_bound (p k z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] bounded (discrepancy p k z R N) (two + num 3 * pw two k) := by
  have hD := denominator_positive N (precision p) hN
  have hE := denominator_positive N (precision p + k) hN
  have samples : Γ ⊢[PRAAx]
      bounded (scale (unit p) (crossDifference
        (series z N (precision p)) (series z N (precision p + k))
        (denominator N (precision p)) (denominator N (precision p + k))))
        (denominator N (precision p) * denominator N (precision p + k)) := by
    simpa only [unit, crossDifference, ComplexLogarithmCauchy.difference]
      using ComplexLogarithmCauchy.dyadic_cauchy z N (precision p) R k hz hN hR
  have rounded := rounded_comparison _ _ _ _ _ (pw two k) hD hE samples
  exact le_congr (ComplexLogarithmRemainder.congr_normSq (discrepancy_compute p k z R N)).eqSymm
    (.eqRefl _) rounded

theorem regular_dyadic_bound (p k z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] bounded (discrepancy p k z R N) (num 5 * pw two k) := by
  have h12 : Γ ⊢[PRAAx] le one two := le_of_eq_add (d := one) (by ipra_ring)
  refine bounded_mono (regular_bound p k z R N hN hz hR) ?_
  refine le_of_eq_add (d := two * monus (pw two k) one) ?_
  ipra_lc 2 * natEq (eq_add_of_le (power_positive two k h12))

/-- Variables `0=p`, `1=k`, `2=z`, `3=R`, `4=N`. Each actual observation
represents its coded numerator divided by `2^(p+4)`. -/
def regularFormula : Fm PTm 5 :=
  le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two * var 3) (var 4) ⟶
    (le one (denominator (var 4) (precision (var 0))) ⋏
      (le one (denominator (var 4) (precision (var 0) + var 1)) ⋏
        bounded (discrepancy (var 0) (var 1) (var 2) (var 3) (var 4)) (num 5 * pw two (var 1))))

theorem primitive_recursive_dyadic_log_tail :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 regularFormula := by
  refine closeUniv 5 (.impI (.impI (.impI ?_)))
  exact .andI (denominator_positive _ _ hyp2) (.andI (denominator_positive _ _ hyp2)
    (regular_dyadic_bound _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))

#print axioms primitive_recursive_dyadic_log_tail

/-! ## Ordered precisions and the public observation definition -/

theorem congr_observation {p q : PTm n} (z R N : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] observation p z R N ≐ observation q z R N := by
  apply congrApp observationF
  intro i
  fin_cases i
  · exact h
  · exact .eqRefl _
  · exact .eqRefl _
  · exact .eqRefl _

def endpointDifference (p q z R N : PTm n) : PTm n :=
  add (observation q z R N)
    (ComplexLogarithmRemainder.neg (scale (pw two (monus q p)) (observation p z R N)))

theorem regular_endpoints (p q z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] bounded z R) (hR : Γ ⊢[PRAAx] le (two * R) N)
    (order : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] bounded (endpointDifference p q z R N) (num 5 * pw two (monus q p)) := by
  have e : Γ ⊢[PRAAx] endpointDifference p q z R N ≐ discrepancy p (monus q p) z R N :=
    congr_add (congr_observation z R N (eq_add_of_le order)) (.eqRefl _)
  exact le_congr (ComplexLogarithmRemainder.congr_normSq e).eqSymm (.eqRefl _)
    (regular_dyadic_bound p (monus q p) z R N hN hz hR)

def observationError (p z R N : PTm n) : PTm n :=
  add (scale (denominator N (precision p)) (observation p z R N))
    (ComplexLogarithmRemainder.neg (scale (unit p) (series z N (precision p))))

theorem observation_rounding (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (observationError p z R N) (two * denominator N (precision p)) := by
  have e : Γ ⊢[PRAAx] observationError p z R N ≐
      roundingError (series z N (precision p)) (denominator N (precision p)) (unit p) :=
    congr_add (congr_scale (observation_compute p z R N)) (.eqRefl _)
  exact le_congr (ComplexLogarithmRemainder.congr_normSq e).eqSymm (.eqRefl _)
    (rounding_bound _ _ _ (denominator_positive _ _ hN))

/-- Variables `0=p`, `1=z`, `2=R`, `3=N`. -/
def observationDefinitionFormula : Fm PTm 4 :=
  observation (var 0) (var 1) (var 2) (var 3) ≐
    rounded (series (var 1) (var 3) (precision (var 0)))
      (denominator (var 3) (precision (var 0))) (unit (var 0))

theorem dyadic_observation_definition :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 observationDefinitionFormula :=
  closeUniv 4 (observation_compute _ _ _ _)

/-- Variables `0=p`, `1=z`, `2=R`, `3=N`. -/
def observationRoundingFormula : Fm PTm 4 :=
  le one (var 3) ⟶
    (le one (denominator (var 3) (precision (var 0))) ⋏
      bounded (observationError (var 0) (var 1) (var 2) (var 3))
        (two * denominator (var 3) (precision (var 0))))

theorem dyadic_observation_rounding :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 observationRoundingFormula :=
  closeUniv 4 (.impI (.andI (denominator_positive _ _ Prf.hyp0)
    (observation_rounding _ _ _ _ Prf.hyp0)))

/-- Variables `0=p`, `1=q`, `2=z`, `3=R`, `4=N`. -/
def endpointsFormula : Fm PTm 5 :=
  le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two * var 3) (var 4) ⟶
    le (var 0) (var 1) ⟶
      (le one (denominator (var 4) (precision (var 0))) ⋏
        (le one (denominator (var 4) (precision (var 1))) ⋏
          bounded (endpointDifference (var 0) (var 1) (var 2) (var 3) (var 4))
            (num 5 * pw two (monus (var 1) (var 0)))))

theorem regular_dyadic_log_tail_endpoints :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 endpointsFormula := by
  refine closeUniv 5 (.impI (.impI (.impI (.impI ?_))))
  exact .andI (denominator_positive _ _ hyp2.wk) (.andI (denominator_positive _ _ hyp2.wk)
    (regular_endpoints _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))

#print axioms dyadic_observation_definition
#print axioms dyadic_observation_rounding
#print axioms regular_dyadic_log_tail_endpoints

end LeanProofs.IPRA.Analysis.DyadicComplexLogarithm
