import IPRADerivations.Analysis.Polynomials.PolynomialBisection
import IPRADerivations.Analysis.RationalArithmetic.RationalClosure
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSummableTails
import IPRADerivations.Core.LinearCombination

/-!
# A regular rational name from the actual polynomial bisection

The degree is an arbitrary fixed external natural. Coefficients, their common
denominator and the initial signed rational bracket are internal data. The
samples are the actual left endpoints of `PolynomialBisection.run`, reindexed
by the primitive recursive shift `1 + |R₀-L₀|`.

Nesting and the proved trace width give the regular-name modulus. The
construction uses the actual PR sample programs, positive sample denominators
and arbitrary internal ordered indices. Its premise is the initial bracket,
rather than a Cauchy estimate or an adjacent-motion modulus.

The actual coefficient sum `K = Σ i |c_i| B^(i-1)`, with
`B=1+|R₀-L₀|+|L₀|`, bounds the polynomial divided difference on that box.
The computed query `μ(N)=N+1+|R₀-L₀|K` makes the polynomial residual at the
actual sample at most `2^-N`. Both regularity and residual convergence are
closed ordinary object sentences. Transport to completed-real semantics is
an application adapter.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PolynomialRootName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialBisection
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open LeanProofs.IPRA.Analysis.RationalSummableTails (cross subst_cross)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq zabs_congr zabs_tri zabs_neg subst_zabs)
open LeanProofs.IPRA.Foundations.QuantitativeIdentities (zpow toZ_zpow)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of le_add_ad)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The runtime input contains coefficients, common coefficient denominator,
and the actual initial signed bracket state. -/
def configuration (code C initial : PTm n) : PTm n := pairT code (pairT C initial)
def coefficientCode (x : PTm n) : PTm n := fstT x
def coefficientDenominator (x : PTm n) : PTm n := fstT (sndT x)
def initialState (x : PTm n) : PTm n := sndT (sndT x)

def initialWidth (x : PTm n) : PTm n := zabs (right (initialState x) - left (initialState x))
def offset (x : PTm n) : PTm n := succ (initialWidth x)

/-- The initial sign-bracket contract. The coefficient denominator is needed
only when interpreting polynomial values, not for regularity of the name. -/
def admissible (degree : ℕ) (x : PTm n) : Fm PTm n :=
  bracket degree (coefficientCode x) (initialState x)

def sampleState (degree : ℕ) (k x : PTm n) : PTm n :=
  run degree (k + offset x) (coefficientCode x) (initialState x)
def sampleNumerator (degree : ℕ) (k x : PTm n) : ZT n := left (sampleState degree k x)
def sampleDenominator (degree : ℕ) (k x : PTm n) : PTm n := denominator (sampleState degree k x)

@[simp] theorem subst_coefficientCode {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (coefficientCode x) = coefficientCode (Syn.subst σ x) := by
  simp only [coefficientCode, subst_fstT]

@[simp] theorem subst_coefficientDenominator {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (coefficientDenominator x) = coefficientDenominator (Syn.subst σ x) := by
  simp only [coefficientDenominator, subst_fstT, subst_sndT]

@[simp] theorem subst_initialState {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (initialState x) = initialState (Syn.subst σ x) := by
  simp only [initialState, subst_sndT]

@[simp] theorem subst_initialWidth {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (initialWidth x) = initialWidth (Syn.subst σ x) := by
  simp only [initialWidth, subst_zabs, ZT.subst_sub, subst_right, subst_left, subst_initialState]

@[simp] theorem subst_offset {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (offset x) = offset (Syn.subst σ x) := by
  simp only [offset, ConciseIPRA.PTm.subst_succ, subst_initialWidth]

@[simp] theorem subst_admissible {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (x : PTm n) :
    (admissible degree x).subst σ = admissible degree (Syn.subst σ x) := by
  simp only [admissible, subst_bracket, subst_coefficientCode, subst_initialState]

@[simp] theorem subst_sampleState {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (k x : PTm n) :
    Syn.subst σ (sampleState degree k x) = sampleState degree (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [sampleState, subst_run, PTm.subst_add, subst_offset, subst_coefficientCode, subst_initialState]

@[simp] theorem subst_sampleNumerator {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (k x : PTm n) :
    (sampleNumerator degree k x).subst σ =
      sampleNumerator degree (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [sampleNumerator, subst_left, subst_sampleState]

@[simp] theorem subst_sampleDenominator {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (k x : PTm n) :
    Syn.subst σ (sampleDenominator degree k x) =
      sampleDenominator degree (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [sampleDenominator, subst_denominator, subst_sampleState]

/-- The explicit binary PR programs of the actual rational name. -/
def numeratorPosF (degree : ℕ) : PR 2 := PTm.toPR (sampleNumerator degree (var 0) (var 1)).pos
def numeratorNegF (degree : ℕ) : PR 2 := PTm.toPR (sampleNumerator degree (var 0) (var 1)).neg
def denominatorF (degree : ℕ) : PR 2 := PTm.toPR (sampleDenominator degree (var 0) (var 1))

theorem numeratorPos_at (degree : ℕ) (k x : PTm n) :
    Γ ⊢[PRAAx] ap2 (numeratorPosF degree) k x ≐ (sampleNumerator degree k x).pos := by
  have h := toPR_eq (Γ := Γ) ((sampleNumerator degree (var 0) (var 1)).pos : PTm 2) ![k, x]
  have e := congrArg (fun u : ZT n => u.pos)
    (subst_sampleNumerator ![k, x] degree (var 0 : PTm 2) (var 1))
  simp only [Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] at e
  simpa only [numeratorPosF, ap2, ← e, ZT.subst] using h

theorem numeratorNeg_at (degree : ℕ) (k x : PTm n) :
    Γ ⊢[PRAAx] ap2 (numeratorNegF degree) k x ≐ (sampleNumerator degree k x).neg := by
  have h := toPR_eq (Γ := Γ) ((sampleNumerator degree (var 0) (var 1)).neg : PTm 2) ![k, x]
  have e := congrArg (fun u : ZT n => u.neg)
    (subst_sampleNumerator ![k, x] degree (var 0 : PTm 2) (var 1))
  simp only [Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] at e
  simpa only [numeratorNegF, ap2, ← e, ZT.subst] using h

theorem denominator_at (degree : ℕ) (k x : PTm n) :
    Γ ⊢[PRAAx] ap2 (denominatorF degree) k x ≐ sampleDenominator degree k x := by
  have h := toPR_eq (Γ := Γ) (sampleDenominator degree (var 0) (var 1) : PTm 2) ![k, x]
  simpa only [denominatorF, ap2, subst_sampleDenominator, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem sample_bracket (degree : ℕ) (k x : PTm n) (h : Γ ⊢[PRAAx] admissible degree x) :
    Γ ⊢[PRAAx] bracket degree (coefficientCode x) (sampleState degree k x) :=
  run_bracket degree _ _ _ h

theorem sample_denominator_positive (degree : ℕ) (k x : PTm n)
    (h : Γ ⊢[PRAAx] admissible degree x) :
    Γ ⊢[PRAAx] le one (sampleDenominator degree k x) := Prf.andE₁ (sample_bracket degree k x h)

/-- The actual initial width is covered by the explicit dyadic shift. -/
theorem offset_budget (x : PTm n) : Γ ⊢[PRAAx] le (initialWidth x) (pw two (offset x)) :=
  le_trans (le_trans (le_succ_self _) (le_succ_self _)) (succ_le_two_pow (offset x))

/-- Every sample denominator covers the initial numerator width at its precision. -/
theorem sample_width_budget (degree : ℕ) (k x : PTm n)
    (h : Γ ⊢[PRAAx] admissible degree x) :
    Γ ⊢[PRAAx] le (pw two k * initialWidth x) (sampleDenominator degree k x) := by
  have initialDen : Γ ⊢[PRAAx] le one (denominator (initialState x)) := Prf.andE₁ h
  have scaled : Γ ⊢[PRAAx] le (initialWidth x)
      (denominator (initialState x) * pw two (offset x)) :=
    le_congr (one_mul _) (.eqRefl _) (le_mul_mono initialDen (offset_budget x))
  have multiplied := mul_le_mul_right (pw two k) scaled
  have powers := pw_add (Γ := Γ) two k (offset x)
  have den := run_denominator (Γ := Γ) degree (k + offset x) (coefficientCode x) (initialState x)
  exact le_congr (mul_comm _ _)
    ((by ipra_ring : Γ ⊢[PRAAx]
      denominator (initialState x) * pw two (offset x) * pw two k ≐
        denominator (initialState x) * (pw two k * pw two (offset x))).eqTrans
      ((congrMul (.eqRefl _) powers.eqSymm).eqTrans den.eqSymm)) multiplied

/-- A signed integer is below its natural absolute value. -/
theorem signed_le_abs (u : ZT n) :
    Γ ⊢[PRAAx] zle u (ZT.ofNat (zabs u)) := by
  have h := le_add_ad (Γ := Γ) u.pos u.neg
  exact le_congr (LeanProofs.IPRA.add_zero u.pos).eqSymm
    (LeanProofs.IPRA.add_comm u.neg (zabs u)) h

/-- A nonnegative signed integer below the natural bound has that absolute bound. -/
theorem abs_le_of_nonnegative {u : ZT n} {B : PTm n}
    (hlo : Γ ⊢[PRAAx] zle (ZT.natLit 0) u)
    (hhi : Γ ⊢[PRAAx] zle u (ZT.ofNat B)) :
    Γ ⊢[PRAAx] le (zabs u) B := by
  have upper : Γ ⊢[PRAAx] le u.pos (u.neg + B) :=
    le_congr (LeanProofs.IPRA.add_zero u.pos) (LeanProofs.IPRA.add_comm B u.neg) hhi
  have lower : Γ ⊢[PRAAx] le u.neg u.pos :=
    le_congr (LeanProofs.IPRA.zero_add u.neg) (LeanProofs.IPRA.add_zero u.pos) hlo
  exact ad_le_of upper (le_trans lower (le_add_right u.pos B))

/-- Exact rational interval containment implies a discrepancy bound relative
to the left endpoint, with no denominator-positivity premise required for
this polynomial inequality. -/
theorem rational_interval_discrepancy (L R A : ZT n) (d t : PTm n)
    (hlo : Γ ⊢[PRAAx] zle (ZT.ofNat t * L) A)
    (hhi : Γ ⊢[PRAAx] zle A (ZT.ofNat t * R)) :
    Γ ⊢[PRAAx] le (zabs (A * ZT.ofNat d - L * ZT.ofNat (t * d)))
      ((t * d) * zabs (R - L)) := by
  let X := A * ZT.ofNat d - L * ZT.ofNat (t * d)
  have lower : Γ ⊢[PRAAx] zle (ZT.natLit 0) X := by
    have H := zle_toZ hlo
    apply zle_of_toZ (d * slack (ZT.ofNat t * L) A)
    dsimp only [X, slack]
    ipra_simps
    linear_combination Groth.ι (Q.mk Γ d) * H
  have upper : Γ ⊢[PRAAx] zle X (ZT.ofNat (t * d) * (R - L)) := by
    have H := zle_toZ hhi
    apply zle_of_toZ (d * slack A (ZT.ofNat t * R))
    dsimp only [X, slack]
    ipra_simps
    linear_combination Groth.ι (Q.mk Γ d) * H
  have width := zle_scale (t * d) (signed_le_abs (Γ := Γ) (R - L))
  have bound : Γ ⊢[PRAAx] zle X (ZT.ofNat ((t * d) * zabs (R - L))) := by
    refine zle_congr rfl ?_ (zle_trans upper width)
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
  exact abs_le_of_nonnegative lower bound

private theorem left_value_congr {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    ZT.toZ Γ (left s) = ZT.toZ Γ (left t) := by
  simp only [left, unpack, ZT.toZ]
  rw [natEq (congrFst (congrFst h)), natEq (congrSnd (congrFst h))]

private theorem denominator_congr {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] denominator s ≐ denominator t := congrSnd (congrSnd h)

def intervalDifference (s t : PTm n) : ZT n := cross (left s) (left t) (denominator s) (denominator t)

private theorem intervalDifference_congr {s t u : PTm n} (h : Γ ⊢[PRAAx] t ≐ u) :
    Γ ⊢[PRAAx] zabs (intervalDifference s t) ≐ zabs (intervalDifference s u) := by
  apply zabs_congr
  simp only [intervalDifference, cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]
  rw [left_value_congr h, natEq (denominator_congr h)]

/-- The actual denominator ratio over any finite suffix of the PR run. -/
theorem trace_denominator_ratio (degree : ℕ) (N r code initial : PTm n) :
    Γ ⊢[PRAAx] denominator (run degree (N + r) code initial) ≐
      pw two r * denominator (run degree N code initial) :=
  (denominator_congr (run_add degree N r code initial)).eqTrans
    ((run_denominator degree r code (run degree N code initial)).eqTrans (mul_comm _ _))

/-- Derived discrepancy bound from actual nested trace intervals and their width. -/
theorem trace_discrepancy_window (degree : ℕ) (N r code initial : PTm n)
    (h : Γ ⊢[PRAAx] bracket degree code initial) :
    Γ ⊢[PRAAx] le
      (zabs (intervalDifference (run degree N code initial) (run degree (N + r) code initial)))
      (zabs (right initial - left initial) * denominator (run degree (N + r) code initial)) := by
  let s := run degree N code initial
  let t := run degree (N + r) code initial
  have nesting := nested_window degree N r code initial h
  have laterBracket := run_bracket degree (N + r) code initial h
  have raw := rational_interval_discrepancy (left s) (right s) (left t) (denominator s) (pw two r)
    (Prf.andE₁ nesting) (zle_trans (Prf.andE₁ (Prf.andE₂ laterBracket)) (Prf.andE₂ nesting))
  have ratio := trace_denominator_ratio (Γ := Γ) degree N r code initial
  have width := zabs_congr (ZT.toZ_eq (run_width (Γ := Γ) degree N code initial))
  have same : ZT.toZ Γ (intervalDifference s t) =
      ZT.toZ Γ (left t * ZT.ofNat (denominator s) -
        left s * ZT.ofNat (pw two r * denominator s)) := by
    simp only [intervalDifference, cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]
    rw [natEq ratio]
  exact le_congr (zabs_congr same).eqSymm
    ((congrMul ratio.eqSymm width).eqTrans (mul_comm _ _)) raw

theorem trace_discrepancy_between (degree : ℕ) (code initial : PTm n) {N M : PTm n}
    (h : Γ ⊢[PRAAx] bracket degree code initial) (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le
      (zabs (intervalDifference (run degree N code initial) (run degree M code initial)))
      (zabs (right initial - left initial) * denominator (run degree M code initial)) := by
  have index : Γ ⊢[PRAAx] N + PTm.monus M N ≐ M := (eq_add_of_le order).eqSymm
  have same : Γ ⊢[PRAAx] run degree (N + PTm.monus M N) code initial ≐ run degree M code initial :=
    congrAp2 (Foundations.TraceInvariant.runF (updateTerm degree)) index (.eqRefl _)
  exact le_congr (intervalDifference_congr same)
    (congrMul (.eqRefl _) (denominator_congr same))
    (trace_discrepancy_window degree N (PTm.monus M N) code initial h)

def sampleDifference (degree : ℕ) (N M x : PTm n) : ZT n :=
  cross (sampleNumerator degree N x) (sampleNumerator degree M x)
    (sampleDenominator degree N x) (sampleDenominator degree M x)

theorem sample_interval_bound (degree : ℕ) (x : PTm n) {N M : PTm n}
    (h : Γ ⊢[PRAAx] admissible degree x) (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (zabs (sampleDifference degree N M x))
      (initialWidth x * sampleDenominator degree M x) :=
  trace_discrepancy_between degree (coefficientCode x) (initialState x) h
    (add_le_add_right (offset x) order)

/-- The actual reindexed rational samples satisfy the explicit modulus `N↦N`. -/
theorem regular_between (degree : ℕ) (x : PTm n) {N M : PTm n}
    (h : Γ ⊢[PRAAx] admissible degree x) (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (pw two N * zabs (sampleDifference degree N M x))
      (sampleDenominator degree N x * sampleDenominator degree M x) := by
  have first : Γ ⊢[PRAAx] le (pw two N * zabs (sampleDifference degree N M x))
      ((pw two N * initialWidth x) * sampleDenominator degree M x) :=
    le_congr (mul_comm _ _) (by ipra_ring)
      (mul_le_mul_right (pw two N) (sample_interval_bound degree x h order))
  exact le_trans first (mul_le_mul_right (sampleDenominator degree M x) (sample_width_budget degree N x h))

/-- The rational name is given by literal binary primitive-recursive symbols. -/
def programNumerator (degree : ℕ) (k x : PTm n) : ZT n :=
  ⟨ap2 (numeratorPosF degree) k x, ap2 (numeratorNegF degree) k x⟩

private theorem programNumerator_value (degree : ℕ) (k x : PTm n) :
    ZT.toZ Γ (programNumerator degree k x) = ZT.toZ Γ (sampleNumerator degree k x) := by
  simp only [programNumerator, ZT.toZ]
  rw [natEq (numeratorPos_at (Γ := Γ) degree k x), natEq (numeratorNeg_at (Γ := Γ) degree k x)]

def programDifference (degree : ℕ) (N M x : PTm n) : ZT n :=
  cross (programNumerator degree N x) (programNumerator degree M x)
    (ap2 (denominatorF degree) N x) (ap2 (denominatorF degree) M x)

theorem regular_program_between (degree : ℕ) (x : PTm n) {N M : PTm n}
    (h : Γ ⊢[PRAAx] admissible degree x) (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (pw two N * zabs (programDifference degree N M x))
      (ap2 (denominatorF degree) N x * ap2 (denominatorF degree) M x) := by
  have same : ZT.toZ Γ (programDifference degree N M x) = ZT.toZ Γ (sampleDifference degree N M x) := by
    simp only [programDifference, sampleDifference, cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat,
      programNumerator_value, natEq (denominator_at (Γ := Γ) degree N x),
      natEq (denominator_at (Γ := Γ) degree M x)]
  exact le_congr (congrMul (.eqRefl _) (zabs_congr same).eqSymm)
    (congrMul (denominator_at degree N x).eqSymm (denominator_at degree M x).eqSymm)
    (regular_between degree x h order)

/-- The exact trace linkage and denominator positivity for the actual sample programs. -/
def programsFormula (degree : ℕ) : Fm PTm 2 :=
  admissible degree (var 1) ⟶
    ((ap2 (numeratorPosF degree) (var 0) (var 1) ≐ (sampleNumerator degree (var 0) (var 1)).pos) ⋏
     (ap2 (numeratorNegF degree) (var 0) (var 1) ≐ (sampleNumerator degree (var 0) (var 1)).neg) ⋏
     (ap2 (denominatorF degree) (var 0) (var 1) ≐ sampleDenominator degree (var 0) (var 1)) ⋏
     le one (ap2 (denominatorF degree) (var 0) (var 1)))

theorem sample_programs (degree : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (programsFormula degree) := by
  refine closeUniv 2 (.impI (.andI (numeratorPos_at degree _ _) (.andI (numeratorNeg_at degree _ _)
    (.andI (denominator_at degree _ _) ?_))))
  exact le_congr (.eqRefl _) (denominator_at degree _ _).eqSymm
    (sample_denominator_positive degree _ _ Prf.hyp0)

/-- Variables `0=N`, `1=M`, `2=runtime polynomial/bracket data`. -/
def regularFormula (degree : ℕ) : Fm PTm 3 :=
  admissible degree (var 2) ⟶ le (var 0) (var 1) ⟶
    (le one (ap2 (denominatorF degree) (var 0) (var 2)) ⋏
     le one (ap2 (denominatorF degree) (var 1) (var 2)) ⋏
     le (pw two (var 0) * zabs (programDifference degree (var 0) (var 1) (var 2)))
      (ap2 (denominatorF degree) (var 0) (var 2) * ap2 (denominatorF degree) (var 1) (var 2)))

theorem regular_name (degree : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (regularFormula degree) := by
  refine closeUniv 3 (.impI (.impI (.andI ?_ (.andI ?_ ?_))))
  · exact le_congr (.eqRefl _) (denominator_at degree _ _).eqSymm
      (sample_denominator_positive degree (var 0) (var 2) Prf.hyp1)
  · exact le_congr (.eqRefl _) (denominator_at degree _ _).eqSymm
      (sample_denominator_positive degree (var 1) (var 2) Prf.hyp1)
  · exact regular_program_between degree (var 2) Prf.hyp1 Prf.hyp0

#print axioms sample_width_budget
#print axioms trace_discrepancy_window
#print axioms regular_between
#print axioms regular_program_between
#print axioms sample_programs
#print axioms regular_name

theorem abs_ofNat (a : PTm n) : Γ ⊢[PRAAx] zabs (ZT.ofNat a) ≐ a :=
  (congrAdd (monus_zero a) (zero_monus a)).eqTrans (LeanProofs.IPRA.add_zero a)

/-- Exact multiplicativity of the signed absolute-value code. -/
theorem abs_mul (u v : ZT n) :
    Γ ⊢[PRAAx] zabs (u * v) ≐ zabs u * zabs v := by
  have square : Γ ⊢[PRAAx]
      zabs (u * v) * zabs (u * v) ≐ (zabs u * zabs v) * (zabs u * zabs v) := by
    apply deriveNat
    calc
      Groth.ι (Q.mk Γ (zabs (u * v) * zabs (u * v))) =
          ZT.toZ Γ (u * v) * ZT.toZ Γ (u * v) := zabs_sq (u * v)
      _ = (ZT.toZ Γ u * ZT.toZ Γ u) * (ZT.toZ Γ v * ZT.toZ Γ v) := by
        rw [ZT.toZ_mul]
        ring
      _ = Groth.ι (Q.mk Γ (zabs u * zabs u)) *
          Groth.ι (Q.mk Γ (zabs v * zabs v)) := by
        rw [zabs_sq u, zabs_sq v]
      _ = Groth.ι (Q.mk Γ ((zabs u * zabs v) * (zabs u * zabs v))) := by
        simp only [Q.mk_mul, map_mul]
        ring
  exact le_antisymm
    (nat_sqrt_mono (le_congr (.eqRefl _) square (le_refl _)))
    (nat_sqrt_mono (le_congr (.eqRefl _) square.eqSymm (le_refl _)))

theorem abs_scale (c : PTm n) (u : ZT n) :
    Γ ⊢[PRAAx] zabs (ZT.ofNat c * u) ≐ c * zabs u :=
  (abs_mul (ZT.ofNat c) u).eqTrans (congrMul (abs_ofNat c) (.eqRefl _))

private theorem toZ_naturalPower (a : PTm n) (k : ℕ) :
    Groth.ι (Q.mk Γ (naturalPower a k)) = Groth.ι (Q.mk Γ a) ^ k := by
  induction k with
  | zero => simp [naturalPower, one]
  | succ k ih => simp only [naturalPower, Q.mk_mul, map_mul, ih, pow_succ]

theorem naturalPower_product (a b : PTm n) (k : ℕ) :
    Γ ⊢[PRAAx] naturalPower (a * b) k ≐ naturalPower a k * naturalPower b k := by
  apply deriveNat
  simp only [Q.mk_mul, map_mul, toZ_naturalPower, mul_pow]

theorem naturalPower_mono (k : ℕ) {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (naturalPower a k) (naturalPower b k) := by
  induction k with
  | zero => exact le_refl one
  | succ k ih => exact le_mul_mono ih h

theorem power_abs_bound (k : ℕ) (u : ZT n) (B : PTm n)
    (h : Γ ⊢[PRAAx] le (zabs u) B) :
    Γ ⊢[PRAAx] le (zabs (zpow u k)) (naturalPower B k) := by
  induction k with
  | zero => exact le_congr (abs_ofNat one).eqSymm (.eqRefl _) (le_refl one)
  | succ k ih => exact le_congr (abs_mul (zpow u k) u).eqSymm (.eqRefl _) (le_mul_mono ih h)

/-- Exact divided difference of a fixed power. -/
theorem powerFactor_identity (k : ℕ) (u v : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((u - v) * powerFactor k u v) (zpow u k - zpow v k) := by
  induction k with
  | zero =>
    ipra_lc [powerFactor, zpow]
  | succ k ih =>
    ipra_lc [powerFactor, zpow] ZT.toZ Γ v * ZT.toZ_eq ih

/-- The actual power divided difference has the computed coefficient bound. -/
theorem powerFactor_bound (k : ℕ) (u v : ZT n) (B : PTm n)
    (hu : Γ ⊢[PRAAx] le (zabs u) B) (hv : Γ ⊢[PRAAx] le (zabs v) B) :
    Γ ⊢[PRAAx] le (zabs (powerFactor (k + 1) u v)) (num (k + 1) * naturalPower B k) := by
  induction k with
  | zero =>
    have val : ZT.toZ Γ (powerFactor 1 u v) = ZT.toZ Γ (ZT.ofNat one) := by
      simp only [powerFactor, zpow, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, ZT.toZ_ofNat]
      simp
    have absolute := (zabs_congr val).eqTrans (abs_ofNat one)
    exact le_congr absolute.eqSymm (one_mul one).eqSymm (le_refl one)
  | succ k ih =>
    have triangle : Γ ⊢[PRAAx] le (zabs (powerFactor (k + 1 + 1) u v))
        (zabs (zpow u (k + 1)) + zabs (v * powerFactor (k + 1) u v)) :=
      zabs_tri (by simp only [powerFactor, ZT.toZ_add])
    have product : Γ ⊢[PRAAx] le (zabs (v * powerFactor (k + 1) u v))
        (B * (num (k + 1) * naturalPower B k)) :=
      le_congr (abs_mul v _).eqSymm (.eqRefl _) (le_mul_mono hv ih)
    have sum := add_le_add₂ (power_abs_bound (k + 1) u B hu) product
    have algebra : Γ ⊢[PRAAx]
        naturalPower B (k + 1) + B * (num (k + 1) * naturalPower B k) ≐
          num (k + 1 + 1) * naturalPower B (k + 1) := by
      change Γ ⊢[PRAAx] (naturalPower B k * B) + B * (num (k + 1) * naturalPower B k) ≐
        succ (num (k + 1)) * (naturalPower B k * B)
      ipra_ring
    exact le_trans triangle (le_congr (.eqRefl _) algebra sum)

/-- Same-denominator factor, avoiding unnecessary denominator powers. -/
def sameDenFactor : ℕ → PTm n → ZT n → ZT n → PTm n → ZT n
  | 0, _, _, _, _ => ZT.natLit 0
  | k + 1, code, L, R, D =>
      ZT.ofNat D * sameDenFactor k code L R D +
        coefficient code (k + 1) * powerFactor (k + 1) R L

theorem sameDenFactor_identity (k : ℕ) (code : PTm n) (L R : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (evaluate k code R D - evaluate k code L D)
      ((R - L) * sameDenFactor k code L R D) := by
  induction k with
  | zero =>
    ipra_lc [evaluate, sameDenFactor]
  | succ k ih =>
    ipra_lc [evaluate, sameDenFactor] Groth.ι (Q.mk Γ D) * ZT.toZ_eq ih -
      ZT.toZ Γ (coefficient code (k + 1)) * ZT.toZ_eq (powerFactor_identity (Γ := Γ) (k + 1) R L)

/-- The computed Lipschitz numerator from the actual signed coefficients. -/
def coefficientBound : ℕ → PTm n → PTm n → PTm n
  | 0, _, _ => zero
  | k + 1, code, B => coefficientBound k code B +
      num (k + 1) * zabs (coefficient code (k + 1)) * naturalPower B k

/-- The actual same-denominator factor is bounded by a computed coefficient
sum. This degree-successor formulation includes the degree-one base and
requires no positivity of `B` or `D`. -/
theorem sameDenFactor_bound (k : ℕ) (code : PTm n) (L R : ZT n) (B D : PTm n)
    (hL : Γ ⊢[PRAAx] le (zabs L) (B * D))
    (hR : Γ ⊢[PRAAx] le (zabs R) (B * D)) :
    Γ ⊢[PRAAx] le (zabs (sameDenFactor (k + 1) code L R D))
      (coefficientBound (k + 1) code B * naturalPower D k) := by
  induction k with
  | zero =>
    have val : ZT.toZ Γ (sameDenFactor 1 code L R D) =
        ZT.toZ Γ (coefficient code 1) := by
      simp only [sameDenFactor, powerFactor, zpow, ZT.toZ_add, ZT.toZ_mul,
        ZT.toZ_ofNat, ZT.toZ_natLit]
      ring
    have algebra : Γ ⊢[PRAAx]
        coefficientBound 1 code B * naturalPower D 0 ≐ zabs (coefficient code 1) := by
      change Γ ⊢[PRAAx]
        (zero + one * zabs (coefficient code 1) * one) * one ≐ zabs (coefficient code 1)
      ipra_ring
    exact le_congr (zabs_congr val).eqSymm algebra.eqSymm (le_refl _)
  | succ k ih =>
    have triangle : Γ ⊢[PRAAx] le (zabs (sameDenFactor (k + 1 + 1) code L R D))
        (zabs (ZT.ofNat D * sameDenFactor (k + 1) code L R D) +
          zabs (coefficient code (k + 1 + 1) * powerFactor (k + 1 + 1) R L)) :=
      zabs_tri (by simp only [sameDenFactor, ZT.toZ_add])
    have old : Γ ⊢[PRAAx] le (zabs (ZT.ofNat D * sameDenFactor (k + 1) code L R D))
        (D * (coefficientBound (k + 1) code B * naturalPower D k)) :=
      le_congr (abs_scale D _).eqSymm (.eqRefl _) (le_mul_mono (le_refl D) ih)
    have powers := powerFactor_bound (k + 1) R L (B * D) hR hL
    have next : Γ ⊢[PRAAx] le
        (zabs (coefficient code (k + 1 + 1) * powerFactor (k + 1 + 1) R L))
        (zabs (coefficient code (k + 1 + 1)) *
          (num (k + 1 + 1) * (naturalPower B (k + 1) * naturalPower D (k + 1)))) :=
      le_congr (abs_mul _ _).eqSymm
        (congrMul (.eqRefl _) (congrMul (.eqRefl _) (naturalPower_product B D (k + 1))))
        (le_mul_mono (le_refl _) powers)
    have algebra : Γ ⊢[PRAAx]
        D * (coefficientBound (k + 1) code B * naturalPower D k) +
          zabs (coefficient code (k + 1 + 1)) *
            (num (k + 1 + 1) * (naturalPower B (k + 1) * naturalPower D (k + 1))) ≐
          coefficientBound (k + 1 + 1) code B * naturalPower D (k + 1) := by
      change Γ ⊢[PRAAx]
        D * (coefficientBound (k + 1) code B * naturalPower D k) +
          zabs (coefficient code (k + 1 + 1)) *
            (num (k + 1 + 1) * (naturalPower B (k + 1) * (naturalPower D k * D))) ≐
          (coefficientBound (k + 1) code B +
            num (k + 1 + 1) * zabs (coefficient code (k + 1 + 1)) * naturalPower B (k + 1)) *
              (naturalPower D k * D)
      ipra_ring
    exact le_trans triangle (le_congr (.eqRefl _) algebra (add_le_add₂ old next))

/-- A fixed rational polynomial has the actual computed Lipschitz numerator
on the supplied bounded box. -/
theorem polynomial_difference_bound (k : ℕ) (code : PTm n) (L R : ZT n) (B D : PTm n)
    (hL : Γ ⊢[PRAAx] le (zabs L) (B * D))
    (hR : Γ ⊢[PRAAx] le (zabs R) (B * D)) :
    Γ ⊢[PRAAx] le (zabs (evaluate (k + 1) code R D - evaluate (k + 1) code L D))
      (zabs (R - L) * coefficientBound (k + 1) code B * naturalPower D k) := by
  have identity := zabs_congr (ZT.toZ_eq (sameDenFactor_identity (Γ := Γ) (k + 1) code L R D))
  have absolute := identity.eqTrans (abs_mul (R - L) (sameDenFactor (k + 1) code L R D))
  exact le_congr absolute.eqSymm (by ipra_ring)
    (le_mul_mono (le_refl (zabs (R - L))) (sameDenFactor_bound k code L R B D hL hR))

/-- A computed bound for every rational point of the initial interval. -/
def boxBound (x : PTm n) : PTm n :=
  succ (initialWidth x + zabs (left (initialState x)))

/-- Absolute numerators of points in a scaled interval have a computed bound. -/
theorem interval_absolute_bound (L R A : ZT n) (t : PTm n)
    (hlo : Γ ⊢[PRAAx] zle (ZT.ofNat t * L) A)
    (hhi : Γ ⊢[PRAAx] zle A (ZT.ofNat t * R)) :
    Γ ⊢[PRAAx] le (zabs A) (t * (zabs (R - L) + zabs L)) := by
  have raw := rational_interval_discrepancy L R A one t hlo hhi
  have difference : ZT.toZ Γ (A * ZT.ofNat one - L * ZT.ofNat (t * one)) =
      ZT.toZ Γ (A - ZT.ofNat t * L) := by
    simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul, Q.mk_one, map_one]
    ring
  have gap : Γ ⊢[PRAAx] le (zabs (A - ZT.ofNat t * L)) (t * zabs (R - L)) :=
    le_congr (zabs_congr difference) (by ipra_ring) raw
  have triangle : Γ ⊢[PRAAx] le (zabs A)
      (zabs (A - ZT.ofNat t * L) + zabs (ZT.ofNat t * L)) :=
    zabs_tri (by simp only [ZT.toZ_sub, ZT.toZ_add]; ring)
  have scaled : Γ ⊢[PRAAx] le (zabs (ZT.ofNat t * L)) (t * zabs L) :=
    le_congr (abs_scale t L).eqSymm (.eqRefl _) (le_refl _)
  exact le_trans triangle (le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ gap scaled))

/-- Both actual bracket endpoints stay in the explicitly bounded rational box. -/
theorem trace_magnitude_bounds (degree : ℕ) (k x : PTm n)
    (h : Γ ⊢[PRAAx] admissible degree x) :
    Γ ⊢[PRAAx]
      le (zabs (left (run degree k (coefficientCode x) (initialState x))))
        (boxBound x * denominator (run degree k (coefficientCode x) (initialState x))) ⋏
      le (zabs (right (run degree k (coefficientCode x) (initialState x))))
        (boxBound x * denominator (run degree k (coefficientCode x) (initialState x))) := by
  let s := run degree k (coefficientCode x) (initialState x)
  have hb := run_bracket degree k (coefficientCode x) (initialState x) h
  have hn := run_nested degree k (coefficientCode x) (initialState x) h
  have order := Prf.andE₁ (Prf.andE₂ hb)
  have leftBound := interval_absolute_bound (left (initialState x)) (right (initialState x)) (left s) (pw two k)
    (Prf.andE₁ hn) (zle_trans order (Prf.andE₂ hn))
  have rightBound := interval_absolute_bound (left (initialState x)) (right (initialState x)) (right s) (pw two k)
    (zle_trans (Prf.andE₁ hn) order) (Prf.andE₂ hn)
  have denLower : Γ ⊢[PRAAx] le (pw two k) (denominator s) :=
    le_congr (one_mul _) (run_denominator degree k (coefficientCode x) (initialState x)).eqSymm
      (le_mul_mono (Prf.andE₁ h) (le_refl _))
  have common : Γ ⊢[PRAAx] le
      (pw two k * (initialWidth x + zabs (left (initialState x)))) (boxBound x * denominator s) :=
    le_congr (mul_comm _ _) (.eqRefl _) (le_mul_mono (le_succ_self _) denLower)
  exact .andI (le_trans leftBound common) (le_trans rightBound common)

/-- Opposite endpoint signs bound the left residual by their actual difference. -/
theorem sign_residual_bound (P Q : ZT n)
    (hP : Γ ⊢[PRAAx] zle P (ZT.natLit 0))
    (hQ : Γ ⊢[PRAAx] zle (ZT.natLit 0) Q) :
    Γ ⊢[PRAAx] le (zabs P) (zabs (Q - P)) := by
  have lower : Γ ⊢[PRAAx] zle (ZT.ofNat one * P) (ZT.natLit 0) :=
    zle_congr (by simp [ZT.toZ_mul, ZT.toZ_ofNat, IPRA.Q.mk_one]) rfl hP
  have upper : Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.ofNat one * Q) :=
    zle_congr rfl (by simp [ZT.toZ_mul, ZT.toZ_ofNat, IPRA.Q.mk_one]) hQ
  have raw := rational_interval_discrepancy P Q (ZT.natLit 0) one one lower upper
  have opposite : ZT.toZ Γ
      (ZT.natLit 0 * ZT.ofNat one - P * ZT.ofNat (one * one)) = ZT.toZ Γ (-P) := by
    simp [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, IPRA.Q.mk_one]
  exact le_congr ((zabs_congr opposite).eqTrans (zabs_neg P)) (by ipra_ring) raw

/-- The computed product of interval width and coefficient Lipschitz numerator. -/
def errorBudget (degree : ℕ) (x : PTm n) : PTm n :=
  initialWidth x * coefficientBound degree (coefficientCode x) (boxBound x)

/-- The genuine polynomial residual bound on the actual PR trace.
For degree `d+1`, its denominator is `C * D^(d+1)`. -/
theorem trace_residual_bound (d : ℕ) (k x : PTm n)
    (h : Γ ⊢[PRAAx] admissible (d + 1) x) :
    Γ ⊢[PRAAx] le
      (zabs (evaluate (d + 1) (coefficientCode x)
        (left (run (d + 1) k (coefficientCode x) (initialState x)))
        (denominator (run (d + 1) k (coefficientCode x) (initialState x)))))
      (errorBudget (d + 1) x * naturalPower
        (denominator (run (d + 1) k (coefficientCode x) (initialState x))) d) := by
  let s := run (d + 1) k (coefficientCode x) (initialState x)
  have hb := run_bracket (d + 1) k (coefficientCode x) (initialState x) h
  have hm := trace_magnitude_bounds (d + 1) k x h
  have signs := sign_residual_bound
    (evaluate (d + 1) (coefficientCode x) (left s) (denominator s))
    (evaluate (d + 1) (coefficientCode x) (right s) (denominator s))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hb))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hb)))
  have difference := polynomial_difference_bound d (coefficientCode x) (left s) (right s)
    (boxBound x) (denominator s) (Prf.andE₁ hm) (Prf.andE₂ hm)
  have width := zabs_congr (ZT.toZ_eq
    (run_width (Γ := Γ) (d + 1) k (coefficientCode x) (initialState x)))
  exact le_trans signs (le_congr (.eqRefl _)
    (congrMul (congrMul width (.eqRefl _)) (.eqRefl _)) difference)

#print axioms abs_mul
#print axioms sameDenFactor_identity
#print axioms sameDenFactor_bound
#print axioms polynomial_difference_bound
#print axioms trace_magnitude_bounds
#print axioms trace_residual_bound

/-- A safe explicit polynomial-residual query, computed from the actual coefficients. -/
def residualSchedule (degree : ℕ) (N x : PTm n) : PTm n := N + succ (errorBudget degree x)

theorem residualSchedule_ge (degree : ℕ) (N x : PTm n) :
    Γ ⊢[PRAAx] le N (residualSchedule degree N x) := le_add_right _ _

private theorem one_le_two_power (k : PTm n) : Γ ⊢[PRAAx] le one (pw two k) :=
  le_trans (le_of_eq_add (d := k) (by ipra_ring)) (succ_le_two_pow k)

/-- The actual trace denominator at `N+1+V` covers any supplied natural budget V. -/
theorem run_natural_budget (degree : ℕ) (N V code initial : PTm n)
    (hD : Γ ⊢[PRAAx] le one (denominator initial)) :
    Γ ⊢[PRAAx] le (pw two N * V) (denominator (run degree (N + succ V) code initial)) := by
  have exponential : Γ ⊢[PRAAx] le V (pw two (succ V)) :=
    le_trans (le_trans (le_succ_self V) (le_succ_self (succ V))) (succ_le_two_pow (succ V))
  have base : Γ ⊢[PRAAx] le V (denominator initial * pw two (succ V)) :=
    le_congr (one_mul V) (.eqRefl _) (le_mul_mono hD exponential)
  have multiplied := mul_le_mul_right (pw two N) base
  have powers := pw_add (Γ := Γ) two N (succ V)
  have den := run_denominator (Γ := Γ) degree (N + succ V) code initial
  exact le_congr (mul_comm _ _)
    ((by ipra_ring : Γ ⊢[PRAAx]
      denominator initial * pw two (succ V) * pw two N ≐
        denominator initial * (pw two N * pw two (succ V))).eqTrans
      ((congrMul (.eqRefl _) powers.eqSymm).eqTrans den.eqSymm)) multiplied

/-- The residual schedule also accounts for the name's original width shift. -/
theorem residual_width_budget (degree : ℕ) (N x : PTm n)
    (h : Γ ⊢[PRAAx] admissible degree x)
    (hC : Γ ⊢[PRAAx] le one (coefficientDenominator x)) :
    Γ ⊢[PRAAx] le (pw two N * errorBudget degree x)
      (coefficientDenominator x * sampleDenominator degree (residualSchedule degree N x) x) := by
  let μ := residualSchedule degree N x
  let s := run degree μ (coefficientCode x) (initialState x)
  have firstBudget := run_natural_budget degree N (errorBudget degree x) (coefficientCode x) (initialState x) (Prf.andE₁ h)
  have ratio := trace_denominator_ratio (Γ := Γ) degree μ (offset x) (coefficientCode x) (initialState x)
  have later : Γ ⊢[PRAAx] le (denominator s) (sampleDenominator degree μ x) :=
    le_congr (one_mul _) ratio.eqSymm (le_mul_mono (one_le_two_power (offset x)) (le_refl _))
  have coefficient : Γ ⊢[PRAAx] le (sampleDenominator degree μ x)
      (coefficientDenominator x * sampleDenominator degree μ x) :=
    le_congr (one_mul _) (.eqRefl _) (le_mul_mono hC (le_refl _))
  exact le_trans firstBudget (le_trans later coefficient)

/-- Actual polynomial residual convergence with an explicit PR query schedule.
The degree-zero branch follows from the two initial signs and has zero residual. -/
theorem residual_bound (degree : ℕ) (N x : PTm n)
    (h : Γ ⊢[PRAAx] admissible degree x)
    (hC : Γ ⊢[PRAAx] le one (coefficientDenominator x)) :
    Γ ⊢[PRAAx] le
      (pw two N * zabs (evaluate degree (coefficientCode x)
        (sampleNumerator degree (residualSchedule degree N x) x)
        (sampleDenominator degree (residualSchedule degree N x) x)))
      (evaluationDenominator degree (coefficientDenominator x)
        (sampleDenominator degree (residualSchedule degree N x) x)) := by
  cases degree with
  | zero =>
    change Γ ⊢[PRAAx] le (pw two N * zabs (coefficient (coefficientCode x) 0))
      (coefficientDenominator x * one)
    have hz : Γ ⊢[PRAAx] ZT.eq (coefficient (coefficientCode x) 0) (ZT.natLit 0) :=
      zle_antisym (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
        (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
    have absolute : Γ ⊢[PRAAx] zabs (coefficient (coefficientCode x) 0) ≐ zero :=
      (zabs_congr (ZT.toZ_eq hz)).eqTrans (abs_ofNat zero)
    exact le_congr ((congrMul (.eqRefl _) absolute).eqTrans (mul_zero _)).eqSymm
      (.eqRefl _) (zero_le _)
  | succ d =>
    let μ := residualSchedule (d + 1) N x
    let D := sampleDenominator (d + 1) μ x
    have raw := trace_residual_bound d (μ + offset x) x h
    have budget := residual_width_budget (d + 1) N x h hC
    change Γ ⊢[PRAAx] le
      (zabs (evaluate (d + 1) (coefficientCode x) (sampleNumerator (d + 1) μ x) D))
      (errorBudget (d + 1) x * naturalPower D d) at raw
    change Γ ⊢[PRAAx] le (pw two N * errorBudget (d + 1) x)
      (coefficientDenominator x * D) at budget
    have first : Γ ⊢[PRAAx] le
        (pw two N * zabs (evaluate (d + 1) (coefficientCode x) (sampleNumerator (d + 1) μ x) D))
        ((pw two N * errorBudget (d + 1) x) * naturalPower D d) :=
      le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right (pw two N) raw)
    have last : Γ ⊢[PRAAx] le ((pw two N * errorBudget (d + 1) x) * naturalPower D d)
        (evaluationDenominator (d + 1) (coefficientDenominator x) D) := by
      change Γ ⊢[PRAAx] le ((pw two N * errorBudget (d + 1) x) * naturalPower D d)
        (coefficientDenominator x * (naturalPower D d * D))
      exact le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (naturalPower D d) budget)
    exact le_trans first last

#print axioms residual_width_budget
#print axioms residual_bound

@[simp] theorem subst_boxBound {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (boxBound x) = boxBound (Syn.subst σ x) := by
  change Syn.subst σ (succ (initialWidth x + zabs (left (initialState x)))) =
    succ (initialWidth (Syn.subst σ x) + zabs (left (initialState (Syn.subst σ x))))
  rw [ConciseIPRA.PTm.subst_succ, PTm.subst_add, subst_initialWidth, subst_zabs,
    subst_left, subst_initialState]

@[simp] theorem subst_coefficientBound {m : ℕ} (σ : Fin n → PTm m)
    (degree : ℕ) (code B : PTm n) :
    Syn.subst σ (coefficientBound degree code B) =
      coefficientBound degree (Syn.subst σ code) (Syn.subst σ B) := by
  induction degree with
  | zero => exact ConciseIPRA.PTm.subst_zero σ
  | succ k ih =>
    change Syn.subst σ (coefficientBound k code B +
      num (k + 1) * zabs (coefficient code (k + 1)) * naturalPower B k) =
      coefficientBound k (Syn.subst σ code) (Syn.subst σ B) +
        num (k + 1) * zabs (coefficient (Syn.subst σ code) (k + 1)) * naturalPower (Syn.subst σ B) k
    rw [PTm.subst_add, PTm.subst_mul, PTm.subst_mul, ih, PTm.subst_num,
      subst_zabs, subst_coefficient, subst_naturalPower]

@[simp] theorem subst_errorBudget {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (x : PTm n) :
    Syn.subst σ (errorBudget degree x) = errorBudget degree (Syn.subst σ x) := by
  simp only [errorBudget, PTm.subst_mul, subst_initialWidth, subst_coefficientBound,
    subst_coefficientCode, subst_boxBound]

@[simp] theorem subst_residualSchedule {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (N x : PTm n) :
    Syn.subst σ (residualSchedule degree N x) =
      residualSchedule degree (Syn.subst σ N) (Syn.subst σ x) := by
  simp only [residualSchedule, PTm.subst_add, ConciseIPRA.PTm.subst_succ, subst_errorBudget]

/-- Explicit PR modulus for the polynomial residual of the actual regular name. -/
def residualScheduleF (degree : ℕ) : PR 2 := PTm.toPR (residualSchedule degree (var 0) (var 1))

theorem residualSchedule_at (degree : ℕ) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (residualScheduleF degree) N x ≐ residualSchedule degree N x := by
  have h := toPR_eq (Γ := Γ) (residualSchedule degree (var 0) (var 1) : PTm 2) ![N, x]
  simpa only [residualScheduleF, ap2, subst_residualSchedule, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem residualProgram_ge (degree : ℕ) (N x : PTm n) :
    Γ ⊢[PRAAx] le N (ap2 (residualScheduleF degree) N x) :=
  le_congr (.eqRefl _) (residualSchedule_at degree N x).eqSymm (residualSchedule_ge degree N x)

/-- Polynomial residual at an arbitrary sample query, after clearing its actual
positive denominator `C * D^degree`. -/
def residualAt (degree : ℕ) (N k x : PTm n) : Fm PTm n :=
  le (pw two N * zabs (evaluate degree (coefficientCode x)
      (sampleNumerator degree k x) (sampleDenominator degree k x)))
    (evaluationDenominator degree (coefficientDenominator x) (sampleDenominator degree k x))

@[simp] theorem subst_residualAt {m : ℕ} (σ : Fin n → PTm m) (degree : ℕ) (N k x : PTm n) :
    (residualAt degree N k x).subst σ =
      residualAt degree (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ x) := by
  simp only [residualAt, subst_le, subst_zabs, PTm.subst_mul, subst_evaluate,
    subst_ap2, subst_coefficientCode, subst_sampleNumerator, subst_sampleDenominator,
    evaluationDenominator, subst_coefficientDenominator, subst_naturalPower,
    two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- The residual estimate uses the actual generated PR schedule symbol. -/
theorem residual_program_at (degree : ℕ) (N x : PTm n)
    (h : Γ ⊢[PRAAx] admissible degree x)
    (hC : Γ ⊢[PRAAx] le one (coefficientDenominator x)) :
    Γ ⊢[PRAAx] residualAt degree N (ap2 (residualScheduleF degree) N x) x := by
  have source : Γ ⊢[PRAAx] (residualAt degree (var 0) (var 1) (var 2) : Fm PTm 3).subst
      ![N, residualSchedule degree N x, x] := by
    rw [subst_residualAt]
    simp only [Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact residual_bound degree N x h hC
  have query := residualSchedule_at (Γ := Γ) degree N x
  have target := Prf.eqSubst (residualAt degree (var 0) (var 1) (var 2) : Fm PTm 3)
    ![N, residualSchedule degree N x, x] ![N, ap2 (residualScheduleF degree) N x, x]
    (fun i => by fin_cases i; exact .eqRefl _; exact query.eqSymm; exact .eqRefl _) source
  simpa only [subst_residualAt, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using target

/-- Internal variables are target precision and runtime polynomial/bracket data. -/
def residualFormula (degree : ℕ) : Fm PTm 2 :=
  let μ := ap2 (residualScheduleF degree) (var 0) (var 1)
  admissible degree (var 1) ⟶ le one (coefficientDenominator (var 1)) ⟶
    (le (var 0) μ ⋏ le one (sampleDenominator degree μ (var 1)) ⋏
     le one (evaluationDenominator degree (coefficientDenominator (var 1))
       (sampleDenominator degree μ (var 1))) ⋏
     residualAt degree (var 0) μ (var 1))

/-- Closed finite-query polynomial root condition for the actual regular name.
The coefficient bound, residual budget and query schedule are all computed. -/
theorem residual_name (degree : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (residualFormula degree) := by
  refine closeUniv 2 (.impI (.impI ?_))
  let Δ : List (Fm PTm 2) := [le one (coefficientDenominator (var 1)), admissible degree (var 1)]
  let μ : PTm 2 := ap2 (residualScheduleF degree) (var 0) (var 1)
  have hd := sample_denominator_positive (Γ := Δ) degree μ (var 1) Prf.hyp1
  exact .andI (residualProgram_ge degree (var 0) (var 1)) (.andI hd (.andI
    (evaluationDenominator_positive degree (coefficientDenominator (var 1)) _ Prf.hyp0 hd)
    (residual_program_at degree (var 0) (var 1) Prf.hyp1 Prf.hyp0)))

#print axioms residualSchedule_at
#print axioms residualProgram_ge
#print axioms residual_program_at
#print axioms residual_name

end LeanProofs.IPRA.Analysis.PolynomialRootName
