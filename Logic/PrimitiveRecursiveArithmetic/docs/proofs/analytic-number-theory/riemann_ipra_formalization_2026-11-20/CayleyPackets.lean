import UniversalCriteria
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Fixed-centre, one-sided conformal coefficient tests for the three
families. The complex-analytic identification is proved in the report.
The syntax, numerical interpretation, and scheduled object derivations
below use only the supplied ConciseIPRA development. -/
namespace RiemannIPRA.Cayley
open LeanProofs.ConciseIPRA PacketLanguage Discrete

inductive Side | upper | lower | both
inductive Precision | all | fixed

private def factE {ctx} (n : E ctx) := call PrimeForms.factCode [n]
private def chooseE {ctx} (n k : E ctx) := call PrimeForms.chooseCode [n,k]

/-- Numerator of the positive or negative part of coefficient number t+1.
The common denominator is (t+1)! N^(2(t+1)) (N!)^5. -/
def part (neg : Bool) : PR 6 := program ["d","H","u","v","t","N"] <|
  sumTo "i" (v "t"+1) <|
    let k := v "i"+1
    let a := fun side => call (Taylor.numerator side) [v "d",v "H",v "u",v "v",5,k,v "N"]
    let src := iteE (modE k 2) (a (!neg)) (a neg)
    let w := powE 9 k * chooseE (v "t") (v "i") *
      divE (factE (v "t"+1)) (factE k) * powE (v "N") (2*(v "t"-v "i"))
    w * src

private def radiusError {ctx} (d0 t : E ctx) := 81*(d0+2)*powE 10 t
private def precisionE {ctx} (mode : Precision) (d0 t h : E ctx) := match mode with
  | .all => h+1
  | .fixed => radiusError d0 t

def matrix (side : Side) (mode : Precision) : PR 8 :=
  program ["d","H","u","v","t","h","b","w"] <|
    let t := v "t"
    let m := t+1
    let N := precisionE mode (v "d") t (v "h")
    let readPart := fun neg => call (part neg) [v "d",v "H",v "u",v "v",t,N]
    let x := N*readPart false
    let y := N*readPart true
    let D := factE m * powE N (2*m) * powE (factE N) 5
    let C := 1000*powE (v "d"+2) 4*powE (v "H"+2) 2
    let B := 13500*C*powE (m+1) 4
    let allowance := D*(N*B+radiusError (v "d") t)
    match side with
    | .upper => x-(y+allowance)
    | .lower => y-(x+allowance)
    | .both => (x-(y+allowance))+(y-(x+allowance))

def statement (f : Family) (side : Side) (mode : Precision) : Fm PTm 0 :=
  f.close8 (matrix side mode)

/-- The factorial representation used by the PR binomial constructor. -/
def binomial (n k : Nat) : Nat :=
  if k ≤ n then Taylor.fact n / (Taylor.fact k * Taylor.fact (n-k)) else 0

private theorem factRead {ctx} (x : E ctx) (e) : denote (factE x) e = Taylor.fact (denote x e) := by
  change value PrimeForms.factCode _ = _
  unfold PrimeForms.factCode
  rw [value_program]
  change overRange 1 _ (denote x e) = _
  simp only [Discrete.plus]
  change overRange 1 (fun i a => a * (i+1)) (denote x e) = _
  generalize denote x e = n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun y => y*(n+1)) ih

theorem fact_eq (n : Nat) : Taylor.fact n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Taylor.fact, Nat.factorial_succ, ih, Nat.mul_comm]

theorem binomial_eq (n k : Nat) : binomial n k = n.choose k := by
  unfold binomial
  split
  · rename_i h
    simp only [fact_eq]
    exact (Nat.choose_eq_factorial_div_factorial h).symm
  · rename_i h
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm

private theorem readLe {ctx} (a b : E ctx) (e) :
    denote (leB a b) e = (if denote a e ≤ denote b e then 1 else 0) := by
  change value isZeroR _ = _
  rw [value_isZeroR]
  change (if denote (a-b) e = 0 then 1 else 0) = _
  simp only [Discrete.minus,Nat.sub_eq_zero_iff_le]

private theorem readIte {ctx} (t a b : E ctx) (e) :
    denote (iteE t a b) e = (if denote t e = 0 then denote b e else denote a e) := by
  have clip (x : E ctx) : denote (call clipR [x]) e = bit (denote x e) := value_clipR _
  have zero (x : E ctx) : denote (call isZeroR [x]) e = (if denote x e = 0 then 1 else 0) :=
    value_isZeroR _
  simp only [iteE,Discrete.plus,Discrete.times,clip,zero,bit]
  split <;> simp

private theorem readSum {ctx} (j : String) (n : E ctx) (s : E (j::ctx)) (e) :
    denote (sumTo j n s) e =
      overRange 0 (fun i a => a+denote s (Fin.cases i e)) (denote n e) := rfl

private theorem rawFact {ctx} (a : E ctx) (e) :
    denote (call PrimeForms.factCode [a]) e = Taylor.fact (denote a e) := factRead a e

private theorem binomRead {ctx} (x k : E ctx) (e) :
    denote (chooseE x k) e = binomial (denote x e) (denote k e) := by
  change value PrimeForms.chooseCode _ = _
  unfold PrimeForms.chooseCode
  rw [value_program]
  simp only [readIte, denote_divE, Discrete.times, rawFact, Discrete.minus,
    readLe, binomial]
  change (if (if denote k e ≤ denote x e then 1 else 0) = 0 then 0 else _) = _
  split <;> split <;> first | rfl | simp_all

private theorem sideRead {ctx} (b : Bool) (d H u v k N : E ctx) (e) :
    denote (call (Taylor.numerator b) [d,H,u,v,5,k,N]) e =
      Taylor.sumSide ⟨denote d e,denote H e,denote u e,denote v e⟩ b
        5 (denote k e) (denote N e) := by
  apply Eq.trans _ (Taylor.numerator_reading _ b 5 _ _)
  change value (Taylor.numerator b) _ = value (Taylor.numerator b) _
  congr 1
  funext ⟨i, hi⟩
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
  | n+7 => omega

def natPart (p : Data) (neg : Bool) (t N : Nat) :=
  overRange 0 (fun i acc =>
    let k := i+1
    let w := 9^k * binomial t i * (Taylor.fact (t+1) / Taylor.fact k) * N^(2*(t-i))
    let src := if k%2 = 0 then Taylor.sumSide p neg 5 k N else Taylor.sumSide p (!neg) 5 k N
    acc+w*src) (t+1)

private theorem partRead {ctx} (b : Bool) (d H u v t N : E ctx) (e) :
    denote (call (part b) [d,H,u,v,t,N]) e =
      natPart ⟨denote d e,denote H e,denote u e,denote v e⟩ b (denote t e) (denote N e) := by
  change value (part b) _ = _
  unfold part
  rw [value_program]
  simp only [readSum,Discrete.times, Discrete.plus, Discrete.minus, Discrete.power,
    binomRead, factRead, denote_divE, readIte, denote_modE, sideRead]
  rfl

def prec : Precision → Nat → Nat → Nat → Nat
  | .all, _, _, h => h+1
  | .fixed, d0, t, _ => 81*(d0+2)*10^t

def check (side : Side) (p : Data) (t N : Nat) : Prop :=
  let m := t+1
  let D := Taylor.fact m * N^(2*m) * (Taylor.fact N)^5
  let C := 1000*(p.degreeOffset+2)^4*(p.height+2)^2
  let allowance := D*(N*(13500*C*(m+1)^4) + 81*(p.degreeOffset+2)*10^t)
  let x := N*natPart p false t N
  let y := N*natPart p true t N
  match side with
  | .upper => x ≤ y+allowance
  | .lower => y ≤ x+allowance
  | .both => x ≤ y+allowance ∧ y ≤ x+allowance

private theorem bothZero (x y b : Nat) : (x-(y+b))+(y-(x+b))=0 ↔ x≤y+b ∧ y≤x+b := by omega

theorem matrix_reading (side : Side) (mode : Precision) (p : Data) (t h b w : Nat) :
    value (matrix side mode) (p.work t h b w) = 0 ↔ check side p t (prec mode p.degreeOffset t h) := by
  cases mode <;> cases side <;> unfold matrix <;> rw [value_program] <;>
    simp only [precisionE,radiusError,Discrete.plus,Discrete.minus,Discrete.times,Discrete.power,
      factRead,partRead,bothZero,Nat.sub_eq_zero_iff_le] <;> rfl

theorem statement_reading (f : Family) (side : Side) (mode : Precision) :
    naturalTerms.Holds (statement f side mode) Fin.elim0 ↔
    f.allData (fun p => ∀ t h, check side p t (prec mode p.degreeOffset t h)) := by
  apply (holds8 f _).trans
  apply f.lift_iff
  intro p
  simp only [matrix_reading]
  exact ⟨fun h t n => h t n 0 0, fun h t n _ _ => h t n⟩

/-- An internal equivalence, valid for every cofinal cube schedule
constructed from the offset program g by the inherited scheduler. -/
theorem scheduled (f : Family) (side : Side) (mode : Precision) (g : PR 1) :
    Prf PRAAx [] (Fm.iff (statement f side mode)
      ((UniversalCriteria.block (statement f side mode)).schedule g)) :=
  UniversalCriteria.scheduled (UniversalCriteria.eight f _) g

theorem certified_failure (f : Family) (side : Side) (mode : Precision) :
    Prf PRAAx [] (Fm.iff (RHCounterexamples.counter (statement f side mode))
      (UniversalCriteria.block (statement f side mode)).firstRadius) :=
  UniversalCriteria.firstFailure (UniversalCriteria.eight f _)

/-- Exact total weight of the conformal transform, the source of the
fixed precision 81(d+1)10^t. -/
theorem weightSum (t : Nat) :
    ∑ i ∈ Finset.range (t+1), 9^(i+1)*binomial t i = 9*10^t := by
  have h := add_pow (9 : Nat) 1 t
  simp only [one_pow, Nat.mul_one, Nat.cast_id] at h
  change 10^t = _ at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [binomial_eq, pow_succ]
  ring

/-- Positive finite sums tolerate a uniform error on their inputs.
Together with a certified tail this is one step of Taylor translation.
The weight bound and tail bound are supplied independently. -/
theorem translation_step (n : Nat) (a w : Nat → ℚ) (M eps y : ℚ)
    (hM : 0 < M) (he : 0 ≤ eps)
    (hw : ∀ i ∈ Finset.range n, 0 ≤ w i)
    (ha : ∀ i ∈ Finset.range n, -(eps/(2*M)) ≤ a i)
    (hweight : ∑ i ∈ Finset.range n, w i ≤ M)
    (htail : (∑ i ∈ Finset.range n, w i*a i) - eps/2 ≤ y) : -eps ≤ y := by
  have hfrac : 0 ≤ eps/(2*M) := div_nonneg he (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hweight hfrac
  have hsum : -(∑ i ∈ Finset.range n, w i)*(eps/(2*M)) ≤
      ∑ i ∈ Finset.range n, w i*a i := by
    rw [neg_mul, ← mul_neg, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (ha i hi) (hw i hi)
  have hid : M*(eps/(2*M))=eps/2 := by
    field_simp
  rw [neg_mul] at hsum
  linarith

/-- Recursively bounded order/precision pairs for a finite string of
translations. Both updates are affine functions of the current pair. -/
def budgets (J E : Nat) : Nat → Nat × Nat
  | 0 => (J,E)
  | n+1 =>
    let (k,t) := budgets J E n
    (2*k+t+1,t+k+2)

theorem finite_propagation (P : Nat → Nat → Nat → Prop) (J E n : Nat)
    (base : P 0 (budgets J E n).1 (budgets J E n).2)
    (step : ∀ i k t, P i (2*k+t+1) (t+k+2) → P (i+1) k t) :
    P n J E := by
  have rows (i l : Nat) (h : i+l=n) :
      P i (budgets J E l).1 (budgets J E l).2 := by
    induction i generalizing l with
    | zero =>
      simp only [Nat.zero_add] at h
      simpa only [h] using base
    | succ i ih =>
      have prev := ih (l+1) (by omega)
      exact step i _ _ prev
  exact rows n 0 (by omega)

end RiemannIPRA.Cayley
