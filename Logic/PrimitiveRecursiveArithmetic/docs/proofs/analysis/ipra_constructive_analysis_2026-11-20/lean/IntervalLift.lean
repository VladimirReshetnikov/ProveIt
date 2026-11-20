import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Rational estimates for extending a finite observation to regular Cauchy
names. The adjacent-cell bound and cross-precision agreement are hypotheses.
All output comparisons quantify only over finite rational observations. -/
namespace BudgetAnalysis.IntervalLift

abbrev UnitQ := {x : ℚ // 0 ≤ x ∧ x ≤ 1}
abbrev Name := Nat → UnitQ

def eps (k : Nat) : ℚ := (1/2)^k

theorem eps_nonneg (k : Nat) : 0 ≤ eps k := pow_nonneg (by norm_num) _

theorem eps_anti : Antitone eps := by
  apply antitone_nat_of_succ_le
  intro i
  have h := eps_nonneg i
  unfold eps at *
  rw [pow_succ]
  linarith

theorem eps_one (i : Nat) : eps (i+1) = eps i / 2 := by
  simp [eps, pow_succ, div_eq_mul_inv]

theorem eps_two (i : Nat) : eps (i+2) = eps i / 4 := by
  rw [show i+2 = (i+1)+1 by omega, eps_one, eps_one]; linarith

theorem eps_three (i : Nat) : eps (i+3) = eps i / 8 := by
  rw [show i+3 = (i+2)+1 by omega, eps_one, eps_two]; linarith

def env (N : Nat → Nat) : Nat → Nat
  | 0 => N 0
  | i+1 => max (env N i) (N (i+1))

theorem env_mono (N : Nat → Nat) : Monotone (env N) :=
  monotone_nat_of_le_succ (fun _ => le_max_left ..)

theorem env_bound (N : Nat → Nat) {k l : Nat} (h : k ≤ l) : N k ≤ env N l := by
  apply le_trans _ (env_mono N h)
  cases k with
  | zero => rfl
  | succ i => exact le_max_right .. 

structure Observation where
  V : Nat → UnitQ → ℚ
  N : Nat → Nat
  consistent : ∀ k l x, |V k x - V l x| ≤ eps k + eps l
  adjacent : ∀ k (x y : UnitQ), |(x:ℚ) - (y:ℚ)| ≤ eps (N k) →
              |V k x - V k y| ≤ 2 * eps k

def precision (E : Observation) (n : Nat) := env E.N (n+3) + 2

def lift (E : Observation) (a : Name) (n : Nat) : ℚ := E.V (n+3) (a (precision E n))

def distLE (r : ℚ) (a b : Name) : Prop :=
  ∀ i l, |(a i : ℚ) - (b l : ℚ)| ≤ r + eps i + eps l

theorem distLE_symm {r : ℚ} {a b : Name} (h : distLE r a b) : distLE r b a := by
  intro i l
  rw [abs_sub_comm]
  linarith [h l i]

theorem precision_bound (E : Observation) {k n : Nat} (h : k ≤ n+3) :
    eps (precision E n) ≤ eps (E.N k) / 4 := by
  rw [← eps_two]
  exact eps_anti (Nat.add_le_add_right (env_bound E.N h) 2)

theorem mixed_ordered (E : Observation) {a b : Name} (eqn : distLE 0 a b)
    (i l : Nat) (il : i ≤ l) :
    |lift E a i - lift E b l| ≤ 3 * eps (i+3) + eps (l+3) := by
  let x := a (precision E i)
  let y := b (precision E l)
  have near : |(x:ℚ)-(y:ℚ)| ≤ eps (E.N (i+3)) := by
    have h := eqn (precision E i) (precision E l)
    change |(x:ℚ)-(y:ℚ)| ≤ _ at h
    linarith [precision_bound E (k:=i+3) (n:=i) (by omega),
      precision_bound E (k:=i+3) (n:=l) (by omega), eps_nonneg (E.N (i+3))]
  change |E.V (i+3) x - E.V (l+3) y| ≤ _
  linarith [E.adjacent _ x y near, E.consistent (i+3) (l+3) y,
    abs_sub_le (E.V (i+3) x) (E.V (i+3) y) (E.V (l+3) y)]

/-- Both regularity (a=b) and preservation of name equality. -/
theorem lift_extensional (E : Observation) {a b : Name} (eqn : distLE 0 a b) (i l : Nat) :
    |lift E a i - lift E b l| ≤ eps i + eps l := by
  rcases Nat.le_total i l with le | le
  · have h := mixed_ordered E eqn i l le
    rw [eps_three, eps_three] at h
    linarith [eps_nonneg i, eps_nonneg l]
  · rw [abs_sub_comm]
    have h := mixed_ordered E (distLE_symm eqn) l i le
    rw [eps_three, eps_three] at h
    linarith [eps_nonneg i, eps_nonneg l]

/-- A rational-domain client can query V directly and use the extracted modulus. -/
theorem rational_modulus (E : Observation) (j p q : Nat) (x y : UnitQ)
    (h : |(x:ℚ)-(y:ℚ)| ≤ eps (E.N (j+2))) :
    |E.V p x - E.V q y| ≤ eps p + eps j + eps q := by
  let k := j+2
  have a := E.adjacent k x y h
  have b := E.consistent p k x
  have c := E.consistent k q y
  have d := abs_sub_le (E.V p x) (E.V k x) (E.V q y)
  have e := abs_sub_le (E.V k x) (E.V k y) (E.V q y)
  have scale : eps k = eps j / 4 := eps_two j
  linarith

/-- Uniform modulus for the Cauchy-name lift. A single finite comparison at
the common index s absorbs all arithmetic slack, with no limiting lemma. -/
theorem lift_modulus (E : Observation) {a b : Name}
    (ha : distLE 0 a a) (hb : distLE 0 b b) (j : Nat)
    (close : distLE (eps (E.N (j+2)+1)) a b) (i l : Nat) :
    |lift E a i - lift E b l| ≤ eps i + eps j + eps l := by
  let k := j+2
  let s := max i (max l k)
  have si : i ≤ s := le_max_left ..
  have sl : l ≤ s := le_trans (le_max_left ..) (le_max_right ..)
  have sk : k ≤ s := le_trans (le_max_right ..) (le_max_right ..)
  let x := a (precision E s)
  let y := b (precision E s)
  have near : |(x:ℚ)-(y:ℚ)| ≤ eps (E.N k) := by
    have c := close (precision E s) (precision E s)
    change |(x:ℚ)-(y:ℚ)| ≤ eps (E.N k+1) + _ + _ at c
    rw [eps_one] at c
    linarith [precision_bound E (k:=k) (n:=s) (by omega)]
  have mid := rational_modulus E j (s+3) (s+3) x y near
  change |lift E a s - lift E b s| ≤ _ at mid
  have left := mixed_ordered E ha i s si
  have right := mixed_ordered E hb l s sl
  rw [abs_sub_comm] at right
  have t₁ := abs_sub_le (lift E a i) (lift E a s) (lift E b l)
  have t₂ := abs_sub_le (lift E a s) (lift E b s) (lift E b l)
  simp only [eps_three] at mid left right
  linarith [eps_anti si, eps_anti sl, eps_nonneg i, eps_nonneg l]

end BudgetAnalysis.IntervalLift
