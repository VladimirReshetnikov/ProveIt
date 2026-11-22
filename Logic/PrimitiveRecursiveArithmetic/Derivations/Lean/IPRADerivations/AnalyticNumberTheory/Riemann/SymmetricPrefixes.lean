import IPRADerivations.AnalyticNumberTheory.Riemann.DiscreteForms
import Mathlib.Tactic.Ring

/-! Imported from the packet `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`,
`SymmetricPrefixes.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Three permutation-invariant finite tests for domination of two integer lists.
The central equivalence is local at each common horizon. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.SymmetricPrefixes
open LeanProofs.ConciseIPRA PacketLanguage Discrete

variable (E B : Nat → Nat)

def height (n : Nat) := 1 + total B n
def level (n i : Nat) := E i + (height B n - B i)
def order (n : Nat) := n * height B n + 1

def powerSum (n : Nat) := total (fun i => (level E B n i)^(order B n)) n
def expSum (n : Nat) := total (fun i => (n+1)^(level E B n i)) n

def product (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => product f n * f n

/-- Absolute value of the signed characteristic polynomial at r. -/
def charAbs (n r : Nat) := product (fun i => delta (r+B i) (E i)) n
def gridProduct (n : Nat) := product (fun j => charAbs E B n (j+1)) (total E n)

inductive Test where | moment | exponential | characteristic

def passes (k : Test) (n : Nat) : Prop := match k with
  | .moment => powerSum E B n ≤ n * height B n ^ order B n
  | .exponential => expSum E B n ≤ n * (n+1)^height B n
  | .characteristic => 0 < gridProduct E B n

private theorem member_le_total (f : Nat → Nat) {i n : Nat} (h : i < n) :
    f i ≤ total f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [total]
    by_cases he : i = n
    · subst i; omega
    · have := ih (by omega); omega

private theorem total_cap (f : Nat → Nat) (c n : Nat) (h : ∀ i < n, f i ≤ c) :
    total f n ≤ n*c := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [total, Nat.succ_mul]
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

private theorem product_pos (f : Nat → Nat) (n : Nat) :
    0 < product f n ↔ ∀ i < n, 0 < f i := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    have hp : ∀ a b : Nat, 0 < a*b ↔ 0 < a ∧ 0 < b := fun _ _ =>
      ⟨fun h => ⟨Nat.pos_of_mul_pos_right h, Nat.pos_of_mul_pos_left h⟩, fun h => Nat.mul_pos h.1 h.2⟩
    rw [product, hp, ih]
    constructor
    · rintro ⟨hp, hf⟩ i hi
      by_cases he : i = n
      · simpa [he] using hf
      · exact hp i (by omega)
    · intro h; exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- Integral binomial lower bound. Its proof needs only monotone multiplication. -/
private theorem bernoulli (M r : Nat) :
    (M+1+r)*M^r ≤ (M+1)^(r+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      (M+1+(r+1))*M^(r+1)
        = ((M+1+r)*M^r)*(M+1) - (r+1)*M^r := by
          apply Nat.eq_sub_of_add_eq
          ring
      _ ≤ ((M+1+r)*M^r)*(M+1) := Nat.sub_le _ _
      _ ≤ (M+1)^(r+1)*(M+1) := Nat.mul_le_mul_right _ ih
      _ = _ := (Nat.pow_succ _ _).symm

private theorem amplify (M n : Nat) (hp : 0 < M) :
    n * M^(n*M+1) < (M+1)^(n*M+1) := by
  have h : n*M < M+1+n*M := by omega
  calc
    n*M^(n*M+1) = n*M * M^(n*M) := by ring
    _ < (M+1+n*M)*M^(n*M) := Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos hp)
    _ ≤ (M+1)^(n*M+1) := bernoulli _ _

private theorem level_iff {n i : Nat} (h : i < n) :
    level E B n i ≤ height B n ↔ E i ≤ B i := by
  have hb := member_le_total B h
  unfold level height
  omega

/-- A single scalar inequality detects every violation, at the same horizon. -/
theorem finite_iff (k : Test) (n : Nat) :
    passes E B k n ↔ ∀ i < n, E i ≤ B i := by
  cases k with
  | moment =>
    constructor
    · intro h i hi
      by_cases hg : E i ≤ B i
      · exact hg
      · have hl : height B n + 1 ≤ level E B n i := by
          have := level_iff E B hi; omega
        have ha := amplify (height B n) n (by simp [height])
        have hb := Nat.pow_le_pow_left hl (order B n)
        have hc := member_le_total (fun j => (level E B n j)^(order B n)) hi
        change total _ n ≤ n*height B n ^ order B n at h
        change n*height B n ^ order B n < (height B n+1)^order B n at ha
        omega
    · intro h
      exact total_cap _ _ n (fun i hi =>
        Nat.pow_le_pow_left ((level_iff E B hi).mpr (h i hi)) _)
  | exponential =>
    constructor
    · intro h i hi
      by_cases hg : E i ≤ B i
      · exact hg
      · have hl : height B n+1 ≤ level E B n i := by
          have := level_iff E B hi; omega
        have hb := Nat.pow_le_pow_right (by omega : 0 < n+1) hl
        have hc := member_le_total (fun j => (n+1)^(level E B n j)) hi
        have ha : n*(n+1)^height B n < (n+1)^(height B n+1) := by
          rw [Nat.pow_succ, Nat.mul_comm ((n+1)^height B n)]
          exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
        change total _ n ≤ n*(n+1)^height B n at h
        omega
    · intro h
      exact total_cap _ _ n (fun i hi => Nat.pow_le_pow_right (by omega)
        ((level_iff E B hi).mpr (h i hi)))
  | characteristic =>
    change 0 < product _ _ ↔ _
    rw [product_pos]
    constructor
    · intro h i hi
      by_cases hg : E i ≤ B i
      · exact hg
      · have he := member_le_total E hi
        let j := E i - B i - 1
        have hj : j < total E n := by dsimp [j]; omega
        have hz := (product_pos _ _).mp (h j hj) i hi
        change 0 < delta (j+1+B i) (E i) at hz
        unfold delta at hz; dsimp [j] at hz; omega
    · intro h j _
      apply (product_pos _ _).mpr
      intro i hi
      have := h i hi
      change 0 < delta (j+1+B i) (E i)
      unfold delta; omega

section Syntax
private abbrev ctx := ["d","H","a","b","n"]

/-- The compiler elaborates each variable name in the surrounding bounded-loop
context.  In particular, 'n' always denotes the original horizon. -/
local macro "atPacket " f:term:arg ", " t:term:arg : term =>
  `(call $f [v "d", v "H", v "a", v "b", $t])

private def totalCode (f : PR 5) : PR 5 :=
  program ctx <| sumTo "i" (v "n") (atPacket f, (v "i"))

private def htCode : PR 5 :=
  program ctx <| 1 + (atPacket (totalCode budgetCode), (v "n"))

local macro "translatedLevel" : term =>
  `((atPacket energyCode, (v "i")) +
      ((atPacket htCode, (v "n")) - (atPacket budgetCode, (v "i"))))

private def momentCode : PR 5 := program ctx <|
  sumTo "i" (v "n") (powE translatedLevel (v "n"*(atPacket htCode, (v "n"))+1)) -
    v "n"*powE (atPacket htCode, (v "n")) (v "n"*(atPacket htCode, (v "n"))+1)

private def expCode : PR 5 := program ctx <|
  sumTo "i" (v "n") (powE (v "n"+1) translatedLevel) -
    v "n"*powE (v "n"+1) (atPacket htCode, (v "n"))

private def charCode : PR 5 := program ctx <|
  1 - prodTo "j" (atPacket (totalCode energyCode), (v "n"))
    (prodTo "i" (v "n") <|
      let x := (v "j"+1) + (atPacket budgetCode, (v "i"))
      let y := (atPacket energyCode, (v "i"))
      (x-y)+(y-x))

def matrix : Test → PR 5
  | .moment => momentCode
  | .exponential => expCode
  | .characteristic => charCode

def statement (s : Family) (k : Test) : Fm PTm 0 := s.close (matrix k)

private theorem sum_eval {c : List String} (j : String) (n : PacketLanguage.E c)
    (f : PacketLanguage.E (j::c)) (e) :
    denote (sumTo j n f) e = total (fun i => denote f (Fin.cases i e)) (denote n e) := by
  change overRange 0 (fun i a => a + denote f (Fin.cases i e)) (denote n e) = _
  generalize denote n e = k
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (· + denote f (Fin.cases k e)) ih

private theorem prod_eval {c : List String} (j : String) (n : PacketLanguage.E c)
    (f : PacketLanguage.E (j::c)) (e) :
    denote (prodTo j n f) e = product (fun i => denote f (Fin.cases i e)) (denote n e) := by
  change overRange 1 (fun i a => a * denote f (Fin.cases i e)) (denote n e) = _
  generalize denote n e = k
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (· * denote f (Fin.cases k e)) ih

private theorem totalCode_ok (f : PR 5) (p : Data) (n : Nat) :
    value (totalCode f) (p.args n) = total (fun i => value f (p.args i)) n := by
  unfold totalCode
  rw [value_program, sum_eval]
  simp only [apply5]; rfl

private theorem height_ok (p : Data) (n : Nat) :
    value htCode (p.args n) = height p.budget n := by
  unfold htCode
  rw [value_program, plus, apply5]
  change 1 + value (totalCode budgetCode) (p.args n) = _
  rw [totalCode_ok]; simp only [budget_ok, height]

theorem matrix_reading (p : Data) (k : Test) (n : Nat) :
    value (matrix k) (p.args n) = 0 ↔ passes p.energy p.budget k n := by
  cases k with
  | moment =>
    unfold matrix momentCode
    rw [value_program, minus, Nat.sub_eq_zero_iff_le, sum_eval]
    simp only [power, times, plus, minus, apply5]
    change total (fun i =>
      (value energyCode (p.args i) +
        (value htCode (p.args n) - value budgetCode (p.args i))) ^
          (n*value htCode (p.args n)+1)) n ≤
        n*value htCode (p.args n)^(n*value htCode (p.args n)+1) ↔ _
    simp only [energy_ok, budget_ok, height_ok]; rfl
  | exponential =>
    unfold matrix expCode
    rw [value_program, minus, Nat.sub_eq_zero_iff_le, sum_eval]
    simp only [power, times, plus, minus, apply5]
    change total (fun i =>
      (n+1)^(value energyCode (p.args i) +
        (value htCode (p.args n) - value budgetCode (p.args i)))) n ≤
        n*(n+1)^value htCode (p.args n) ↔ _
    simp only [energy_ok, budget_ok, height_ok]; rfl
  | characteristic =>
    unfold matrix charCode
    rw [value_program, minus, Nat.sub_eq_zero_iff_le]
    simp only [prod_eval, plus, minus, apply5]
    change 1 ≤ product (fun j => product (fun i =>
      ((j+1+value budgetCode (p.args i))-value energyCode (p.args i)) +
        (value energyCode (p.args i)-(j+1+value budgetCode (p.args i)))) n)
          (value (totalCode energyCode) (p.args n)) ↔ _
    simp only [totalCode_ok, energy_ok, budget_ok]; rfl

theorem statement_iff (s : Family) (k : Test) :
    naturalTerms.Holds (statement s k) Fin.elim0 ↔
    naturalTerms.Holds (s.close excess) Fin.elim0 := by
  apply (s.holds_matrix (matrix k)).trans
  apply Iff.trans _ (s.holds_matrix excess).symm
  apply s.lift_iff
  intro p
  constructor
  · intro h i
    exact (read_test p i).mpr ((finite_iff _ _ k (i+1)).mp
      ((matrix_reading p k (i+1)).mp (h (i+1))) i (by omega))
  · intro h n
    exact (matrix_reading p k n).mpr ((finite_iff _ _ k n).mpr
      (fun i _ => (read_test p i).mp (h i)))

end Syntax
end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA.SymmetricPrefixes
