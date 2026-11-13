import DiophantineConsistency.ModelOptimizer
import DiophantineConsistency.DirectScalarArithmetic

/-! # Internal meaning of the elementary scalar program combinators

`DirectScalar` builds supplied programs (`ScalarPRCode.Realizes`) for
identity, constants, successor, addition, predecessor, truncated
subtraction, multiplication, zero tests, equality tests and iteration, each
certified only on `ℕ`. This file computes their internal semantics
`ModelScalarPR.evalV` in an arbitrary model `V` of `𝗜𝚺₁` at every input:

* `evalV (add p q).val x = evalV p.val x + evalV q.val x`, and likewise
  `sub` (model truncated subtraction), `mul`, `pred`, `successor`,
  `constant`, `identity`;
* `evalV (ifZero p q r).val x = if evalV p.val x = 0 then … else …` and the
  same for `ifEq`;
* `iterate p k` is the internal iteration `iterV p k` of `evalV p.val`
  from `k` (`evalV_iterate`, `iterV_zero`, `iterV_succ`).

The `*_val` lemmas expose each combinator's code one level deep by `rfl`
(cheap: only the named definitions are unfolded), so that every semantic
statement is proved by rewriting with the `evalV` recursion equations and,
for the arithmetic recursions, internal `𝚺₁` induction. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelDirectScalar
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelScalarPR ScalarPRCode DirectScalar

/-! ### Code of the combinators, one level deep -/

section Codes
variable {f g h k : ℕ → ℕ}

theorem zeroR_val : (Realizes.zero).val = ScalarPRCode.zero := rfl
theorem succR_val : (Realizes.succ).val = ScalarPRCode.succ := rfl
theorem leftR_val : (Realizes.left).val = ScalarPRCode.left := rfl
theorem rightR_val : (Realizes.right).val = ScalarPRCode.right := rfl
theorem pairR_val (p : R f) (q : R g) : (p.pair q).val = .pair p.val q.val := rfl
theorem compR_val (p : R f) (q : R g) : (p.comp q).val = .comp p.val q.val := rfl
theorem ofEq_val (p : R f) (e : ∀ n, f n = g n) : (p.ofEq e).val = p.val := rfl
theorem identity_val : identity.val = .pair .left .right := rfl
theorem constant_zero_val : (constant 0).val = .zero := rfl
theorem constant_succ_val (n : ℕ) : (constant (n + 1)).val = .comp .succ (constant n).val := rfl
theorem successor_val (p : R f) : (successor p).val = .comp .succ p.val := rfl
theorem addition_val :
    addition.val = .prec identity.val (.comp .succ (.comp .right .right)) := rfl
theorem add_val (p : R f) (q : R g) :
    (add p q).val = .comp addition.val (.pair p.val q.val) := rfl
theorem predecessor_val :
    predecessor.val = .comp (.prec .zero (.comp .left .right)) (.pair .zero identity.val) := rfl
theorem pred_val (p : R f) : (pred p).val = .comp predecessor.val p.val := rfl
theorem subtraction_val :
    subtraction.val = .prec identity.val (.comp predecessor.val (.comp .right .right)) := rfl
theorem sub_val (p : R f) (q : R g) :
    (DirectScalar.sub p q).val = .comp subtraction.val (.pair p.val q.val) := rfl
theorem multiplication_val :
    multiplication.val =
      .prec .zero (add Realizes.left (Realizes.right.comp Realizes.right)).val := rfl
theorem mul_val (p : R f) (q : R g) :
    (mul p q).val = .comp multiplication.val (.pair p.val q.val) := rfl
theorem zeroBranch_val : zeroBranch.val = .prec .left (.comp .right .left) := rfl
theorem ifZero_val (p : R f) (q : R g) (r : R h) :
    (ifZero p q r).val = .comp zeroBranch.val (.pair (.pair q.val r.val) p.val) := rfl
theorem ifEq_val (p : R f) (q : R g) (r : R h) (s : R k) :
    (ifEq p q r s).val = (ifZero (add (DirectScalar.sub p q) (DirectScalar.sub q p)) r s).val := rfl
theorem iterate_val (p : R f) (initial : ℕ) :
    (iterate p initial).val =
      .comp (.prec (constant initial).val (.comp p.val (.comp .right .right)))
        (.pair .zero identity.val) := rfl

end Codes

/-! ### Internal semantics -/

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {f g h k : ℕ → ℕ}

theorem evalV_zeroR (x : V) : evalV (Realizes.zero).val x = 0 := rfl
theorem evalV_succR (x : V) : evalV (Realizes.succ).val x = x + 1 := rfl
theorem evalV_leftR (x : V) : evalV (Realizes.left).val x = munpair₁ x := rfl
theorem evalV_rightR (x : V) : evalV (Realizes.right).val x = munpair₂ x := rfl

theorem evalV_pairR (p : R f) (q : R g) (x : V) :
    evalV (p.pair q).val x = mpair (evalV p.val x) (evalV q.val x) := by
  rw [pairR_val, evalV_pair]

theorem evalV_compR (p : R f) (q : R g) (x : V) :
    evalV (p.comp q).val x = evalV p.val (evalV q.val x) := by
  rw [compR_val, evalV_comp]

theorem evalV_ofEq (p : R f) (e : ∀ n, f n = g n) (x : V) :
    evalV (p.ofEq e).val x = evalV p.val x := by
  rw [ofEq_val]

theorem evalV_identity (x : V) : evalV identity.val x = x := by
  rw [identity_val, evalV_pair, evalV_left, evalV_right, mpair_unpair]

theorem evalV_constant (n : ℕ) (x : V) : evalV (constant n).val x = (n : V) := by
  induction n with
  | zero => rw [constant_zero_val, evalV_zero, Nat.cast_zero]
  | succ n ih => rw [constant_succ_val, evalV_comp, evalV_succ, ih, Nat.cast_succ]

theorem evalV_successor (p : R f) (x : V) :
    evalV (successor p).val x = evalV p.val x + 1 := by
  rw [successor_val, evalV_comp, evalV_succ]

/-! #### Addition -/

theorem evalV_addition (a n : V) : evalV addition.val (mpair a n) = a + n := by
  rw [addition_val]
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [evalV_prec_zero, evalV_identity, add_zero]
  case succ n ih =>
    rw [evalV_prec_succ, evalV_comp, evalV_comp, evalV_right, evalV_right, munpair₂_mpair,
      munpair₂_mpair, ih, evalV_succ, add_assoc]

theorem evalV_add (p : R f) (q : R g) (x : V) :
    evalV (add p q).val x = evalV p.val x + evalV q.val x := by
  rw [add_val, evalV_comp, evalV_pair, evalV_addition]

/-! #### Predecessor and truncated subtraction -/

theorem evalV_predecessor (x : V) : evalV predecessor.val x = x - 1 := by
  rw [predecessor_val, evalV_comp, evalV_pair, evalV_zero, evalV_identity]
  by_cases hx : x = 0
  · rw [hx, evalV_prec_zero, evalV_zero]
    exact (LO.FirstOrder.Arithmetic.sub_eq_zero_iff_le.mpr
      (LO.FirstOrder.Arithmetic.zero_le (1 : V))).symm
  · obtain ⟨m, rfl⟩ : ∃ m : V, x = m + 1 := ⟨x - 1, (ModelOptimizer.sub_one_add_one hx).symm⟩
    rw [evalV_prec_succ, evalV_comp, evalV_left, evalV_right, munpair₂_mpair, munpair₁_mpair,
      add_tsub_cancel_right]

theorem evalV_pred (p : R f) (x : V) : evalV (pred p).val x = evalV p.val x - 1 := by
  rw [pred_val, evalV_comp, evalV_predecessor]

theorem evalV_subtraction (a n : V) : evalV subtraction.val (mpair a n) = a - n := by
  rw [subtraction_val]
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [evalV_prec_zero, evalV_identity]
    exact (LO.FirstOrder.Arithmetic.sub_zero a).symm
  case succ n ih =>
    rw [evalV_prec_succ, evalV_comp, evalV_predecessor, evalV_comp, evalV_right, evalV_right,
      munpair₂_mpair, munpair₂_mpair, ih, tsub_tsub]

theorem evalV_sub (p : R f) (q : R g) (x : V) :
    evalV (DirectScalar.sub p q).val x = evalV p.val x - evalV q.val x := by
  rw [sub_val, evalV_comp, evalV_pair, evalV_subtraction]

/-! #### Multiplication -/

theorem evalV_multiplication (a n : V) : evalV multiplication.val (mpair a n) = a * n := by
  rw [multiplication_val]
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [evalV_prec_zero, evalV_zero, mul_zero]
  case succ n ih =>
    rw [evalV_prec_succ, evalV_add, evalV_leftR, evalV_compR, evalV_rightR, evalV_rightR,
      munpair₁_mpair, munpair₂_mpair, munpair₂_mpair, ih, mul_add, mul_one, add_comm]

theorem evalV_mul (p : R f) (q : R g) (x : V) :
    evalV (mul p q).val x = evalV p.val x * evalV q.val x := by
  rw [mul_val, evalV_comp, evalV_pair, evalV_multiplication]

/-! #### Branching -/

theorem evalV_zeroBranch (z n : V) :
    evalV zeroBranch.val (mpair z n) = if n = 0 then munpair₁ z else munpair₂ z := by
  rw [zeroBranch_val]
  by_cases hn : n = 0
  · rw [if_pos hn, hn, evalV_prec_zero, evalV_left]
  · rw [if_neg hn]
    obtain ⟨m, rfl⟩ : ∃ m : V, n = m + 1 := ⟨n - 1, (ModelOptimizer.sub_one_add_one hn).symm⟩
    rw [evalV_prec_succ, evalV_comp, evalV_left, evalV_right, munpair₁_mpair]

theorem evalV_ifZero (p : R f) (q : R g) (r : R h) (x : V) :
    evalV (ifZero p q r).val x =
      if evalV p.val x = 0 then evalV q.val x else evalV r.val x := by
  rw [ifZero_val, evalV_comp, evalV_pair, evalV_pair, evalV_zeroBranch]
  by_cases hp : evalV p.val x = 0
  · rw [if_pos hp, if_pos hp, munpair₁_mpair]
  · rw [if_neg hp, if_neg hp, munpair₂_mpair]

/-- In the model, the two truncated differences vanish together iff the
arguments are equal. -/
theorem sub_add_sub_eq_zero_iff (a b : V) : a - b + (b - a) = 0 ↔ a = b := by
  constructor
  · intro hs
    have h1 : a - b ≤ a - b + (b - a) := le_self_add
    have h2 : b - a ≤ a - b + (b - a) := le_add_self
    rw [hs] at h1 h2
    have e1 : a - b = 0 := le_antisymm h1 (LO.FirstOrder.Arithmetic.zero_le _)
    have e2 : b - a = 0 := le_antisymm h2 (LO.FirstOrder.Arithmetic.zero_le _)
    exact le_antisymm (LO.FirstOrder.Arithmetic.sub_eq_zero_iff_le.mp e1)
      (LO.FirstOrder.Arithmetic.sub_eq_zero_iff_le.mp e2)
  · intro e
    rw [e, LO.FirstOrder.Arithmetic.sub_self, add_zero]

theorem evalV_ifEq (p : R f) (q : R g) (r : R h) (s : R k) (x : V) :
    evalV (ifEq p q r s).val x =
      if evalV p.val x = evalV q.val x then evalV r.val x else evalV s.val x := by
  rw [ifEq_val, evalV_ifZero, evalV_add, evalV_sub, evalV_sub]
  by_cases he : evalV p.val x = evalV q.val x
  · rw [if_pos ((sub_add_sub_eq_zero_iff _ _).mpr he), if_pos he]
  · rw [if_neg (fun hz => he ((sub_add_sub_eq_zero_iff _ _).mp hz)), if_neg he]

/-! #### Iteration -/

/-- The internal iteration of `evalV p.val` from the standard seed `initial`. -/
def iterV (p : R f) (initial : ℕ) (n : V) : V :=
  evalV (.prec (constant initial).val (.comp p.val (.comp .right .right))) (mpair 0 n)

theorem evalV_iterate (p : R f) (initial : ℕ) (n : V) :
    evalV (iterate p initial).val n = iterV p initial n := by
  unfold iterV
  rw [iterate_val, evalV_comp, evalV_pair, evalV_zero, evalV_identity]

theorem iterV_zero (p : R f) (initial : ℕ) : iterV p initial (0 : V) = (initial : V) := by
  unfold iterV
  rw [evalV_prec_zero, evalV_constant]

theorem iterV_succ (p : R f) (initial : ℕ) (n : V) :
    iterV p initial (n + 1) = evalV p.val (iterV p initial n) := by
  unfold iterV
  rw [evalV_prec_succ, evalV_comp, evalV_comp, evalV_right, evalV_right, munpair₂_mpair,
    munpair₂_mpair]

end DiophantineConsistency.ModelDirectScalar
