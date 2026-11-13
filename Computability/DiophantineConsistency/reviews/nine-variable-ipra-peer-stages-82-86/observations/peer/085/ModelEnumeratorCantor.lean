import DiophantineConsistency.ModelDirectScalar
import DiophantineConsistency.DirectScalarEnumeratorCore
import BusyBeaver.ZFC.ArithmeticCode254

/-! # Internal Cantor pairing and formula codes of the enumerator program

`DirectEnumerator` (file `DirectScalarEnumeratorCore`) computes the literal
Cantor pairing `P a b = tri (a+b) + b` of the C222 calculus with scalar
programs: the triangular numbers by recursion, the pairing by addition, and
the inverse pairing `unP` by *iterating* the anti-diagonal walk
`cantorWalkStep` from `0`. Here their internal semantics are identified with
the model-level Cantor package `ArithmeticCantor` (`triangle`, `cantor`,
`first`, `second`) used by the internal machine `ArithmeticEnumStepPerm222`:

* `evalV_triangular`: `triangle`;
* `evalV_cantorPair`: `cantor`;
* `evalV_cantorUnpair`: `x ↦ ⟪first x, second x⟫` (Foundation pairing of the
  two Cantor projections), by internal induction along the walk, using the
  successor law `cantor_add_one`;
* `evalV_unpairLeft`/`evalV_unpairRight`: `first`/`second`;
* the formula constructors `implication`, `membership`, `universal`,
  `equality`, `negation`, `existential`: `wim`, `wel`, `wal`, `weq` of
  `ArithmeticCode254`, with the relative falsity code `1`.

This is the translation layer between the program's Foundation-paired
registers and the machine's Cantor-coded formulas. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelEnumeratorCantor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelScalarPR ScalarPRCode DirectScalar ModelDirectScalar DirectEnumerator
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor SetTheory.BusyBeaver.ZFC.ArithmeticCode254

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance first_definable' : 𝚺₁-Function₁[V] (first : V → V) := first_defined.to_definable₀
instance second_definable' : 𝚺₁-Function₁[V] (second : V → V) := second_defined.to_definable₀

/-! ### Cantor arithmetic in the model -/

theorem triangle_zero' : triangle (0 : V) = 0 := by simp [triangle]

theorem cantor_zero_zero : cantor (0 : V) 0 = 0 := by
  rw [cantor, add_zero, add_zero, triangle_zero']

theorem first_zero' : first (0 : V) = 0 := by
  have h := first_cantor (0 : V) 0
  rwa [cantor_zero_zero] at h

theorem second_zero' : second (0 : V) = 0 := by
  have h := second_cantor (0 : V) 0
  rwa [cantor_zero_zero] at h

/-- One step along the anti-diagonal. -/
theorem cantor_add_one (a b : V) :
    cantor a b + 1 = if a = 0 then cantor (b + 1) 0 else cantor (a - 1) (b + 1) := by
  by_cases ha : a = 0
  · rw [if_pos ha, ha]
    unfold cantor
    rw [zero_add, add_zero, add_zero, triangle_succ]
  · rw [if_neg ha]
    obtain ⟨c, rfl⟩ : ∃ c : V, a = c + 1 := ⟨a - 1, (ModelOptimizer.sub_one_add_one ha).symm⟩
    rw [add_tsub_cancel_right]
    unfold cantor
    rw [add_assoc c 1 b, add_comm 1 b, add_assoc]

/-! ### Code of the Cantor programs, one level deep -/

theorem triangular_val :
    triangular.val = .comp (.prec .zero (successor (add (Realizes.right.comp Realizes.right)
      (Realizes.left.comp Realizes.right))).val) (.pair .zero identity.val) := rfl

theorem cantorPairCore_val :
    cantorPairCore.val = (add Realizes.right (triangular.comp (add Realizes.left Realizes.right))).val :=
  rfl

theorem cantorPair_val {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    (cantorPair ha hb).val = .comp cantorPairCore.val (.pair ha.val hb.val) := rfl

theorem cantorWalkStep_val : cantorWalkStep.val =
    (ifZero Realizes.left ((successor Realizes.right).pair Realizes.zero)
      ((DirectScalar.sub Realizes.left (constant 1)).pair (successor Realizes.right))).val := rfl

theorem cantorUnpair_val : cantorUnpair.val = (iterate cantorWalkStep 0).val := rfl

theorem unpairLeft_val {a : ℕ → ℕ} (ha : R a) :
    (unpairLeft ha).val = .comp (.comp .left cantorUnpair.val) ha.val := rfl

theorem unpairRight_val {a : ℕ → ℕ} (ha : R a) :
    (unpairRight ha).val = .comp (.comp .right cantorUnpair.val) ha.val := rfl

/-! ### Internal semantics of the Cantor programs -/

theorem evalV_triangular (n : V) : evalV triangular.val n = triangle n := by
  rw [triangular_val, evalV_comp, evalV_pair, evalV_zero, evalV_identity]
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [evalV_prec_zero, evalV_zero, triangle_zero']
  case succ n ih =>
    simp only [evalV_prec_succ, evalV_successor, evalV_add, evalV_compR, evalV_rightR,
      evalV_leftR, munpair₁_mpair, munpair₂_mpair, ih, triangle_succ]

theorem evalV_cantorPairCore (x : V) :
    evalV cantorPairCore.val x = cantor (munpair₁ x) (munpair₂ x) := by
  rw [cantorPairCore_val, evalV_add, evalV_rightR, evalV_compR, evalV_triangular, evalV_add,
    evalV_leftR, evalV_rightR, cantor, add_comm (munpair₂ x)]

theorem evalV_cantorPair {a b : ℕ → ℕ} (ha : R a) (hb : R b) (x : V) :
    evalV (cantorPair ha hb).val x = cantor (evalV ha.val x) (evalV hb.val x) := by
  rw [cantorPair_val, evalV_comp, evalV_pair, evalV_cantorPairCore, munpair₁_mpair,
    munpair₂_mpair]

theorem evalV_cantorWalkStep (x : V) :
    evalV cantorWalkStep.val x =
      if munpair₁ x = 0 then mpair (munpair₂ x + 1) 0
      else mpair (munpair₁ x - 1) (munpair₂ x + 1) := by
  rw [cantorWalkStep_val, evalV_ifZero, evalV_leftR, evalV_pairR, evalV_pairR, evalV_successor,
    evalV_rightR, evalV_zeroR, evalV_sub, evalV_leftR, evalV_constant,
    Nat.cast_one]

/-- The iterated anti-diagonal walk is the Cantor inverse, Foundation-paired. -/
theorem evalV_cantorUnpair (n : V) :
    evalV cantorUnpair.val n = mpair (first n) (second n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [cantorUnpair_val, evalV_iterate, iterV_zero, Nat.cast_zero, first_zero', second_zero',
      ModelOptimizer.mpair_zero_zero]
  case succ n ih =>
    have hs : evalV cantorUnpair.val (n + 1) =
        evalV cantorWalkStep.val (evalV cantorUnpair.val n) := by
      rw [cantorUnpair_val, evalV_iterate, evalV_iterate, iterV_succ]
    rw [hs, ih, evalV_cantorWalkStep, munpair₁_mpair, munpair₂_mpair]
    have hn := cantor_add_one (first n) (second n)
    rw [cantor_projections] at hn
    by_cases h0 : first n = 0
    · rw [if_pos h0] at hn ⊢
      rw [hn, first_cantor, second_cantor]
    · rw [if_neg h0] at hn ⊢
      rw [hn, first_cantor, second_cantor]

theorem evalV_unpairLeft {a : ℕ → ℕ} (ha : R a) (x : V) :
    evalV (unpairLeft ha).val x = first (evalV ha.val x) := by
  rw [unpairLeft_val, evalV_comp, evalV_comp, evalV_left, evalV_cantorUnpair, munpair₁_mpair]

theorem evalV_unpairRight {a : ℕ → ℕ} (ha : R a) (x : V) :
    evalV (unpairRight ha).val x = second (evalV ha.val x) := by
  rw [unpairRight_val, evalV_comp, evalV_comp, evalV_right, evalV_cantorUnpair, munpair₂_mpair]

/-! ### Formula constructors -/

section Formulas
variable {a b : ℕ → ℕ} (ha : R a) (hb : R b) (x : V)

theorem evalV_implication :
    evalV (implication ha hb).val x = wim (evalV ha.val x) (evalV hb.val x) := by
  unfold implication
  rw [evalV_mul, evalV_constant, evalV_cantorPair]
  simp only [wim, tagged, add_zero, Nat.cast_ofNat]

theorem evalV_membership :
    evalV (membership ha hb).val x = wel (evalV ha.val x) (evalV hb.val x) := by
  unfold membership
  rw [evalV_successor, evalV_implication]
  simp only [wim, wel, tagged, add_zero]

theorem evalV_universal :
    evalV (universal ha hb).val x = wal (evalV ha.val x) (evalV hb.val x) := by
  unfold universal
  rw [evalV_add, evalV_implication, evalV_constant]
  simp only [wim, wal, tagged, add_zero, Nat.cast_ofNat]

theorem evalV_equality :
    evalV (equality ha hb).val x = weq (evalV ha.val x) (evalV hb.val x) := by
  unfold equality
  rw [evalV_add, evalV_implication, evalV_constant]
  simp only [wim, weq, tagged, add_zero, Nat.cast_ofNat]

theorem evalV_negation : evalV (negation ha).val x = wim (evalV ha.val x) 1 := by
  unfold negation
  rw [evalV_implication, evalV_constant, Nat.cast_one]

theorem evalV_existential :
    evalV (existential ha hb).val x = wim (wal (evalV ha.val x) (wim (evalV hb.val x) 1)) 1 := by
  unfold existential
  rw [evalV_negation, evalV_universal, evalV_negation]

end Formulas

end DiophantineConsistency.ModelEnumeratorCantor
