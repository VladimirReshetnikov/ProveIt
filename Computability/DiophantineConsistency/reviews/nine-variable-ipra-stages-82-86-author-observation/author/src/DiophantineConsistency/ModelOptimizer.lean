import DiophantineConsistency.ModelScalarPR
import DiophantineConsistency.ScalarPROptimizer
import DiophantineConsistency.ArithmeticCommandFetchPerm222

/-! # The scalar program optimizer inside models of `𝗜𝚺₁`

`ScalarPRCode.optimize` rewrites programs by the rules `smartComp`,
`smartPair` and `smartPrec`; `ScalarPROptimizer.eval_optimize` proves that
it preserves evaluation on `ℕ`. Here the same rules are shown to preserve
the internal semantics `ModelScalarPR.evalV` at every model input,
including nonstandard ones. The three recursion rules (constant zero,
unchanged accumulator, pure counter) need internal `𝚺₁` induction on the
counter, through the `𝚺₁` definability of `evalV` (`evalV_definable`). -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelOptimizer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelScalarPR ScalarPRCode

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The internal semantics of every program is a `𝚺₁`-definable function. -/
instance evalV_definable (c : ScalarPRCode) : 𝚺₁-Function₁[V] (evalV c : V → V) :=
  (evalV_defined c).to_definable

theorem mpair_zero_zero : mpair (0 : V) 0 = 0 :=
  ((mpair_eq_iff (c := (0 : V)) (a := 0) (b := 0)).mpr (Or.inr ⟨le_refl _, by simp⟩)).symm

/-- A nonzero model element is a successor. -/
theorem sub_one_add_one {n : V} (hn : n ≠ 0) : n - 1 + 1 = n :=
  ArithmeticCommandFetchPerm222.pred_add_one n hn

/-! ### The three local rules -/

theorem evalV_smartComp (f g : ScalarPRCode) (x : V) :
    evalV (smartComp f g) x = evalV f (evalV g x) := by
  unfold smartComp
  split <;> simp only [evalV_zero, evalV_left, evalV_right, evalV_pair, evalV_comp,
    munpair₁_mpair, munpair₂_mpair, mpair_unpair]

theorem evalV_smartPair (f g : ScalarPRCode) (x : V) :
    evalV (smartPair f g) x = mpair (evalV f x) (evalV g x) := by
  unfold smartPair
  split
  · rw [evalV_zero, mpair_zero_zero]
  · split_ifs with h
    · subst h
      rw [evalV_comp, evalV_comp, evalV_left, evalV_right, mpair_unpair]
    · exact evalV_pair _ _ x
  · exact evalV_pair _ _ x

/-- Constant-zero recursion. -/
theorem evalV_prec_zero_zero (a n : V) :
    evalV (.prec .zero .zero) (mpair a n) = 0 := by
  by_cases hn : n = 0
  · rw [hn, evalV_prec_zero, evalV_zero]
  · rw [← sub_one_add_one hn, evalV_prec_succ, evalV_zero]

/-- Unchanged-accumulator recursion returns its base value. -/
theorem evalV_prec_previous (f : ScalarPRCode) (a n : V) :
    evalV (.prec f (.comp .right .right)) (mpair a n) = evalV f a := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [evalV_prec_zero]
  case succ n ih =>
    simp only [evalV_prec_succ, evalV_comp, evalV_right, munpair₂_mpair, ih]

/-- Pure-counter recursion returns its counter. -/
theorem evalV_prec_counter (a n : V) :
    evalV (.prec .zero (.comp .succ (.comp .right .right))) (mpair a n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [evalV_prec_zero, evalV_zero]
  case succ n ih =>
    simp only [evalV_prec_succ, evalV_comp, evalV_right, evalV_succ, munpair₂_mpair, ih]

theorem evalV_smartPrec (f g : ScalarPRCode) (x : V) :
    evalV (smartPrec f g) x = evalV (.prec f g) x := by
  have hx : mpair (munpair₁ x) (munpair₂ x) = x := mpair_unpair x
  unfold smartPrec
  split
  · rw [evalV_zero, ← hx, evalV_prec_zero_zero]
  · rw [evalV_smartComp, evalV_left, ← hx, evalV_prec_previous, munpair₁_mpair]
  · rw [evalV_right, ← hx, evalV_prec_counter, munpair₂_mpair]
  · rfl

/-! ### The whole optimizer -/

/-- Recursion respects pointwise internal equality of base and step. -/
theorem evalV_prec_congr {f g f' g' : ScalarPRCode} (hf : ∀ x : V, evalV f' x = evalV f x)
    (hg : ∀ x : V, evalV g' x = evalV g x) (x : V) :
    evalV (.prec f' g') x = evalV (.prec f g) x := by
  have key : ∀ a n : V,
      evalV (.prec f' g') (mpair a n) = evalV (.prec f g) (mpair a n) := by
    intro a n
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero => rw [evalV_prec_zero, evalV_prec_zero, hf]
    case succ n ih => rw [evalV_prec_succ, evalV_prec_succ, ih, hg]
  have h := key (munpair₁ x) (munpair₂ x)
  rwa [mpair_unpair] at h

/-- The optimizer preserves the internal semantics at every model input. -/
theorem evalV_optimize (c : ScalarPRCode) (x : V) : evalV c.optimize x = evalV c x := by
  induction c generalizing x with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair f g hf hg =>
    show evalV (smartPair f.optimize g.optimize) x = evalV (ScalarPRCode.pair f g) x
    rw [evalV_smartPair, hf, hg, evalV_pair]
  | comp f g hf hg =>
    show evalV (smartComp f.optimize g.optimize) x = evalV (ScalarPRCode.comp f g) x
    rw [evalV_smartComp, hg, hf, evalV_comp]
  | prec f g hf hg =>
    show evalV (smartPrec f.optimize g.optimize) x = evalV (ScalarPRCode.prec f g) x
    rw [evalV_smartPrec]
    exact evalV_prec_congr hf hg x

/-- The same for a supplied program with its specification. -/
theorem evalV_realizes_optimize {f : ℕ → ℕ} (p : ScalarPRCode.Realizes f) (x : V) :
    evalV (ScalarPRCode.Realizes.optimize p).val x = evalV p.val x :=
  evalV_optimize p.val x

end DiophantineConsistency.ModelOptimizer
