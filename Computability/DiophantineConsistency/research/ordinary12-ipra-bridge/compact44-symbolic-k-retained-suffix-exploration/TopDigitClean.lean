import SymbolicKernelBytes
import KernelDigitsBounded
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace TopDigit
open ConcreteSparseKernel ConcreteSparsePositions CompactSymbolicKernelOpaque
attribute [local irreducible] paramKernel

def lowTerms : List (ℕ × ℕ) :=
  [(30,1),(62,1),(1100,1),(2201,1)] ++
  AbstractSparseFamily.twoBands (fun i : Fin 943 => 4393-i.val)
    (fun i => 5495-i.val) selectorWeight ++
  AbstractSparseFamily.twoBands (fun i : Fin 41 => 4393-CompactSymbolicKernel.position i)
    (fun i => 5495-CompactSymbolicKernel.position i) copyWeight

theorem lowTerms_lt : ∀ t ∈ lowTerms, t.1 < 5496 := by
  intro t ht
  simp only [lowTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ((rfl | rfl | rfl | rfl) | hs) | hc
  all_goals try decide
  · apply twoBands_bounded 5496 _ _ _ <;> try exact hs
    all_goals intro i; exact lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  · apply twoBands_bounded 5496 _ _ _ <;> try exact hc
    all_goals intro i; exact lt_of_le_of_lt (Nat.sub_le _ _) (by decide)

theorem coeff_top : SparseRadix.coefficientAt kernelTerms 8849 = 1 := by
  have hnone : lowTerms.filter (fun t => t.1 = 8849) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    exact Nat.ne_of_lt (lt_trans (lowTerms_lt t ht) (by decide))
  have hk : kernelTerms = lowTerms ++ [(8849,1)] := by rfl
  rw [hk]
  simp [SparseRadix.coefficientAt, hnone]

theorem top_digit :
    (paramKernel CompactSymbolicKernel.rho / CompactSymbolicKernel.rho ^ 8849) %
      CompactSymbolicKernel.rho = 1 := by
  rw [KernelDigitsBounded.rho_digit 8849 (by decide), coeff_top]

theorem coeff_gap (j : ℕ) (hj : 5496 ≤ j) (hj' : j < 8849) :
    SparseRadix.coefficientAt kernelTerms j = 0 := by
  have hnone : lowTerms.filter (fun t => t.1 = j) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    exact Nat.ne_of_lt (lt_of_lt_of_le (lowTerms_lt t ht) hj)
  have hk : kernelTerms = lowTerms ++ [(8849,1)] := by rfl
  rw [hk]
  simp [SparseRadix.coefficientAt, hnone, Nat.ne_of_gt hj']

theorem top_quotient :
    paramKernel CompactSymbolicKernel.rho / CompactSymbolicKernel.rho ^ 8849 = 1 := by
  have hlt := KernelDigitsBounded.kernel_lt CompactSymbolicKernel.rho (by rfl)
  have hrho : 0 < CompactSymbolicKernel.rho := by unfold CompactSymbolicKernel.rho; positivity
  have hp : 0 < CompactSymbolicKernel.rho ^ 8849 := pow_pos hrho _
  have hq : paramKernel CompactSymbolicKernel.rho / CompactSymbolicKernel.rho ^ 8849 <
      CompactSymbolicKernel.rho := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    rw [show (8850 : ℕ) = 8849 + 1 by decide, pow_succ] at hlt
    simpa only [mul_comm] using hlt
  have ht := top_digit
  rwa [Nat.mod_eq_of_lt hq] at ht

theorem kernel_bounds : 2 ^ 592883 ≤ paramKernel CompactSymbolicKernel.rho ∧
    paramKernel CompactSymbolicKernel.rho < 2 ^ 592884 := by
  have hp : 0 < CompactSymbolicKernel.rho ^ 8849 := by
    unfold CompactSymbolicKernel.rho; positivity
  have hexp : CompactSymbolicKernel.rho ^ 8849 = 2 ^ 592883 := by
    unfold CompactSymbolicKernel.rho
    rw [← pow_mul]
  constructor
  · rw [← hexp]
    have h := (Nat.le_div_iff_mul_le hp).1 (show 1 ≤
      paramKernel CompactSymbolicKernel.rho / CompactSymbolicKernel.rho ^ 8849 by rw [top_quotient])
    simpa using h
  · have h := (Nat.div_lt_iff_lt_mul hp).1 (show
      paramKernel CompactSymbolicKernel.rho / CompactSymbolicKernel.rho ^ 8849 < 2 by rw [top_quotient]; decide)
    rw [hexp] at h
    rw [show (592884 : ℕ) = 592883 + 1 by decide, pow_succ]
    simpa only [mul_comm] using h

#print axioms TopDigit.coeff_top
#print axioms TopDigit.coeff_gap
#print axioms TopDigit.top_quotient
#print axioms TopDigit.kernel_bounds
end TopDigit
