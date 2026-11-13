import DiophantineConsistency.Compact44.AbstractSparseFamily
import DiophantineConsistency.Compact44.SparseCountBound
import DiophantineConsistency.Source34.Source34KernelFiniteCert
import DiophantineConsistency.Mixed121.Mixed121SparseKernel

/-! # The source34 kernel as a sparse radix-`r` numeral

`Mixed121SparseKernel` at the source34 tuple. `Source34Kernel.paramKernel r` is
the weighted sum of 1979 terms `(exponent, weight)`: the bare exponents
`40, 41, 1100, 2200`; both reflected bands of the 943 clause coefficients and
of the 44 extra weights at the source34 positions; and `8802 = 8801 + 1`
(121x8801: `30, 62, 1100, 2200` and `8843 = 8801 + 42`). Every exponent is
below `8803` and every weight at most `2^99`, so for any radix `r ≥ 2^121`
the radix-`r` digits of the kernel are its sparse coefficients
(`kernel_digit`). The top digit `8802` is `1` and the digits `5496..8801`
vanish, so `2^1065042 ≤ K < 2^1065043` at `r = 2^121` (`kernel_bounds`).

Generic and used from `Mixed121SparseKernel`: `selectorWeight`, `copyWeight`,
`twoBands_bounded`, `twoBands_weights`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34SparseKernel
open Mixed121Kernel (rho clause W)
open Source34Kernel Source34KernelFiniteCert
open Mixed121SparseKernel (selectorWeight copyWeight twoBands_bounded twoBands_weights)
open scoped BigOperators

def kernelTerms : List (ℕ × ℕ) :=
  [(40,1),(41,1),(1100,1),(2200,1)] ++
  AbstractSparseFamily.twoBands (fun i : Fin 943 => 4393-i.val)
    (fun i => 5495-i.val) selectorWeight ++
  AbstractSparseFamily.twoBands (fun k : Fin 44 => 4393-extraPos k)
    (fun k => 5495-extraPos k) copyWeight ++ [(8802,1)]

theorem kernel_weighted_sum (r : ℕ) :
    paramKernel r = (kernelTerms.map (fun t => t.2 * r ^ t.1)).sum := by
  simp only [kernelTerms, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, one_mul, AbstractSparseFamily.twoBands_weighted_sum,
    paramKernel, selectorWeight, copyWeight]
  rw [show (8802 : ℕ) = 8801 + 1 by decide, pow_add]
  ring

/-! ## Positions -/

theorem kernel_positions_bounded : ∀ t ∈ kernelTerms, t.1 < 8803 := by
  intro t ht
  simp only [kernelTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with (((rfl | rfl | rfl | rfl) | hs) | hc) | rfl
  all_goals try decide
  · apply twoBands_bounded 8803 _ _ _ _ _ t hs <;> intro i <;>
      have h := reflected_range i.val (selector_allowed i) <;> omega
  · apply twoBands_bounded 8803 _ _ _ _ _ t hc <;> intro i <;>
      have h := reflected_range (extraPos i) (extra_allowed i) <;> omega

/-! ## Digits -/

theorem kernel_ofDigits (r : ℕ) :
    paramKernel r = Nat.ofDigits r ((List.range 8803).map (SparseRadix.coefficientAt kernelTerms)) := by
  rw [SparseRadix.ofDigits_map_range, SparseRadix.sparse_sum r 8803 kernelTerms kernel_positions_bounded]
  exact kernel_weighted_sum r

theorem kernel_weights_bound : ∀ t ∈ kernelTerms, t.2 ≤ 2^99 := by
  intro t ht
  simp only [kernelTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with (((rfl | rfl | rfl | rfl) | hs) | hc) | rfl
  all_goals try decide
  · exact twoBands_weights _ _ _ _ (fun i => le_of_lt (Mixed121Flatten.clause_lt _)) t hs
  · exact twoBands_weights _ _ _ _ (fun k => le_of_lt (lt_trans (Mixed121Flatten.W_lt k.val k.isLt)
      (Nat.pow_lt_pow_right (by decide) (by decide)))) t hc

theorem kernel_terms_length : kernelTerms.length = 1979 := by
  simp only [kernelTerms, List.length_append, List.length_cons, List.length_nil,
    AbstractSparseFamily.twoBands, AbstractSparseFamily.terms, List.length_ofFn]

theorem kernel_coefficient_bound (r j : ℕ) (hr : 2^121 ≤ r) :
    SparseRadix.coefficientAt kernelTerms j < r := by
  have h := SparseCountBound.coefficient_le_length_mul kernelTerms j (2^99) kernel_weights_bound
  rw [kernel_terms_length] at h
  have hsmall : 1979 * 2^99 < 2^121 := by norm_num
  omega

theorem kernel_digit (r i : ℕ) (hr : 2^121 ≤ r) (hi : i < 8803) :
    (paramKernel r / r ^ i) % r = SparseRadix.coefficientAt kernelTerms i := by
  have hp : 0 < r := lt_of_lt_of_le (by norm_num) hr
  rw [kernel_weighted_sum r]
  exact SparseRadix.sparse_terms_digit r 8803 i kernelTerms hp kernel_positions_bounded
    (fun j _ => kernel_coefficient_bound r j hr) hi

theorem kernel_lt (r : ℕ) (hr : 2^121 ≤ r) : paramKernel r < r ^ 8803 := by
  have hp : 1 < r := lt_of_lt_of_le (by norm_num) hr
  have h := SparseRadix.finite_sum_lt r 8803 (SparseRadix.coefficientAt kernelTerms) hp
    (fun j _ => kernel_coefficient_bound r j hr)
  rw [SparseRadix.sparse_sum r 8803 kernelTerms kernel_positions_bounded, ← kernel_weighted_sum r] at h
  exact h

theorem rho_digit (i : ℕ) (hi : i < 8803) :
    (paramKernel rho / rho ^ i) % rho = SparseRadix.coefficientAt kernelTerms i :=
  kernel_digit rho i le_rfl hi

/-! ## The top digit -/

def lowTerms : List (ℕ × ℕ) :=
  [(40,1),(41,1),(1100,1),(2200,1)] ++
  AbstractSparseFamily.twoBands (fun i : Fin 943 => 4393-i.val)
    (fun i => 5495-i.val) selectorWeight ++
  AbstractSparseFamily.twoBands (fun k : Fin 44 => 4393-extraPos k)
    (fun k => 5495-extraPos k) copyWeight

theorem lowTerms_lt : ∀ t ∈ lowTerms, t.1 < 5496 := by
  intro t ht
  simp only [lowTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ((rfl | rfl | rfl | rfl) | hs) | hc
  all_goals try decide
  · apply twoBands_bounded 5496 _ _ _ <;> try exact hs
    all_goals intro i; exact lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  · apply twoBands_bounded 5496 _ _ _ <;> try exact hc
    all_goals intro i; exact lt_of_le_of_lt (Nat.sub_le _ _) (by decide)

theorem kernelTerms_split : kernelTerms = lowTerms ++ [(8802,1)] := by
  simp only [kernelTerms, lowTerms, List.append_assoc]

theorem coeff_top : SparseRadix.coefficientAt kernelTerms 8802 = 1 := by
  have hnone : lowTerms.filter (fun t => t.1 = 8802) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    exact Nat.ne_of_lt (lt_trans (lowTerms_lt t ht) (by decide))
  rw [kernelTerms_split]
  simp [SparseRadix.coefficientAt, hnone]

theorem coeff_gap (j : ℕ) (hj : 5496 ≤ j) (hj' : j < 8802) :
    SparseRadix.coefficientAt kernelTerms j = 0 := by
  have hnone : lowTerms.filter (fun t => t.1 = j) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    exact Nat.ne_of_lt (lt_of_lt_of_le (lowTerms_lt t ht) hj)
  rw [kernelTerms_split]
  simp [SparseRadix.coefficientAt, hnone, Nat.ne_of_gt hj']

theorem top_digit : (paramKernel rho / rho ^ 8802) % rho = 1 := by
  rw [rho_digit 8802 (by decide), coeff_top]

theorem top_quotient : paramKernel rho / rho ^ 8802 = 1 := by
  have hlt := kernel_lt rho le_rfl
  have hrho : 0 < rho := by unfold rho; positivity
  have hp : 0 < rho ^ 8802 := pow_pos hrho _
  have hq : paramKernel rho / rho ^ 8802 < rho := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    rw [show (8803 : ℕ) = 8802 + 1 by decide, pow_succ] at hlt
    simpa only [mul_comm] using hlt
  have ht := top_digit
  rwa [Nat.mod_eq_of_lt hq] at ht

theorem kernel_bounds : 2 ^ 1065042 ≤ paramKernel rho ∧ paramKernel rho < 2 ^ 1065043 := by
  have hp : 0 < rho ^ 8802 := by unfold rho; positivity
  have hexp : rho ^ 8802 = 2 ^ 1065042 := by
    unfold rho
    rw [← pow_mul]
  constructor
  · rw [← hexp]
    have h := (Nat.le_div_iff_mul_le hp).1 (show 1 ≤ paramKernel rho / rho ^ 8802 by rw [top_quotient])
    simpa using h
  · have h := (Nat.div_lt_iff_lt_mul hp).1 (show paramKernel rho / rho ^ 8802 < 2 by
      rw [top_quotient]; decide)
    rw [hexp] at h
    rw [show (1065043 : ℕ) = 1065042 + 1 by decide, pow_succ]
    simpa only [mul_comm] using h

#print axioms Source34SparseKernel.kernel_weighted_sum
#print axioms Source34SparseKernel.kernel_digit
#print axioms Source34SparseKernel.kernel_lt
#print axioms Source34SparseKernel.coeff_gap
#print axioms Source34SparseKernel.kernel_bounds
end Source34SparseKernel
