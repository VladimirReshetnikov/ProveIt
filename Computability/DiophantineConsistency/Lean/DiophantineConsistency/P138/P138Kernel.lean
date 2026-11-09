import DiophantineConsistency.Source34.Source34KernelSplit

/-! # The top coefficient of the source34 lower kernel (natural numbers)

`Source34KernelSplit` writes the source34 kernel as `K = ρ^8802 + lower` with `lower < ρ^5496`,
`ρ = 2^121`. The cone calibration of package 138 (`P138Cone`) needs the leading radix-`ρ`
digit of `lower`: it sits at position `5495` and is the selector weight of row `0`,

    c0 = clause (2, 435, 3, 1) = 105534389824824194647382298625,   2^96 ≤ c0 < 3·2^95 − 2.

`coeff_top_low` is a kernel `decide` on the 1979-term sparse list (small numbers only); the
digit is then read off symbolically in `ρ` through `Source34SparseKernel.rho_digit`
(`lower_div`, `lower_nat`). No radix power is ever evaluated: `ρ` stays irreducible and every
power is rewritten with the core `Nat.pow_add`, so all powers keep one instance path. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Kernel
open Mixed121Kernel (rho)
open Source34Kernel Source34KernelSplit

/-- The coefficient of `ρ^5495` in the lower kernel, `clause (2, 435, 3, 1)`. -/
def c0 : ℕ := 105534389824824194647382298625

/-- Only the selector term of row `0` sits at position `5495`. -/
theorem coeff_top_low : SparseRadix.coefficientAt Source34SparseKernel.lowTerms 5495 = c0 := by
  unfold c0
  decide +kernel

attribute [local irreducible] paramKernel rho lowerKernelAt

/-- Reading one radix digit, with every quantity an atom. -/
theorem digit_aux (r P L c S : ℕ) (hr : 0 < r) (hP : 0 < P) (hL : L < r * P)
    (hd : (P * (r * S) + L) / P % r = c) : L / P = c := by
  rw [Nat.mul_add_div hP, Nat.mul_add_mod] at hd
  have hlt : L / P < r := (Nat.div_lt_iff_lt_mul hP).2 hL
  rwa [Nat.mod_eq_of_lt hlt] at hd

theorem lower_div : lowerKernelAt rho / rho ^ 5495 = c0 := by
  have hd := Source34SparseKernel.rho_digit 5495 (by decide)
  rw [← coeff_low_eq 5495 (by decide), coeff_top_low, kernel_split_generic] at hd
  have hr : 0 < rho := by unfold rho; positivity
  have hp : 0 < rho ^ 5495 := Nat.pow_pos_iff.mpr (Or.inl hr)
  have h8802 : rho ^ 8802 = rho ^ 5495 * (rho * rho ^ 3306) := by
    rw [show (8802 : ℕ) = 5495 + (1 + 3306) from rfl, Nat.pow_add rho 5495 (1 + 3306),
      Nat.pow_add rho 1 3306, Nat.pow_one]
  have hL : lowerKernelAt rho < rho * rho ^ 5495 := by
    have h := lower_lt
    rwa [show (5496 : ℕ) = 1 + 5495 from rfl, Nat.pow_add rho 1 5495, Nat.pow_one] at h
  rw [h8802] at hd
  exact digit_aux rho (rho ^ 5495) (lowerKernelAt rho) c0 (rho ^ 3306) hr hp hL hd

theorem lower_nat : c0 * rho ^ 5495 ≤ lowerKernelAt rho ∧ lowerKernelAt rho < (c0 + 1) * rho ^ 5495 := by
  have hr : 0 < rho := by unfold rho; positivity
  have hp : 0 < rho ^ 5495 := Nat.pow_pos_iff.mpr (Or.inl hr)
  have h := Nat.div_add_mod (lowerKernelAt rho) (rho ^ 5495)
  have hm := Nat.mod_lt (lowerKernelAt rho) hp
  rw [lower_div] at h
  generalize rho ^ 5495 = P at h hm hp ⊢
  generalize lowerKernelAt rho = L at h hm ⊢
  generalize L % P = m at h hm
  unfold c0 at h ⊢
  constructor
  · omega
  · omega

theorem c0_lower : 2 ^ 97 ≤ 2 * c0 := by unfold c0; norm_num
theorem c0_upper : 4 * c0 + 10 ≤ 3 * 2 ^ 97 := by unfold c0; norm_num

#print axioms coeff_top_low
#print axioms digit_aux
#print axioms lower_div
#print axioms lower_nat
#print axioms c0_lower
#print axioms c0_upper

end DiophantineConsistency.P138Kernel
