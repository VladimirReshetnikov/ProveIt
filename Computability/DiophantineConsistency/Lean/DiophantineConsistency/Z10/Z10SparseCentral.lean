import DiophantineConsistency.ModelCarries

/-! # Ten-integer package 106: the sparse central calibration at a plain power of two

The prefix of package 106 uses the sparse rank of packages 101/105,

  `R = L(S + T + 1) − S − 1`, with `L = 2ᵘ` and `S + T < L`,

but its threshold `Y = b · 2^34159017 · Bc^2109` is a plain power of two `2ᵐ`
rather than a square. `noCarry_iff_exp_dvd_sparse` is therefore
`Nine121.SparseCentral.noCarry_iff_sq_dvd_sparse` with the calibration
`m = u + σ(T)` in place of `2ν = u + σ(T)`:

  `2ᵐ ∣ binom (2R) R ↔ σ(S) + σ(T) ≤ σ(S + T) ↔ NoCarry S T`.

The mask of package 106 is the mask of package 105 minus two. The low mask is
`≡ 3 (mod 4)` (`four_three_of_eq`, from its digit-sum identity) and the low
word `g` is divisible by four, so removing the bit of weight two changes
neither the carry condition (`noCarry_low`) nor more than one unit of
population (`population_low`).

Everything is internal: the exponents and the arguments are arbitrary elements
of the model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10SparseCentral
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticBinomPascal ModelCarries
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The sparse calibration at a plain power of two.** -/
theorem noCarry_iff_exp_dvd_sparse {u m S T R : V} (hST : S + T < Exp.exp u)
    (hR : R + S + 1 = Exp.exp u * (S + T + 1)) (hm : m = u + population T) :
    NoCarry S T ↔ Exp.exp m ∣ binom (2 * R) R := by
  have hS : S < Exp.exp u := lt_of_le_of_lt (le_add_right le_rfl) hST
  obtain ⟨s', hs'⟩ : ∃ s', Exp.exp u = S + s' + 1 := by
    have h1 : S + 1 ≤ Exp.exp u := lt_iff_succ_le.mp hS
    refine ⟨Exp.exp u - (S + 1), ?_⟩
    have h2 := add_tsub_cancel_of_le h1
    calc Exp.exp u = S + 1 + (Exp.exp u - (S + 1)) := h2.symm
      _ = S + (Exp.exp u - (S + 1)) + 1 := by ring
  have hs'lt : s' < Exp.exp u := by
    rw [hs']
    exact lt_of_le_of_lt (le_add_left le_rfl) (lt_add_one _)
  have hRe : R = (S + T) * Exp.exp u + s' := by
    apply add_right_cancel (b := S + 1)
    calc R + (S + 1) = R + S + 1 := by ring
      _ = Exp.exp u * (S + T + 1) := hR
      _ = (S + T) * Exp.exp u + Exp.exp u := by ring
      _ = (S + T) * Exp.exp u + s' + (S + 1) := by rw [hs']; ring
  have hpR : population R = population (S + T) + population s' := by
    rw [hRe, ArithmeticBinaryPopulation.concatenate _ _ _ hs'lt]
  have hcS : population S + population s' = u := by
    have h := ArithmeticBinaryPopulation.complement u S hS
    have e : Exp.exp u - 1 - S = s' := by
      rw [hs', add_tsub_cancel_right, add_tsub_cancel_left]
    rwa [e] at h
  rw [exp_dvd_central_iff, hpR, hm, ← hcS, ← population_add_eq_iff]
  constructor
  · intro h
    rw [h]
    exact le_of_eq (by ring)
  · intro h
    apply le_antisymm (population_subadditive S T)
    have h' : population S + population T + population s' ≤
        population (S + T) + population s' := by
      calc population S + population T + population s'
          = population S + population s' + population T := by ring
        _ ≤ population (S + T) + population s' := h
    exact le_of_add_le_add_right h'

/-- A number that is one less than a multiple of four, written additively, is `4q + 3`. -/
theorem four_three_of_eq {L c d : V} (h : L + 4 * c + 1 = 4 * d) : ∃ q, L = 4 * q + 3 := by
  have hcd : c < d := by
    by_contra hcon
    have hdc : d ≤ c := not_lt.mp hcon
    have h1 : 4 * d ≤ 4 * c := mul_le_mul le_rfl hdc (by simp) (by simp)
    have h2 : 4 * c < 4 * d := by
      rw [← h]
      exact lt_of_le_of_lt (le_add_left le_rfl) (lt_add_one _)
    exact not_lt.mpr h1 h2
  obtain ⟨e, rfl⟩ : ∃ e, d = c + 1 + e :=
    ⟨d - (c + 1), (add_tsub_cancel_of_le (lt_iff_succ_le.mp hcd)).symm⟩
  refine ⟨e, ?_⟩
  apply add_right_cancel (b := 4 * c + 1)
  calc L + (4 * c + 1) = L + 4 * c + 1 := by ring
    _ = 4 * (c + 1 + e) := h
    _ = 4 * e + 3 + (4 * c + 1) := by ring

/-- Removing the bit of weight two from `4q + 3` removes one unit of population. -/
theorem population_low (q : V) : population (4 * q + 3) = population (4 * q + 1) + 1 := by
  have e1 : 4 * q + 1 = 2 * (2 * q + 0) + 1 := by ring
  have e3 : 4 * q + 3 = 2 * (2 * q + 1) + 1 := by ring
  have h0 : (0 : V) ≤ 1 := by simp
  rw [e1, e3, population_binary (2 * q + 1) 1 le_rfl, population_binary q 1 le_rfl,
    population_binary (2 * q + 0) 1 le_rfl, population_binary q 0 h0, add_zero]

/-- Against a multiple of four, the bit of weight two of the mask is immaterial. -/
theorem noCarry_low (a q : V) : NoCarry (4 * a) (4 * q + 1) ↔ NoCarry (4 * a) (4 * q + 3) := by
  have ea : 4 * a = 2 * (2 * a + 0) + 0 := by ring
  have e1 : 4 * q + 1 = 2 * (2 * q + 0) + 1 := by ring
  have e3 : 4 * q + 3 = 2 * (2 * q + 1) + 1 := by ring
  have h0 : (0 : V) ≤ 1 := by simp
  have h01 : (0 : V) + 1 ≤ 1 := by simp
  have h00 : (0 : V) + 0 ≤ 1 := by simp
  rw [ea, e1, e3, noCarry_binary (2 * a + 0) (2 * q + 0) 0 1 h0 le_rfl,
    noCarry_binary a q 0 0 h0 h0, noCarry_binary (2 * a + 0) (2 * q + 1) 0 1 h0 le_rfl,
    noCarry_binary a q 0 1 h0 le_rfl]
  simp only [h01, h00, true_and]

#print axioms noCarry_iff_exp_dvd_sparse
#print axioms four_three_of_eq
#print axioms population_low
#print axioms noCarry_low

end DiophantineConsistency.Z10SparseCentral
