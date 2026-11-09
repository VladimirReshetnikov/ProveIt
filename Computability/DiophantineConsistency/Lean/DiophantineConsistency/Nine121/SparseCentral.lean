import DiophantineConsistency.ModelCarries

/-! # The sparse central-binomial calibration in every model of `𝗜𝚺₁`

The 101/105 nine-variable prefixes do not use Jones's `R = S(N² − N) + (T + 1)(N² − 1)`
(`ModelCarries.noCarry_iff_sq_dvd_central`) but the sparse rank

  `R = L(S + T + 1) − S − 1`, with `L = 2ᵘ` and `S + T < L`,

whose binary expansion is the concatenation of `S + T` above the complement
`L − 1 − S`. Hence `σ(R) = σ(S + T) + u − σ(S)`, and with the calibrated
threshold `N = 2^ν`, `2ν = u + σ(T)`, Legendre's formula (Lemma 2.15,
`ModelCarries.exp_dvd_central_iff`) gives

  `N² ∣ binom (2R) R ↔ σ(S) + σ(T) ≤ σ(S + T) ↔ NoCarry S T`.

Everything is internal: the exponents `u, ν` and the arguments are arbitrary
elements of the model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Nine121.SparseCentral
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticBinomPascal ModelCarries
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The sparse calibration.** -/
theorem noCarry_iff_sq_dvd_sparse {u ν S T R : V} (hST : S + T < Exp.exp u)
    (hR : R + S + 1 = Exp.exp u * (S + T + 1)) (hν : 2 * ν = u + population T) :
    NoCarry S T ↔ Exp.exp ν ^ 2 ∣ binom (2 * R) R := by
  have hS : S < Exp.exp u := lt_of_le_of_lt (le_add_right le_rfl) hST
  -- the complement `s' = L − 1 − S`
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
  have hsq : Exp.exp ν ^ 2 = Exp.exp (2 * ν) := by
    rw [two_mul, exp_add, pow_two]
  rw [hsq, exp_dvd_central_iff, hpR, hν, ← hcS, ← population_add_eq_iff]
  constructor
  · intro h
    rw [h]
    exact le_of_eq (by ring)
  · intro h
    apply le_antisymm (population_subadditive S T)
    have h' : population S + population T + population s' ≤ population (S + T) + population s' := by
      calc population S + population T + population s' = population S + population s' + population T := by
            ring
        _ ≤ population (S + T) + population s' := h
    exact le_of_add_le_add_right h'

end Nine121.SparseCentral

#print axioms Nine121.SparseCentral.noCarry_iff_sq_dvd_sparse
