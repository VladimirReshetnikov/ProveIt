import DiophantineConsistency.SplitSourceExistence
import DiophantineConsistency.SplitKernels59

/-! # Literal report59 source and the nine-coordinate arithmetic equation

The four coefficient ports remain parameters with explicit size bounds.
No native compiler calibration or internal ZFC derivation is assumed.
-/

namespace DiophantineConsistency.SplitNineSource59

open SplitSourceWords SplitSourceContract

noncomputable def parameters (ports : Fin 4 → ℤ) : Parameters where
  w := SplitCertificate59.weights
  q := SplitCertificate59.targets
  D0 := SplitKernels59.D0 ports
  D1 := SplitKernels59.D1 ports
  D2 := SplitKernels59.D2 ports

theorem valid_of_kernelBounds (ports : Fin 4 → ℤ) (a : ℕ)
    (hk : SplitWordBounds.KernelBounds (SplitKernels59.D0 ports) (SplitKernels59.D1 ports)
      (SplitKernels59.D2 ports) ((2 : ℤ) ^ a)) : Valid (parameters ports) a := by
  constructor
  · exact SplitCertificate59.weights_injective
  · exact SplitCertificate59.maximum_weight
  · exact ⟨20, rfl⟩
  · exact SplitCertificate59.targets_injective
  · exact SplitCertificate59.maximum_target
  · exact hk

theorem valid_of_portBounds (ports : Fin 4 → ℤ) (p q : ℕ)
    (hp : 1 ≤ p) (hpq : p + 4 ≤ q)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2 ^ p)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2 ^ q)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2 ^ p)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2 * 2 ^ p) :
    Valid (parameters ports) (p + q + 1) :=
  valid_of_kernelBounds ports _ (SplitKernels59.kernelBounds_pow ports p q hp hpq hb hk hm hf)

theorem coefficients_zero_iff_source (ports : Fin 4 → ℤ) (z : Fin 31 → ℕ) :
    (∀ j, (sourcePolynomial (parameters ports) z).coeff (SplitCertificate59.targets j) = 0) ↔
      ∀ j, SplitCertificate59.sourceRows ports (fun i => (z i : ℤ) + 1) j = 0 := by
  unfold sourcePolynomial SplitCoefficientBounds.product parameters
  rw [SplitKernels59.D0_eq, SplitKernels59.D1_eq, SplitKernels59.D2_eq]
  exact SplitCertificate59.coeff_zero_iff_source_zero ports (fun i => (z i : ℤ) + 1)

noncomputable def naturalValue (ports : Fin 4 → ℤ) (a : ℕ) (x : Fin 9 → ℕ) : ℤ :=
  SplitSourceExistence.naturalValue (parameters ports) a x

/-- The full unbounded existence equivalence with the authoritative old-z
source. The source itself rules out the all-one positive tuple. -/
theorem exists_natural_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : Valid (parameters ports) a) :
    (∃ x : Fin 9 → ℕ, naturalValue ports a x = 0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        SplitCertificate59.sourceRows ports (fun i => (z i : ℤ) + 1) j = 0 := by
  change (∃ x : Fin 9 → ℕ, SplitSourceExistence.naturalValue (parameters ports) a x = 0) ↔ _
  rw [SplitSourceExistence.exists_natural_zero_iff_source hd]
  constructor
  · rintro ⟨z, _, hz⟩
    exact ⟨z, (coefficients_zero_iff_source ports z).mp hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, SplitKernels59.source_zero_has_nonzero_digit ports z hz,
      (coefficients_zero_iff_source ports z).mpr hz⟩

theorem exists_natural_zero_iff_source_portBounds (ports : Fin 4 → ℤ) (p q : ℕ)
    (hp : 1 ≤ p) (hpq : p + 4 ≤ q)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2 ^ p)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2 ^ q)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2 ^ p)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2 * 2 ^ p) :
    (∃ x : Fin 9 → ℕ, naturalValue ports (p + q + 1) x = 0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        SplitCertificate59.sourceRows ports (fun i => (z i : ℤ) + 1) j = 0 :=
  exists_natural_zero_iff_source ports _ (valid_of_portBounds ports p q hp hpq hb hk hm hf)

/-- The compact54-sharp exponent follows from the original four port boxes;
no numerical coefficient-height assumption remains. -/
theorem exists_natural_zero_iff_source_compact54 (ports : Fin 4 → ℤ)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2 ^ 429959)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2 ^ 434054)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2 ^ 429959)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2 * 2 ^ 429959) :
    (∃ x : Fin 9 → ℕ, naturalValue ports 864014 x = 0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        SplitCertificate59.sourceRows ports (fun i => (z i : ℤ) + 1) j = 0 :=
  exists_natural_zero_iff_source_portBounds ports 429959 434054 (by decide) (by decide) hb hk hm hf

theorem no_natural_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hd : Valid (parameters ports) a) :
    (∀ x : Fin 9 → ℕ, naturalValue ports a x ≠ 0) ↔
      ¬∃ z : Fin 31 → ℕ, ∀ j,
        SplitCertificate59.sourceRows ports (fun i => (z i : ℤ) + 1) j = 0 := by
  simpa only [not_exists] using not_congr (exists_natural_zero_iff_source ports a hd)

end DiophantineConsistency.SplitNineSource59
