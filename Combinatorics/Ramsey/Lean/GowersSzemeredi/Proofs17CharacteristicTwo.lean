import GowersSzemeredi.Sections17_18

/-! The unrestricted characteristic version of Lemma 17.1 fails.
Over F₂, even arbitrary one-variable functions cannot polarize x₁*x₂. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- In characteristic two, every sum of one-variable Boolean-cube phases
has zero mixed second difference in the two sidelengths. -/
theorem signedCubeSum_two_mixed_difference
    (phi : (Fin 2 → Bool) → ZMod 2 → ZMod 2) :
    signedCubeSum phi 0 ![0, 0] + signedCubeSum phi 0 ![0, 1] +
      signedCubeSum phi 0 ![1, 0] + signedCubeSum phi 0 ![1, 1] = 0 := by
  classical
  unfold signedCubeSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro e _
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hfour : (4 : ZMod 2) = 0 := by decide
  have hadd : ∀ z : ZMod 2, z + z = 0 := by decide
  by_cases hp : Even (boolWeight e) <;>
    cases h0 : e 0 <;> cases h1 : e 1 <;>
    simp [hp, cubeArgument, Fin.sum_univ_two, h0, h1] <;> ring_nf <;> simp [htwo, hfour, hadd]

/-- The monomial x₁*x₂ has mixed second difference one, so the printed
polarization identity is impossible at N=k=2, even without a degree bound. -/
theorem lemma_17_1_characteristic_two_obstruction :
    ¬ ∃ phi : (Fin 2 → Bool) → ZMod 2 → ZMod 2,
      ∀ s (x : Point 2 2), x 0 * x 1 = signedCubeSum phi s x := by
  rintro ⟨phi, hphi⟩
  have h := signedCubeSum_two_mixed_difference phi
  rw [← hphi 0 ![0, 0], ← hphi 0 ![0, 1],
    ← hphi 0 ![1, 0], ← hphi 0 ![1, 1]] at h
  norm_num at h

def lemma_17_1_without_characteristic_bound : Prop :=
  ∀ (N k : Nat) [NeZero N] [Fact N.Prime],
    ∀ sigma : Point N k → ZMod N, IsMultilinear sigma →
      ∃ phi : (Fin k → Bool) → ZMod N → ZMod N,
        (∀ e, PolynomialOn k Finset.univ (phi e)) ∧
        ∀ s x, sigma x = signedCubeSum phi s x

/-- Separate refutation of the original range, preserving the proposition
being refuted alongside the corrected prime-range theorem. -/
theorem lemma_17_1_characteristic_two_counterexample :
    ¬ lemma_17_1_without_characteristic_bound := by
  classical
  intro claim
  have hm : IsMultilinear (fun x : Point 2 2 => x 0 * x 1) := by
    refine ⟨fun e => if e = (fun _ => true) then 1 else 0, ?_⟩
    intro x
    rw [Finset.sum_eq_single (fun _ : Fin 2 => true)]
    · simp [Fin.prod_univ_two]
    · intro e _ he
      simp only [if_neg he, zero_mul]
    · simp
  obtain ⟨phi, _, hid⟩ := claim 2 2 (fun x => x 0 * x 1) hm
  exact lemma_17_1_characteristic_two_obstruction ⟨phi, hid⟩

end LeanProofs.GowersSzemeredi
