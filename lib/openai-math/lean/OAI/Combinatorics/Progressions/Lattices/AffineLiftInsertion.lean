import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialPatchComposition

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ ρ : Type*} {D E s : ℕ}

noncomputable def affineLiftSubstitution (c : ρ → ℝ) (M : ρ → Fin D → ℝ) :
    σ ⊕ ρ → MvPolynomial (σ ⊕ Fin D) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (fun a => C (c a) + ∑ j, M a j • X (Sum.inr j))

theorem affineLiftSubstitution_degree {p : ρ → ℕ} {w : Fin D → ℕ}
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → w j ≤ p a) (a : σ ⊕ ρ) :
    affineLiftSubstitution c M a ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w)
      (Sum.elim (fun _ : σ => 1) p a) := by
  classical
  cases a with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr a =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    apply (weightedSupportLE _ _).sum_mem
    intro j _
    by_cases hj : M a j = 0
    · simp only [hj, zero_smul]
      exact (weightedSupportLE _ _).zero_mem
    · exact weightedSupportLE_mono (hM a j hj)
        ((weightedSupportLE _ _).smul_mem (M a j)
          (weightedSupportLE_X (Sum.elim (fun _ : σ => 1) w) (Sum.inr j)))

theorem affineLiftSubstitution_eval (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (t : σ → ℝ) (x : Fin D → ℝ) (a : σ ⊕ ρ) :
    aeval (Sum.elim t x) (affineLiftSubstitution c M a) =
      Sum.elim t (fun a => c a + ∑ j, M a j * x j) a := by
  cases a <;> simp [affineLiftSubstitution]

namespace PolynomialPatch

noncomputable def insertAffineLifts {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a) : PolynomialPatch σ s (D + E) :=
  A.insertLifts (B.reparam (affineLiftSubstitution c M) (affineLiftSubstitution_degree c M hM))

@[simp] theorem insertAffineLifts_lip {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a) :
    (A.insertAffineLifts B c M hM).kernel.lip = A.kernel.lip + B.kernel.lip := rfl

theorem insertAffineLifts_value_at_lift {p : ρ → ℕ} (A : PolynomialPatch σ s D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ)
    (hM : ∀ a j, M a j ≠ 0 → A.weight j ≤ p a)
    (t : σ → ℝ) (b : Fin D → ℤ)
    (hb : ∀ i, |(A.form.slots t).residual b i| ≤ 1 / 3) :
    (A.insertAffineLifts B c M hM).value t =
      A.kernel.value ((A.form.slots t).residual b) *
        B.value (Sum.elim t (fun a => c a + ∑ j, M a j * (b j : ℝ))) := by
  unfold insertAffineLifts
  rw [insertLifts_value_at_lift _ _ t b hb, WeightedParameterPatch.reparam_value]
  simp only [affineLiftSubstitution_eval]

theorem exists_affine_lift_insertion {p : ρ → ℕ} (w : Fin D → ℕ)
    (hw : ∀ i, 1 ≤ w i) (hws : ∀ i, w i ≤ s) (hmono : Monotone w)
    (P : Fin D → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) (Φ : PatchKernel D)
    (B : WeightedParameterPatch (σ ⊕ ρ) (Sum.elim (fun _ => 1) p) s E)
    (c : ρ → ℝ) (M : ρ → Fin D → ℝ) (hM : ∀ a j, M a j ≠ 0 → w j ≤ p a) :
    ∃ Q : PolynomialPatch σ s (D + E), Q.kernel.lip = Φ.lip + B.kernel.lip ∧
      ∀ (t : σ → ℝ) (b : Fin D → ℤ),
        (∀ i, |(b i : ℝ) - aeval t (P i)| ≤ 1 / 3) →
        Q.value t = Φ.value (fun i => (b i : ℝ) - aeval t (P i)) *
          B.value (Sum.elim t (fun a => c a + ∑ j, M a j * (b j : ℝ))) := by
  let A := ofCoordinates w hw hws hmono P hP Φ
  refine ⟨A.insertAffineLifts B c M hM, rfl, ?_⟩
  intro t b hb
  have hres : (A.form.slots t).residual b = fun i => (b i : ℝ) - aeval t (P i) :=
    ofCoordinates_residual w hw hws hmono P hP Φ t b
  rw [insertAffineLifts_value_at_lift A B c M hM t b (by simpa only [hres] using hb), hres]
  rfl

end PolynomialPatch
end Erdos3

end

end OAI
