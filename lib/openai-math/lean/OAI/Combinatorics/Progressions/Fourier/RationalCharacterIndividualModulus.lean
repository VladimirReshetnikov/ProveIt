import OAI.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {O : Type*} {N : ℕ}

noncomputable def rationalCharacterIndividualModulus (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) : ℕ := Nat.lcm qW (orderOf χ)

theorem rationalCharacterIndividualModulus_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) (hW : qW ∣ N) :
    rationalCharacterIndividualModulus qW χ ∣ N :=
  Nat.lcm_dvd hW (zmod_character_order_dvd χ)

theorem rationalCharacterIndividualModulus_test_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) :
    qW ∣ rationalCharacterIndividualModulus qW χ := Nat.dvd_lcm_left _ _

theorem rationalCharacterIndividualModulus_order_dvd (qW : ℕ)
    (χ : AddChar (O → ZMod N) ℂ) :
    orderOf χ ∣ rationalCharacterIndividualModulus qW χ := Nat.dvd_lcm_right _ _

variable [NeZero N] (qW : ℕ) [NeZero qW] (χ : AddChar (O → ZMod N) ℂ)

theorem rationalCharacterIndividualModulus_pos :
    0 < rationalCharacterIndividualModulus qW χ :=
  Nat.lcm_pos (NeZero.pos qW) (zmod_character_order_pos χ)

noncomputable instance rationalCharacterIndividualModulus_neZero :
    NeZero (rationalCharacterIndividualModulus qW χ) :=
  ⟨(rationalCharacterIndividualModulus_pos qW χ).ne'⟩

theorem rationalCharacterIndividualModulus_le_mul {T : ℕ} (hχ : orderOf χ ≤ T) :
    rationalCharacterIndividualModulus qW χ ≤ qW * T := by
  exact (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos qW) (zmod_character_order_pos χ))
    (Nat.lcm_dvd_mul qW (orderOf χ))).trans (Nat.mul_le_mul_left qW hχ)

variable (hW : qW ∣ N)

omit [NeZero qW] in
private theorem exists_rationalCharacterIndividualReduction [NeZero qW] :
    ∃ ψ : AddChar (O → ZMod (rationalCharacterIndividualModulus qW χ)) ℂ,
      characterPullback (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW)) ψ = χ ∧
        orderOf ψ = orderOf χ := by
  apply exists_zmodPiReduction_character (rationalCharacterIndividualModulus_dvd qW χ hW) χ
  exact orderOf_dvd_iff_pow_eq_one.mp (rationalCharacterIndividualModulus_order_dvd qW χ)

noncomputable def rationalCharacterIndividualReduction :
    AddChar (O → ZMod (rationalCharacterIndividualModulus qW χ)) ℂ :=
  (exists_rationalCharacterIndividualReduction qW χ hW).choose

theorem rationalCharacterIndividualReduction_order :
    orderOf (rationalCharacterIndividualReduction qW χ hW) = orderOf χ :=
  (exists_rationalCharacterIndividualReduction qW χ hW).choose_spec.2

theorem rationalCharacterIndividualReduction_apply (b : O → ZMod N) :
    rationalCharacterIndividualReduction qW χ hW
        (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW) b) = χ b :=
  congrArg (fun ψ : AddChar (O → ZMod N) ℂ => ψ b)
    (exists_rationalCharacterIndividualReduction qW χ hW).choose_spec.1

theorem rationalCharacterIndividualReduction_intCast (b : O → ℤ) :
    rationalCharacterIndividualReduction qW χ hW
        (fun o => (b o : ZMod (rationalCharacterIndividualModulus qW χ))) =
      χ (fun o => (b o : ZMod N)) := by
  have h := rationalCharacterIndividualReduction_apply qW χ hW (fun o => (b o : ZMod N))
  have hred : zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW)
      (fun o => (b o : ZMod N)) =
        (fun o => (b o : ZMod (rationalCharacterIndividualModulus qW χ))) := by
    funext o
    exact map_intCast (ZMod.castHom (rationalCharacterIndividualModulus_dvd qW χ hW)
      (ZMod (rationalCharacterIndividualModulus qW χ))) (b o)
  rwa [hred] at h

omit [NeZero N] [NeZero qW] in
theorem rationalCharacterIndividualModulus_reduce_test {D : Type*} (b : D → ZMod N) :
    zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ)
        (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW) b) =
      zmodPiReduction hW b := by
  funext o
  exact RingHom.congr_fun (ZMod.castHom_comp
    (rationalCharacterIndividualModulus_test_dvd qW χ)
    (rationalCharacterIndividualModulus_dvd qW χ hW)) (b o)

variable [Fintype O]

theorem rationalCharacterIndividualReduction_phase_uniform
    (phase : ℂ → ℂ) (test : (O → ZMod qW) → ℂ) :
    (𝔼 b : O → ZMod N, phase (χ b) * test (zmodPiReduction hW b)) =
      𝔼 b : O → ZMod (rationalCharacterIndividualModulus qW χ),
        phase (rationalCharacterIndividualReduction qW χ hW b) *
          test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ) b) := by
  have hu := uniform_complexMean_surjective_hom
    (zmodPiReduction (I := O) (rationalCharacterIndividualModulus_dvd qW χ hW))
    (zmodPiReduction_surjective (rationalCharacterIndividualModulus_dvd qW χ hW))
    (fun b => phase (rationalCharacterIndividualReduction qW χ hW b) *
      test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ) b))
  simpa only [FiniteProbabilityWeights.uniform_complexMean,
    rationalCharacterIndividualReduction_apply,
    rationalCharacterIndividualModulus_reduce_test qW χ hW]
    using hu

theorem rationalCharacterIndividualReduction_uniform
    (test : (O → ZMod qW) → ℂ) :
    (𝔼 b : O → ZMod N, χ b * test (zmodPiReduction hW b)) =
      𝔼 b : O → ZMod (rationalCharacterIndividualModulus qW χ),
        rationalCharacterIndividualReduction qW χ hW b *
          test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ) b) :=
  rationalCharacterIndividualReduction_phase_uniform qW χ hW id test

theorem rationalCharacterIndividualReduction_star_uniform
    (test : (O → ZMod qW) → ℂ) :
    (𝔼 b : O → ZMod N, star (χ b) * test (zmodPiReduction hW b)) =
      𝔼 b : O → ZMod (rationalCharacterIndividualModulus qW χ),
        star (rationalCharacterIndividualReduction qW χ hW b) *
          test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ) b) :=
  rationalCharacterIndividualReduction_phase_uniform qW χ hW star test

section Partial

variable {Aux D : Type*} [Fintype D]
variable (χ' : AddChar ((Aux ⊕ D) → ZMod N) ℂ)

theorem rationalCharacterIndividualReduction_partial_phase_uniform
    (aux : Aux → ZMod N) (phase : ℂ → ℂ) (test : (D → ZMod qW) → ℂ) :
    (𝔼 b : D → ZMod N, phase (χ' (Sum.elim aux b)) * test (zmodPiReduction hW b)) =
      𝔼 b : D → ZMod (rationalCharacterIndividualModulus qW χ'),
        phase (rationalCharacterIndividualReduction qW χ' hW
          (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux) b)) *
            test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ') b) := by
  have hphase (b : D → ZMod N) :
      rationalCharacterIndividualReduction qW χ' hW
        (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux)
          (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) b)) =
        χ' (Sum.elim aux b) := by
    have hred : zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW)
        (Sum.elim aux b) =
      Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux)
        (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) b) := by
      funext o
      cases o <;> rfl
    rw [← hred]
    exact rationalCharacterIndividualReduction_apply qW χ' hW _
  have hu := uniform_complexMean_surjective_hom
    (zmodPiReduction (I := D) (rationalCharacterIndividualModulus_dvd qW χ' hW))
    (zmodPiReduction_surjective (rationalCharacterIndividualModulus_dvd qW χ' hW))
    (fun b => phase (rationalCharacterIndividualReduction qW χ' hW
      (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux) b)) *
        test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ') b))
  simpa only [FiniteProbabilityWeights.uniform_complexMean, hphase,
    rationalCharacterIndividualModulus_reduce_test qW χ' hW] using hu

theorem rationalCharacterIndividualReduction_partial_star_uniform
    (aux : Aux → ZMod N) (test : (D → ZMod qW) → ℂ) :
    (𝔼 b : D → ZMod N, star (χ' (Sum.elim aux b)) * test (zmodPiReduction hW b)) =
      𝔼 b : D → ZMod (rationalCharacterIndividualModulus qW χ'),
        star (rationalCharacterIndividualReduction qW χ' hW
          (Sum.elim (zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ' hW) aux) b)) *
            test (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ') b) :=
  rationalCharacterIndividualReduction_partial_phase_uniform qW hW χ' aux star test

end Partial

end Erdos3

end

end OAI
