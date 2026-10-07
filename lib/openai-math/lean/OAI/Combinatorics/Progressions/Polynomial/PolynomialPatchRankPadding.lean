import OAI.Combinatorics.Progressions.Linear.VaryingRankFixedPatchFunction

namespace OAI

section

namespace Erdos3.PolynomialPatch

open scoped BigOperators NNReal

noncomputable def unitRank (σ : Type*) (s d : ℕ) (hs : 1 ≤ s) :
    PolynomialPatch σ s d where
  weight := fun _ => 1
  weight_pos := fun _ => le_rfl
  weight_le := fun _ => hs
  weight_mono := fun _ _ _ => le_rfl
  form := { center := fun _ => 0, degree := fun _ => Submodule.zero_mem _ }
  kernel := localTentKernel d 8 le_rfl

@[simp] theorem unitRank_value {σ : Type*} {s d : ℕ} (hs : 1 ≤ s) (t : σ → ℝ) :
    (unitRank σ s d hs).value t = 1 := by
  change ((unitRank σ s d hs).form.slots t).patchValue (localTentKernel d 8 le_rfl) = 1
  have hres : ((unitRank σ s d hs).form.slots t).residual 0 = 0 := by
    ext i
    simp [unitRank, PolynomialSlots.slots, TriangularSlots.residual]
  rw [TriangularSlots.patchValue_eq_at_residual (b := 0)]
  · rw [hres]
    norm_num [localTentKernel]
  · intro i
    rw [hres]
    norm_num

@[simp] theorem unitRank_lip {σ : Type*} {s d : ℕ} (hs : 1 ≤ s) :
    (unitRank σ s d hs).kernel.lip = 4 := by
  norm_num [unitRank, localTentKernel]

noncomputable def padRank {σ : Type*} {s d D : ℕ}
    (P : PolynomialPatch σ s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    PolynomialPatch σ s D :=
  (P.product (unitRank σ s (D-d) hs)).castRank (Nat.add_sub_of_le hd)

@[simp] theorem padRank_value {σ : Type*} {s d D : ℕ}
    (P : PolynomialPatch σ s d) (hs : 1 ≤ s) (hd : d ≤ D) (t : σ → ℝ) :
    (P.padRank hs hd).value t = P.value t := by
  simp only [padRank, castRank_value, product_value, unitRank_value, mul_one]

@[simp] theorem padRank_lip {σ : Type*} {s d D : ℕ}
    (P : PolynomialPatch σ s d) (hs : 1 ≤ s) (hd : d ≤ D) :
    (P.padRank hs hd).kernel.lip = P.kernel.lip + 4 := by
  simp only [padRank, castRank_kernel_lip, product_lip, unitRank_lip]

theorem padRank_score {σ Ω : Type*} [Fintype Ω] {s d D : ℕ}
    (P : PolynomialPatch σ s d) (hs : 1 ≤ s) (hd : d ≤ D)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (a : ℝ) :
    (𝔼 x, (f x - a) * (P.padRank hs hd).value (t x)) =
      𝔼 x, (f x - a) * P.value (t x) := by
  simp only [padRank_value]

noncomputable def padRankFamily {σ H : Type*} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, PolynomialPatch σ s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) : H → PolynomialPatch σ s D :=
  fun h => (P h).padRank hs (hd h)

@[simp] theorem padRankFamily_value {σ H : Type*} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, PolynomialPatch σ s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) (h : H) (t : σ → ℝ) :
    (padRankFamily d P hs hd h).value t = (P h).value t :=
  padRank_value _ _ _ _

theorem padRankFamily_lip_bound {σ H : Type*} {s D : ℕ}
    (d : H → ℕ) (P : ∀ h, PolynomialPatch σ s (d h))
    (hs : 1 ≤ s) (hd : ∀ h, d h ≤ D) {L : ℝ≥0}
    (hL : ∀ h, (P h).kernel.lip ≤ L) (h : H) :
    (padRankFamily d P hs hd h).kernel.lip ≤ L + 4 := by
  exact (padRank_lip (P h) hs (hd h)).le.trans (add_le_add (hL h) le_rfl)

end Erdos3.PolynomialPatch

end

end OAI
