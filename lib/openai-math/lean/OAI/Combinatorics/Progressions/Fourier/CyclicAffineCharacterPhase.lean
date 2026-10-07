import OAI.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
import OAI.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution

namespace OAI

section

namespace Erdos3.CircleFourier

theorem character_sub (x y : Circle) : character (x - y) = character x / character y := by
  have hne : character y ≠ 0 := by
    intro h
    have hn := norm_character y
    rw [h, norm_zero] at hn
    norm_num at hn
  apply (eq_div_iff hne).mpr
  rw [← character_add, sub_add_cancel]

theorem exists_real_character_phase {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ r : ℝ, character (r : Circle) = z := by
  let c : _root_.Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  rw [AddCircle.homeomorphCircle_apply] at ht
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact ⟨r, congrArg (fun c : _root_.Circle => (c : ℂ)) ht⟩

end Erdos3.CircleFourier

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem exists_real_frequency_phase (r : ZMod N) :
    ∃ theta : ℝ, ∀ x : ZMod N,
      CircleFourier.character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = character r x := by
  obtain ⟨theta, htheta⟩ := CircleFourier.exists_real_character_phase (norm_character r 1)
  refine ⟨theta, ?_⟩
  intro x
  have hphase : (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) =
      x.val • (theta : CircleFourier.Circle) := by
    simpa only [nsmul_eq_mul] using
      (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := x.val) (x := theta))
  rw [hphase, CircleFourier.character_nsmul, htheta]
  calc
    _ = character r (x.val • (1 : ZMod N)) := (AddChar.map_nsmul_eq_pow _ _ _).symm
    _ = character r x := by simp

theorem real_frequency_phase_sub {r : ZMod N} {theta : ℝ}
    (htheta : ∀ x : ZMod N,
      CircleFourier.character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = character r x)
    (x z : ZMod N) :
    CircleFourier.character ((((x.val : ℝ) - (z.val : ℝ)) * theta : ℝ) : CircleFourier.Circle) =
      character r (x - z) := by
  rw [sub_mul, AddCircle.coe_sub, CircleFourier.character_sub, htheta, htheta,
    AddChar.map_sub_eq_div]

theorem exists_real_frequency_phases (B : Set N) :
    ∃ theta : B.frequencies → ℝ, ∀ x z : ZMod N, ∀ r : B.frequencies,
      CircleFourier.character ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle) =
        character r (x - z) := by
  classical
  choose theta htheta using (fun r : B.frequencies => exists_real_frequency_phase (r : ZMod N))
  exact ⟨theta, fun x z r => real_frequency_phase_sub (htheta r) x z⟩

end Erdos3.CyclicBohr

end

section

namespace Erdos3

open scoped BigOperators

theorem CircleFourier.character_affine_integer_combination
    {I : Type*} [Fintype I] (a t : ℝ) (b : I → ℝ) (x : I → ℤ) :
    character ((t * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : Circle) =
      character ((t * a : ℝ) : Circle) *
        ∏ i, character ((t * b i : ℝ) : Circle) ^ (x i) := by
  classical
  have hcoe (v : I → ℝ) : ((∑ i, v i : ℝ) : Circle) = ∑ i, (v i : Circle) :=
    map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) v Finset.univ
  rw [mul_add, Finset.mul_sum, AddCircle.coe_add, character_add, hcoe, character_fintype_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← character_zsmul, ← AddCircle.coe_zsmul]
  congr 1
  congr 1
  simp only [zsmul_eq_mul]
  ring

theorem exists_affine_cyclic_character_phase {I : Type*} [Fintype I]
    {N : ℕ} [NeZero N] (ξ : (I → ℤ) →+ ZMod N) (ξ₀ : ZMod N) :
    ∃ (a : ℝ) (b : I → ℝ), ∀ (x : I → ℤ) (n : ZMod N),
      CircleFourier.character
        (((n.val : ℝ) * (a + ∑ i, (x i : ℝ) * b i) : ℝ) : CircleFourier.Circle) =
          AddChar.zmodAddEquiv (ξ₀ + ξ x) n := by
  classical
  obtain ⟨a, ha⟩ := CyclicBohr.exists_real_frequency_phase ξ₀
  choose b hb using fun i => CyclicBohr.exists_real_frequency_phase (ξ (Pi.single i 1))
  simp only [CyclicBohr.character] at ha hb
  refine ⟨a, b, ?_⟩
  intro x n
  have hx : ξ x = ∑ i, (x i) • ξ (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    simp only [map_zsmul]
  rw [CircleFourier.character_affine_integer_combination, ha n, hx]
  simp only [map_add, map_sum, map_zsmul, AddChar.add_apply, AddChar.sum_apply,
    AddChar.zsmul_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [hb i n]

end Erdos3

end

end OAI
