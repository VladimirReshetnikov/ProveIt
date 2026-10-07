import OAI.Combinatorics.Progressions.Geometry.OneDimensionalBox

namespace OAI

section

namespace Erdos3

theorem imageExtension_comap_eq_indicator {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [DecidableEq B] (φ : A →+ B) (Q : Finset A)
    (hφ : Set.InjOn φ (Q : Set A)) (f : B → ℂ) :
    imageExtension φ Q (fun x => f (φ x)) =
      fun y => f y * finiteIndicator (Q.image φ) y := by
  classical
  funext y
  by_cases hy : y ∈ Q.image φ
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [imageExtension_apply hφ _ hx]
    simp [finiteIndicator, Finset.mem_image_of_mem φ hx]
  · rw [imageExtension_eq_zero]
    · simp [finiteIndicator, hy]
    · rintro ⟨x, hx, hxy⟩
      exact hy (Finset.mem_image.mpr ⟨x, hx, hxy⟩)

theorem cyclicInterval_gowersNorm_pow {N : ℕ} [NeZero N] (a : ℤ) (len j : ℕ)
    (hshort : 2 * ((len : ℤ) - 1) < N) (f : ZMod N → ℂ) :
    gowersNorm (j + 1) (fun x => f x * finiteIndicator (cyclicInterval (a : ZMod N) len) x)
        ^ (2 ^ (j + 1)) =
      ((Nat.card (SupportedCube (j + 1) (Finset.Ico a (a + len) : Set ℤ)) : ℝ) /
        (N : ℝ) ^ (j + 2)) * finiteSupportGowersNorm (j + 1)
          (Finset.Ico a (a + len)) (fun x => f (x : ZMod N)) ^ (2 ^ (j + 1)) := by
  have he := integerInterval_reflectsPairSums N a (a + len) (by omega)
  have hh := finiteSupportGowersNorm_ambient_comparison he j
    (fun x => f ((integerCyclicMap N) x))
  rw [imageExtension_comap_eq_indicator _ _ he.injOn,
    integerInterval_image_cyclicInterval, ZMod.card] at hh
  exact hh

theorem cyclicInterval_gowersNorm_lower_pow {N : ℕ} [NeZero N]
    (a : ℤ) (len j : ℕ) [NeZero len]
    (hshort : 2 * ((len : ℤ) - 1) < N) (f : ZMod N → ℂ)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hvol : δ ≤ (len : ℝ) / N)
    (hloc : η ≤ finiteSupportGowersNorm (j + 1) (Finset.Ico a (a + len))
      (fun x => f (x : ZMod N))) :
    ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * δ ^ (j + 2) * η ^ (2 ^ (j + 1)) ≤
      gowersNorm (j + 1) (fun x => f x * finiteIndicator (cyclicInterval (a : ZMod N) len) x)
        ^ (2 ^ (j + 1)) := by
  rw [cyclicInterval_gowersNorm_pow a len j hshort]
  have hcount := (integerInterval_cubeCount_bounds a len (j + 1)).1
  have hn : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hc : 0 ≤ (1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2) := by positivity
  have hratio : ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * δ ^ (j + 2) ≤
      (Nat.card (SupportedCube (j + 1) (Finset.Ico a (a + len) : Set ℤ)) : ℝ) /
        (N : ℝ) ^ (j + 2) := by
    calc
      _ ≤ ((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * ((len : ℝ) / N) ^ (j + 2) := by
        gcongr
      _ = (((1 : ℝ) / ((j : ℝ) + 2) ^ (j + 2)) * (len : ℝ) ^ (j + 2)) /
          (N : ℝ) ^ (j + 2) := by rw [div_pow, mul_div_assoc]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hn.le _)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hcount
  exact mul_le_mul hratio (pow_le_pow_left₀ hη hloc _) (pow_nonneg hη _)
    (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hn.le _))

end Erdos3

end

end OAI
