import OAI.Combinatorics.Progressions.Estimates.PivotStageBoundary

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def twoSlopeAddHom {R : Type*} [CommRing R] (a b : R) : (R × R) →+ (R × R) where
  toFun z := (z.1 + a * z.2, z.1 + b * z.2)
  map_zero' := by simp
  map_add' x y := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem exists_two_slope_characters {R : Type*} [CommRing R]
    (a b : R) (hab : IsUnit (b - a)) (Psi : AddChar (R × R) ℂ) :
    ∃ chi rho : AddChar R ℂ, ∀ x d, Psi (x, d) = chi (x + a * d) * rho (x + b * d) := by
  let e : (R × R) ≃+ (R × R) := AddEquiv.ofBijective (twoSlopeAddHom a b)
    (twoSlopeMap_bijective a b hab)
  let L : R →+ (R × R) := { toFun := fun x => (x, 0), map_zero' := rfl, map_add' := by intros; simp }
  let M : R →+ (R × R) := { toFun := fun y => (0, y), map_zero' := rfl, map_add' := by intros; simp }
  refine ⟨Psi.compAddMonoidHom (e.symm.toAddMonoidHom.comp L),
    Psi.compAddMonoidHom (e.symm.toAddMonoidHom.comp M), ?_⟩
  intro x d
  change Psi (x, d) = Psi (e.symm (x + a * d, 0)) * Psi (e.symm (0, x + b * d))
  have hpair : (x + a * d, 0) + (0, x + b * d) = e (x, d) := by
    change (x + a * d, 0) + (0, x + b * d) = (x + a * d, x + b * d)
    simp
  rw [← AddChar.map_add_eq_mul, ← map_add, hpair, e.symm_apply_apply]

theorem exists_single_slope_characters {R : Type*} [CommRing R]
    (a : R) (Psi : AddChar (R × R) ℂ) :
    ∃ chi rho : AddChar R ℂ, ∀ u d, Psi (u - a * d, d) = chi u * rho d := by
  let L : R →+ (R × R) := { toFun := fun u => (u, 0), map_zero' := rfl, map_add' := by intros; simp }
  let M : R →+ (R × R) := {
    toFun := fun d => (-a * d, d)
    map_zero' := by simp
    map_add' := by intro x y; ext <;> simp [mul_add] }
  refine ⟨Psi.compAddMonoidHom L, Psi.compAddMonoidHom M, ?_⟩
  intro u d
  change Psi (u - a * d, d) = Psi (u, 0) * Psi (-a * d, d)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ext <;> simp [sub_eq_add_neg]

theorem complex_expect_pivot_change {R : Type*} [Ring R] [Fintype R]
    (a : R) (F : R → R → ℂ) :
    (𝔼 x, 𝔼 d, F x d) = 𝔼 u, 𝔼 d, F (u - a * d) d := by
  rw [Finset.expect_comm, Finset.expect_comm (Finset.univ : Finset R) (Finset.univ : Finset R)
    (fun u d => F (u - a * d) d)]
  apply Finset.expect_congr rfl
  intro d _
  symm
  apply Fintype.expect_equiv (Equiv.addRight (-(a * d)))
  intro u
  change F (u - a * d) d = F (u + -(a * d)) d
  rw [sub_eq_add_neg]

theorem complex_expect_single_slope {R : Type*} [Ring R] [Fintype R]
    (a : R) (f : R → ℂ) : (𝔼 x, 𝔼 d, f (x + a * d)) = 𝔼 u, f u := by
  rw [complex_expect_pivot_change a]
  simp only [sub_add_cancel, Fintype.expect_const]

theorem exists_single_slope_character_bound {R : Type*} [CommRing R] [Fintype R]
    (a : R) (Psi : AddChar (R × R) ℂ) (f : R → ℂ) :
    ∃ chi : AddChar R ℂ,
      ‖𝔼 x, 𝔼 d, Psi (x, d) * f (x + a * d)‖ ≤ ‖𝔼 u, chi u * f u‖ := by
  obtain ⟨chi, rho, hfactor⟩ := exists_single_slope_characters a Psi
  refine ⟨chi, ?_⟩
  rw [complex_expect_pivot_change a]
  simp only [sub_add_cancel, hfactor]
  have he : (𝔼 u, 𝔼 d, chi u * rho d * f u) =
      (𝔼 u, chi u * f u) * (𝔼 d, rho d) := by
    have hpoint (u d : R) : chi u * rho d * f u = (chi u * f u) * rho d := by ring
    simp only [hpoint, ← Finset.mul_expect, ← Finset.expect_mul]
  rw [he, norm_mul]
  have hrho : ‖𝔼 d, rho d‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    simp only [AddChar.norm_apply, Fintype.expect_const]
    exact le_rfl
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hrho (norm_nonneg _)

end Erdos3

end

end OAI
