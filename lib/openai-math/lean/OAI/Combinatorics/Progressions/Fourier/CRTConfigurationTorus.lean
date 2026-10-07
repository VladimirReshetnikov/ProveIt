import Mathlib.Data.ZMod.QuotientRing
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def crtConfigurationEquiv {J : Type*} [Fintype J] (N : J → ℕ)
    (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) :
    (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ≃+ ((t : J × Bool) → ZMod (N t.1)) where
  toFun z t := if t.2 then ZMod.prodEquivPi N hN z.2 t.1 else ZMod.prodEquivPi N hN z.1 t.1
  invFun w := ((ZMod.prodEquivPi N hN).symm (fun j => w (j, false)),
    (ZMod.prodEquivPi N hN).symm (fun j => w (j, true)))
  left_inv z := by
    apply Prod.ext
    · change (ZMod.prodEquivPi N hN).symm (ZMod.prodEquivPi N hN z.1) = z.1
      exact (ZMod.prodEquivPi N hN).symm_apply_apply z.1
    · change (ZMod.prodEquivPi N hN).symm (ZMod.prodEquivPi N hN z.2) = z.2
      exact (ZMod.prodEquivPi N hN).symm_apply_apply z.2
  right_inv w := by
    funext ⟨j, b⟩
    cases b
    · change ZMod.prodEquivPi N hN ((ZMod.prodEquivPi N hN).symm (fun j => w (j, false))) j = _
      exact congrFun ((ZMod.prodEquivPi N hN).apply_symm_apply _) j
    · change ZMod.prodEquivPi N hN ((ZMod.prodEquivPi N hN).symm (fun j => w (j, true))) j = _
      exact congrFun ((ZMod.prodEquivPi N hN).apply_symm_apply _) j
  map_add' z v := by
    funext ⟨j, b⟩
    cases b
    · change ZMod.prodEquivPi N hN (z.1 + v.1) j = _
      exact congrFun (map_add (ZMod.prodEquivPi N hN) z.1 v.1) j
    · change ZMod.prodEquivPi N hN (z.2 + v.2) j = _
      exact congrFun (map_add (ZMod.prodEquivPi N hN) z.2 v.2) j

noncomputable def crtConfigurationTorus {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) :
    (ZMod (∏ j, N j) × ZMod (∏ j, N j)) →+ ((J × Bool) → UnitAddCircle) where
  toFun z t := ZMod.toAddCircle (crtConfigurationEquiv N hN z t)
  map_zero' := by ext t; simp
  map_add' z v := by ext t; simp

theorem crt_configuration_expect {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
    [∀ j, NeZero (N j)] [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
    (f : ((t : J × Bool) → ZMod (N t.1)) → ℝ) :
    (𝔼 z : ZMod (∏ j, N j) × ZMod (∏ j, N j), f (crtConfigurationEquiv N hN z)) = 𝔼 w, f w :=
  Fintype.expect_equiv (crtConfigurationEquiv N hN).toEquiv _ _ (fun _ => rfl)

noncomputable def crtConfigurationCharacter {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (frequency : J × Bool → ℤ) :
    AddChar (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ℂ where
  toFun z := ∏ t, CircleFourier.character (frequency t • crtConfigurationTorus N hN z t)
  map_zero_eq_one' := by simp
  map_add_eq_mul' z v := by
    simp only [map_add, Pi.add_apply, smul_add, CircleFourier.character_add, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
