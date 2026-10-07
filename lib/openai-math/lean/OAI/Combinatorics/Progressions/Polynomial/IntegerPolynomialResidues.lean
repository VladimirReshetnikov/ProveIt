import Mathlib.Algebra.MvPolynomial.Eval
import OAI.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
import OAI.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod

namespace OAI

section

namespace Erdos3

theorem integerPolynomial_eval_residue {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) (x : X → ℤ) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod m)) (integerResidueMap X m x) p := by
  have heq : integerResidueMap X m x = (fun i => (x i : ZMod m)) := rfl
  rw [heq]
  simpa only [MvPolynomial.eval₂_id, RingHom.comp_id, Int.coe_castRingHom] using
    MvPolynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom (ZMod m)) x

theorem integerPolynomial_eval_congr {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) {x y : X → ℤ} (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) = ((MvPolynomial.eval y p : ℤ) : ZMod m) := by
  rw [integerPolynomial_eval_residue, integerPolynomial_eval_residue, hxy]

theorem integerPolynomial_eval_mod {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) {x y : X → ℤ} (hxy : ∀ i, x i % (m : ℤ) = y i % (m : ℤ)) :
    MvPolynomial.eval x p % (m : ℤ) = MvPolynomial.eval y p % (m : ℤ) :=
  (ZMod.intCast_eq_intCast_iff' _ _ m).mp
    (integerPolynomial_eval_congr p m ((integerResidueMap_eq_iff m x y).mpr hxy))

theorem integerBooleanCoefficient_residue {α : Type*} [DecidableEq α]
    (m : ℕ) (f : Finset α → ℤ) (s : Finset α) :
    ((booleanCoefficient f s : ℤ) : ZMod m) =
      booleanCoefficient (fun t => (f t : ZMod m)) s :=
  booleanCoefficient_map (Int.castRingHom (ZMod m)) f s

theorem integerBooleanCoefficient_congr {α : Type*} [DecidableEq α]
    (m : ℕ) (f g : Finset α → ℤ) (s : Finset α)
    (hfg : ∀ t ∈ s.powerset, (f t : ZMod m) = (g t : ZMod m)) :
    ((booleanCoefficient f s : ℤ) : ZMod m) = ((booleanCoefficient g s : ℤ) : ZMod m) := by
  rw [integerBooleanCoefficient_residue, integerBooleanCoefficient_residue]
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro t ht
  dsimp only
  rw [hfg t ht]

end Erdos3

end

end OAI
