import GowersSzemeredi.Proofs16FourWalkDifferences
import GowersSzemeredi.Proofs16WeightedCollision

/-! Count four-walks between prescribed endpoint sets and collisions
of their edge-difference sequences. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

abbrev FourWalkData (N : Nat) := (ZMod N × ZMod N) × (ZMod N × ZMod N × ZMod N)

def fourWalkDataSteps {N : Nat} (w : FourWalkData N) : Fin 4 → ZMod N :=
  fourWalkSteps w.1.1 w.1.2 w.2

def fourWalkFamily {N : Nat} [NeZero N] (E : Finset (ZMod N × ZMod N))
    (U V : Finset (ZMod N)) : Finset (FourWalkData N) :=
  ((U ×ˢ V) ×ˢ Finset.univ).filter (fun w => w.2 ∈ graphFourWalks (fun a b => (a,b) ∈ E) w.1.1 w.1.2)

def fourWalkCollisions {N : Nat} [NeZero N] (W : Finset (FourWalkData N)) :
    Finset (FourWalkData N × FourWalkData N) :=
  (W ×ˢ W).filter (fun p => fourWalkDataSteps p.1 = fourWalkDataSteps p.2)

theorem fourWalkFamily_card {N : Nat} [NeZero N] (E : Finset (ZMod N × ZMod N))
    (U V : Finset (ZMod N)) :
    (fourWalkFamily E U V).card =
      ∑ u ∈ U, ∑ v ∈ V, (graphFourWalks (fun a b => (a,b) ∈ E) u v).card := by
  simp only [fourWalkFamily, Finset.card_filter, Finset.sum_product]
  simp

/-- Uniform endpoint walk counts give the total mass without selecting
a particular pair of endpoints. -/
theorem fourWalkFamily_mass {N : Nat} [NeZero N] (E : Finset (ZMod N × ZMod N))
    (U V : Finset (ZMod N)) {eta : Real}
    (hwalk : ∀ u ∈ U, ∀ v ∈ V, eta*(N : Real)^3 ≤
      ((graphFourWalks (fun a b => (a,b) ∈ E) u v).card : Real)) :
    (U.card : Real)*V.card*eta*(N : Real)^3 ≤ (fourWalkFamily E U V).card := by
  have heq : ((fourWalkFamily E U V).card : Real) =
      ∑ u ∈ U, ∑ v ∈ V, ((graphFourWalks (fun a b => (a,b) ∈ E) u v).card : Real) := by
    exact_mod_cast fourWalkFamily_card E U V
  rw [heq]
  calc _ = ∑ _u ∈ U, ∑ _v ∈ V, eta*(N : Real)^3 := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => hwalk u hu v hv

/-- Cauchy--Schwarz costs only the `N^4` possible edge-difference sequences. -/
theorem fourWalkCollisions_mass_bound {N : Nat} [NeZero N] (W : Finset (FourWalkData N)) :
    (W.card : Real)^2 ≤ (N : Real)^4 * (fourWalkCollisions W).card := by
  have heq : weightedCollisionEnergy W fourWalkDataSteps (fun _ => 1) =
      ((fourWalkCollisions W).card : Real) := by
    simp only [weightedCollisionEnergy, fourWalkCollisions, Finset.card_filter,
      Finset.sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, one_mul]
  have h := weightedCollisionEnergy_mass_bound W (Finset.univ : Finset (Fin 4 → ZMod N))
    fourWalkDataSteps (fun _ => 1) (fun _ _ => Finset.mem_univ _)
  simpa [heq] using h

end LeanProofs.GowersSzemeredi
