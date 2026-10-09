import GowersSzemeredi.Proofs16CenteredProgressionGeometry

/-! Uniform bridge abundance for pairs of points in the quarter shrinking.
Every point of the half shrinking is an admissible bridge, giving the
explicit rank loss required by the bounded-image purification argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def progressionBridgeSet {N : Nat} (C : Finset (ZMod N)) (a : ZMod N) : Finset (ZMod N) :=
  C.filter fun u => u+a ∈ C

/-- Quarter-box differences translate the entire half box into the parent. -/
theorem centered_progression_bridge_mem {N : Nat} (Q : CenteredProgression N)
    {x y u : ZMod N}
    (hx : x ∈ (centeredProgressionShrink Q 4).carrier)
    (hy : y ∈ (centeredProgressionShrink Q 4).carrier)
    (hu : u ∈ (centeredProgressionShrink Q 2).carrier) :
    u ∈ progressionBridgeSet Q.carrier (x-y) := by
  have huQ := centered_progression_shrink_subset Q 2 hu
  obtain ⟨z, hz, ex⟩ := (centered_progression_mem_iff _ x).mp hx
  obtain ⟨w, hw, ey⟩ := (centered_progression_mem_iff _ y).mp hy
  obtain ⟨v, hv, eu⟩ := (centered_progression_mem_iff _ u).mp hu
  dsimp only [centeredProgressionShrink, centeredProgressionResize] at z w v hz hw hv ex ey eu
  refine Finset.mem_filter.mpr ⟨huQ, (centered_progression_mem_iff Q _).mpr ?_⟩
  refine ⟨fun i => v i+(z i-w i), ?_, ?_⟩
  · intro i
    have hb : Q.radius i/2+Q.radius i/4+Q.radius i/4 ≤ Q.radius i := by omega
    calc |v i+(z i-w i)| ≤ |v i|+|z i-w i| := abs_add_le _ _
      _ ≤ |v i|+(|z i|+|w i|) := add_le_add (le_refl (|v i|)) (abs_sub (z i) (w i))
      _ ≤ (Q.radius i/2 : Nat)+(Q.radius i/4 : Nat)+(Q.radius i/4 : Nat) := by
        have h := add_le_add (hv i) (add_le_add (hz i) (hw i))
        simpa only [add_assoc] using h
      _ ≤ (Q.radius i : Int) := by exact_mod_cast hb
  · rw [eu, ex, ey]
    change (∑ i : Fin Q.rank, (v i : ZMod N)*Q.step i) +
      ((∑ i : Fin Q.rank, (z i : ZMod N)*Q.step i) -
        (∑ i : Fin Q.rank, (w i : ZMod N)*Q.step i)) =
      ∑ i : Fin Q.rank, ((v i+(z i-w i) : Int) : ZMod N)*Q.step i
    simp only [Int.cast_add, Int.cast_sub, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Every bridge family has at least the half-box mass, independently of
which pair of quarter-box points gives the difference. -/
theorem centered_progression_bridge_card {N : Nat} (Q : CenteredProgression N)
    (hQ : Q.Proper) {x y : ZMod N}
    (hx : x ∈ (centeredProgressionShrink Q 4).carrier)
    (hy : y ∈ (centeredProgressionShrink Q 4).carrier) :
    Q.carrier.card ≤ 4^Q.rank*(progressionBridgeSet Q.carrier (x-y)).card := by
  have hsub : (centeredProgressionShrink Q 2).carrier ⊆ progressionBridgeSet Q.carrier (x-y) :=
    fun _ hu => centered_progression_bridge_mem Q hx hy hu
  exact (centered_progression_shrink_card Q hQ (by decide : 0 < (2 : Nat))).trans
    (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

end LeanProofs.GowersSzemeredi
