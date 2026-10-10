import GowersSzemeredi.Proofs16ShrunkBridgeCandidates

/-! Signed-coordinate bounds for translated finite words in a shrinking. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem centered_progression_translated_sum_mem {N m : Nat} (Q : CenteredProgression N)
    (r s t : Fin Q.rank → Nat) (hbudget : ∀ i, s i+m*r i ≤ t i)
    (u : ZMod N) (xs : Fin m → ZMod N)
    (hu : u ∈ (centeredProgressionResize Q s).carrier)
    (hxs : ∀ j, xs j ∈ (centeredProgressionResize Q r).carrier) :
    u+∑ j, xs j ∈ (centeredProgressionResize Q t).carrier := by
  obtain ⟨w,hw,eu⟩ := (centered_progression_mem_iff _ u).mp hu
  choose z hz he using fun j => (centered_progression_mem_iff _ _).mp (hxs j)
  dsimp only [centeredProgressionResize] at w hw eu z hz he ⊢
  refine (centered_progression_mem_iff _ _).mpr ⟨fun i => w i+∑ j, z j i, ?_, ?_⟩
  · intro i
    calc |w i+∑ j, z j i| ≤ |w i|+|∑ j, z j i| := abs_add_le _ _
      _ ≤ |w i|+∑ j, |z j i| := add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (s i : Int)+∑ _j : Fin m, (r i : Int) :=
        add_le_add (hw i) (Finset.sum_le_sum fun j _ => hz j i)
      _ = (s i : Int)+(m : Int)*r i := by simp
      _ ≤ (t i : Int) := by exact_mod_cast hbudget i
  · rw [eu]
    simp_rw [he]
    change (∑ i : Fin Q.rank, (w i : ZMod N)*Q.step i)+
      (∑ j : Fin m, ∑ i : Fin Q.rank, (z j i : ZMod N)*Q.step i) =
      ∑ i : Fin Q.rank, ((w i+∑ j : Fin m, z j i : Int) : ZMod N)*Q.step i
    rw [Finset.sum_comm]
    simp only [Int.cast_add, Int.cast_sum, add_mul, Finset.sum_add_distrib, Finset.sum_mul]

/-- Six tiny word entries leave room for a common anchor in `Q/32`. -/
theorem centered_progression_six_word_shift_mem {N : Nat} (Q : CenteredProgression N)
    (u : ZMod N) (xs : Fin 6 → ZMod N)
    (hu : u ∈ (centeredProgressionShrink Q 32).carrier)
    (hxs : ∀ j, xs j ∈ (centeredProgressionShrink Q 256).carrier) :
    u+∑ j, xs j ∈ (centeredProgressionShrink Q 16).carrier := by
  exact centered_progression_translated_sum_mem Q (fun i => Q.radius i/256)
    (fun i => Q.radius i/32) (fun i => Q.radius i/16) (fun i => by omega) u xs hu hxs

end LeanProofs.GowersSzemeredi
