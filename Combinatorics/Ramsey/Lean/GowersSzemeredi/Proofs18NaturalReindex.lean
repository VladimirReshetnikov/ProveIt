import GowersSzemeredi.Proofs18NaturalIntervalIncrement

/-! Reindexing a natural progression preserves its relative set cardinality
and transports every positive-step progression back to the original set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def NatAP.index (Q : NatAP) (i : Fin Q.length) : Nat := Q.start + (i : Nat) * Q.step

theorem NatAP.index_injective (Q : NatAP) (hQ : Q.IsProper) : Function.Injective Q.index := by
  intro i j hij
  apply Fin.ext
  exact Nat.mul_right_cancel hQ.1 (Nat.add_left_cancel hij)

/-- The original set on the finite index interval of the progression. -/
def NatAP.pullback (Q : NatAP) (A : Finset Nat) : Finset (Fin Q.length) :=
  Finset.univ.filter fun i => Q.index i ∈ A

@[simp] theorem NatAP.mem_pullback (Q : NatAP) (A : Finset Nat) (i : Fin Q.length) :
    i ∈ Q.pullback A ↔ Q.index i ∈ A := by
  classical
  simp [NatAP.pullback]

theorem NatAP.image_pullback (Q : NatAP) (A : Finset Nat) :
    (Q.pullback A).image Q.index = A ∩ Q.carrier := by
  classical
  ext x
  simp only [Finset.mem_image, NatAP.mem_pullback, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  · rintro ⟨hx, hp⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i, hx, rfl⟩

theorem NatAP.card_pullback (Q : NatAP) (hQ : Q.IsProper) (A : Finset Nat) :
    (Q.pullback A).card = (A ∩ Q.carrier).card := by
  rw [← Q.image_pullback A, Finset.card_image_of_injective _ (Q.index_injective hQ)]

/-- Reindexing cannot introduce a progression that was absent originally. -/
theorem NatAP.hasNatAP_of_pullback {k : Nat} (Q : NatAP) (hQ : Q.IsProper)
    (A : Finset Nat) (hAP : HasNatAP ((Q.pullback A).image Fin.val) k) : HasNatAP A k := by
  classical
  obtain ⟨a, d, hd, hAP⟩ := hAP
  refine ⟨Q.start + a * Q.step, d * Q.step, Nat.mul_pos hd hQ.1, ?_⟩
  intro i hi
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (hAP i hi)
  have hm := (Q.mem_pullback A j).mp hj
  dsimp [NatAP.index] at hm
  rw [hji] at hm
  convert hm using 1
  ring

end LeanProofs.GowersSzemeredi
