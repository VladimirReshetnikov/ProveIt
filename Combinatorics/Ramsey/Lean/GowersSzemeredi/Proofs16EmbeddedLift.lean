import GowersSzemeredi.Proofs16PrefixLift
import GowersSzemeredi.Proofs16PermutedCovers
import Mathlib.Logic.Equiv.Fintype

/-! Extension from any embedded set of coordinate directions. Permutation
invariance turns the iterated prefix extension into an ambient face cover. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def selectedCoordinates {N l d : Nat} (f : Fin l ↪ Fin d) (z : Point N d) : Point N l :=
  fun i => z (f i)

def selectedDomain {N l d : Nat} [NeZero N] (f : Fin l ↪ Fin d)
    (B : Finset (Point N l)) : Finset (Point N d) :=
  Finset.univ.filter (fun z => selectedCoordinates f z ∈ B)

@[simp] theorem mem_selectedDomain {N l d : Nat} [NeZero N]
    (f : Fin l ↪ Fin d) (B : Finset (Point N l)) (z : Point N d) :
    z ∈ selectedDomain f B ↔ selectedCoordinates f z ∈ B := by
  classical
  simp [selectedDomain]

/-- Extend a partial function across every unused coordinate, regardless of
the positions or order of its active coordinates. -/
theorem MultiplyLinearFunction.lift_embedding {N l d : Nat} [NeZero N] [Fact N.Prime]
    {gamma s : Real} {B : Finset (Point N l)} {phi : Point N l → ZMod N}
    (hML : MultiplyLinearFunction gamma s B phi)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 2 ≤ s)
    (hgraphs : ((3 ^ d : Nat) : Real) ≤ s) (f : Fin l ↪ Fin d) :
    MultiplyLinearFunction gamma s (selectedDomain f B)
      (fun z => phi (selectedCoordinates f z)) := by
  classical
  have hld : l ≤ d := by simpa using Fintype.card_le_of_injective f f.injective
  obtain ⟨sigma, hsigma⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin l => i.castLE hld) f (Fin.castLE_injective hld) f.injective
  let e : Point N d ≃ Point N d := LeanProofs.GowersSzemeredi.coordinateReindex sigma.symm
  have hinv : ∀ z, coordinatePrefix hld (e.symm z) = selectedCoordinates f z := by
    intro z
    funext i
    exact congrArg z (hsigma i)
  have hp := (hML.lift_prefix hg hg1 hs hgraphs hld).coordinateReindex sigma.symm
  change MultiplyLinearFunction gamma s ((prefixDomain hld B).image e)
    (fun z => phi (coordinatePrefix hld (e.symm z))) at hp
  have hdom : (prefixDomain hld B).image e = selectedDomain f B := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      rw [mem_selectedDomain, ← hinv, e.symm_apply_apply]
      exact (mem_prefixDomain hld B w).mp hw
    · intro hz
      refine Finset.mem_image.mpr ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      rw [mem_prefixDomain, hinv]
      exact (mem_selectedDomain f B z).mp hz
  simpa only [hdom, hinv] using hp

end LeanProofs.GowersSzemeredi
