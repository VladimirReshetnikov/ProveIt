import GowersSzemeredi.Proofs16JointRowProperProgression

/-! Split affine row frequencies into one fixed spectrum and a varying
Freiman family. Half radii ensure the new Bohr domains lie inside the
original selected domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def affineRowConstants {N m : Nat} (J : Fin 4 → Finset (Fin m))
    (c : Fin 4 → Fin m → ZMod N) : Finset (ZMod N) :=
  Finset.univ.biUnion (fun j : Fin 4 => (J j).image (c j))
def varyingRowFrequencies {N m : Nat} (J : Fin 4 → Finset (Fin m))
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (j : Fin 4) (x : ZMod N) : Finset (ZMod N) :=
  (J j).image (fun i => psi j i x)
def affineRowBohrDomain {N m : Nat} [NeZero N] (J : Fin 4 → Finset (Fin m))
    (c : Fin 4 → Fin m → ZMod N) (psi : Fin 4 → Fin m → ZMod N → ZMod N)
    (sigma : Real) (j : Fin 4) (x : ZMod N) : Finset (ZMod N) :=
  bohr (affineRowConstants J c ∪ varyingRowFrequencies J psi j x) (sigma/2)

theorem affineRowConstants_card_le {N m K : Nat} (J : Fin 4 → Finset (Fin m))
    (c : Fin 4 → Fin m → ZMod N) (hJ : ∀ j, (J j).card ≤ K) :
    (affineRowConstants J c).card ≤ 4*K := by
  calc _ ≤ ∑ j : Fin 4, ((J j).image (c j)).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 4, K := Finset.sum_le_sum fun j _ => Finset.card_image_le.trans (hJ j)
    _ = _ := by simp

theorem affineRowFrequencies_card_le {N m K : Nat} (J : Fin 4 → Finset (Fin m))
    (c : Fin 4 → Fin m → ZMod N) (psi : Fin 4 → Fin m → ZMod N → ZMod N)
    (hJ : ∀ j, (J j).card ≤ K) (j : Fin 4) (x : ZMod N) :
    (affineRowConstants J c ∪ varyingRowFrequencies J psi j x).card ≤ 5*K := by
  have hc := affineRowConstants_card_le J c hJ
  have hv : (varyingRowFrequencies J psi j x).card ≤ K := Finset.card_image_le.trans (hJ j)
  exact (Finset.card_union_le _ _).trans (by omega)

theorem affine_row_bohr_subset {N m : Nat} [NeZero N]
    (J : Fin 4 → Finset (Fin m)) (c : Fin 4 → Fin m → ZMod N)
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (f : Fin m → ZMod N → ZMod N)
    (j : Fin 4) (t x : ZMod N) (sigma : Real)
    (hf : ∀ i ∈ J j, f i (t+x) = c j i+psi j i x) :
    affineRowBohrDomain J c psi sigma j x ⊆ bohr ((J j).image (fun i => f i (t+x))) sigma := by
  intro z hz
  have hz' : z ∈ bohr (affineRowConstants J c) (sigma/2) ∧
      z ∈ bohr (varyingRowFrequencies J psi j x) (sigma/2) := by
    simpa only [affineRowBohrDomain,bohr_union,Finset.mem_inter] using hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  have hc := (Finset.mem_filter.mp hz'.1).2 (c j i)
    (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩)
  have hp := (Finset.mem_filter.mp hz'.2).2 (psi j i x) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  have ha : (centeredAbs ((c j i+psi j i x)*z) : Real) ≤
      centeredAbs (c j i*z)+centeredAbs (psi j i x*z) := by
    rw [add_mul]
    exact_mod_cast centeredAbs_add_le (c j i*z) (psi j i x*z)
  rw [hf i hi]
  linarith

end LeanProofs.GowersSzemeredi
