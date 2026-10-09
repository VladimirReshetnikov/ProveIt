import GowersSzemeredi.Proofs16DenseAffineCluster
import GowersSzemeredi.Proofs16VarietyRegularStep

/-! Affine recentering of a tuple of varying Bohr frequencies. Add only its
constant offsets to the fixed frequency set and halve the phase radius. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def tupleRowGeometry {N : Nat} [NeZero N] {κ : Type*} [Fintype κ]
    (A : Finset (ZMod N × ZMod N)) (W F : Finset (ZMod N))
    (L : κ → ZMod N → ZMod N) (a : ZMod N) (eta : Real) : Prop :=
  ∀ x ∈ W, ∀ d ∈ bohr F eta,
    d ∈ bohr (Finset.univ.image fun j => L j x) eta → (d, a + x) ∈ A

/-- Constant and varying half-radius phase bounds control their affine sum. -/
theorem bohr_affine_tuple {N : Nat} [NeZero N] {κ : Type*} [Fintype κ]
    (L : κ → ZMod N → ZMod N) (c : κ → ZMod N) (t x d : ZMod N) {eta : Real}
    (haff : ∀ j, L j (t + x) = c j + L j x)
    (hc : d ∈ bohr (Finset.univ.image c) (eta / 2))
    (hx : d ∈ bohr (Finset.univ.image fun j => L j x) (eta / 2)) :
    d ∈ bohr (Finset.univ.image fun j => L j (t + x)) eta := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
  have hcj := (Finset.mem_filter.mp hc).2 _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hxj := (Finset.mem_filter.mp hx).2 _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  rw [haff j, add_mul]
  have h : (centeredAbs (c j * d + L j x * d) : Real) ≤
      centeredAbs (c j * d) + centeredAbs (L j x * d) := by
    exact_mod_cast centeredAbs_add_le (c j * d) (L j x * d)
  linarith

/-- Recenter actual row geometry, without changing the variable maps. -/
theorem tupleRowGeometry.affine_recenter {N : Nat} [NeZero N] {κ : Type*} [Fintype κ]
    {A : Finset (ZMod N × ZMod N)} {W V F : Finset (ZMod N)}
    {L : κ → ZMod N → ZMod N} {a t : ZMod N} {eta : Real} (heta : 0 ≤ eta)
    (hgeom : tupleRowGeometry A W F L a eta) (c : κ → ZMod N)
    (hVW : ∀ x ∈ V, t + x ∈ W)
    (haff : ∀ j, ∀ x ∈ V, L j (t + x) = c j + L j x) :
    tupleRowGeometry A V (F ∪ Finset.univ.image c) L (a + t) (eta / 2) := by
  intro x hx d hd hvar
  rw [bohr_union] at hd
  have hF := bohr_mono_radius F (show eta / 2 ≤ eta by linarith) (Finset.mem_inter.mp hd).1
  have hv := bohr_affine_tuple L c t x d (fun j => haff j x hx) (Finset.mem_inter.mp hd).2 hvar
  simpa only [add_assoc] using hgeom (t + x) (hVW x hx) d hF hv

/-- The extra fixed-frequency cost is at most the number of maps. -/
theorem affine_fixed_frequencies_card_le {N : Nat} {κ : Type*} [Fintype κ]
    (F : Finset (ZMod N)) (c : κ → ZMod N) :
    (F ∪ Finset.univ.image c).card ≤ F.card + Fintype.card κ :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (by simpa only [Finset.card_univ] using (Finset.card_image_le (s := Finset.univ) (f := c))) _)

end LeanProofs.GowersSzemeredi
