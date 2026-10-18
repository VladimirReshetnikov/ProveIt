import GowersSzemeredi.Proofs16FibreGeometry
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Bertrand

/-! # Synchronizing product covers without changing their candidates

Each refined base axis lies in a short parent parallel to the original
final axis. Retiling that final axis at the refined step converts every
rectangular cell into proper common-step boxes. The good set and the
multilinear candidate family are unchanged.

`section16_synchronize_base_cover` is in `Proofs16SynchronizedCoverSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem appendCoordinate_init_last {N k : Nat} (z : Point N (k + 1)) :
    appendCoordinate (section16Init z) (section16Last z) = z := by
  rw [appendCoordinate_eq_snoc]
  exact Fin.snoc_init_self z

/-- **Synchronized retiling for a family.** The tiling depends only on the
base cells, so it serves every member. -/
theorem section16_synchronize_base_cover_family {N k M v : Nat} [NeZero N] {C ι : Type*}
    (T : Box N k) (I : ModAP N) (hI : I.IsProper)
    (R : Fin M → Box N k) (hRpart : IsBoxPartition R T) (hR : ∀ j, (R j).IsProper)
    (B : Fin M → ModAP N) (axis : Fin k) (u : Fin M → (ZMod N)ˣ)
    (hBstep : ∀ j, (B j).step = (↑(u j) : ZMod N))
    (hIstep : ∀ j, I.step = (B j).step)
    (hsub : ∀ j, ((R j).axis axis).carrier ⊆ (B j).carrier)
    (hshort : ∀ j, 2 * (B j).length ≤ N) (hL : ∀ j, (B j).length ≤ I.length)
    (hv : 1 ≤ v) (hfit : ∀ j, v ^ 2 ≤ (R j).width - 1)
    (D G : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
    (mu : Fin M → C → Point N (k + 1) → ZMod N)
    (hmu : ∀ j c, IsMultilinear (mu j c))
    (hcover : ∀ a j z, section16Init z ∈ (R j).carrier → z ∈ D a → z ∈ G a →
      ∃ c, phi a z = mu j c z) :
    ∃ (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → C → Point N (k + 1) → ZMod N),
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G a → ∃ c, phi a z = nu j c z := by
  choose L S J hSpart hSproper hSproduct _ using fun j =>
    box_product_tiling_of_contained_axis (R j) (B j) I axis (u j)
      (hR j) hI (hBstep j) (hIstep j) (hsub j) (hshort j) (hL j) hv (hfit j)
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, boxFlatten L S, fun j => mu (e.symm j).1,
    finsetPartition_flatten L (fun j => lastProductSet (R j).carrier I.carrier)
      (lastProductSet T.carrier I.carrier) (fun j a => (S j a).carrier)
      (lastProductSet_partition _ _ _ hRpart) hSpart,
    fun j => hSproper _ _, fun j c => hmu _ c, ?_⟩
  intro a j z hz hD hG
  have hp := (hSproduct (e.symm j).1 (e.symm j).2).1
  change z ∈ (S (e.symm j).1 (e.symm j).2).carrier at hz
  rw [hp] at hz
  exact hcover a _ z (Finset.mem_filter.mp hz).2.1 hD hG

end LeanProofs.GowersSzemeredi
