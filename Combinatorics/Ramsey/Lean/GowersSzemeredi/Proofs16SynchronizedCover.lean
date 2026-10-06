import GowersSzemeredi.Proofs16RecoveredSliceCover

/-! # Synchronizing product covers without changing their candidates

Each refined base axis lies in a short parent parallel to the original
final axis. Retiling that final axis at the refined step converts every
rectangular cell into proper common-step boxes. The good set and the
multilinear candidate family are unchanged.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem appendCoordinate_init_last {N k : Nat} (z : Point N (k + 1)) :
    appendCoordinate (section16Init z) (section16Last z) = z := by
  rw [appendCoordinate_eq_snoc]
  exact Fin.snoc_init_self z

/-- Synchronize a finite rectangular cover using short parent axes. All
candidate functions are inherited from the old base cell, so there is no
increase in the number of graphs and no additional exceptional set. -/
theorem section16_synchronize_base_cover {N k M v : Nat} [NeZero N] {C : Type*}
    (T : Box N k) (I : ModAP N) (hI : I.IsProper)
    (R : Fin M → Box N k) (hRpart : IsBoxPartition R T) (hR : ∀ j, (R j).IsProper)
    (B : Fin M → ModAP N) (axis : Fin k) (u : Fin M → (ZMod N)ˣ)
    (hBstep : ∀ j, (B j).step = (↑(u j) : ZMod N))
    (hIstep : ∀ j, I.step = (B j).step)
    (hsub : ∀ j, ((R j).axis axis).carrier ⊆ (B j).carrier)
    (hshort : ∀ j, 2 * (B j).length ≤ N) (hL : ∀ j, (B j).length ≤ I.length)
    (hv : 1 ≤ v) (hfit : ∀ j, v ^ 2 ≤ (R j).width - 1)
    (D G : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (mu : Fin M → C → Point N (k + 1) → ZMod N)
    (hmu : ∀ j c, IsMultilinear (mu j c))
    (hcover : ∀ j z, section16Init z ∈ (R j).carrier → z ∈ D → z ∈ G →
      ∃ c, phi z = mu j c z) :
    ∃ (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → C → Point N (k + 1) → ZMod N),
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ D → z ∈ G → ∃ c, phi z = nu j c z := by
  classical
  choose L S J hSpart hSproper hSproduct hJlength using fun j =>
    box_product_tiling_of_contained_axis (R j) (B j) I axis (u j)
      (hR j) hI (hBstep j) (hIstep j) (hsub j) (hshort j) (hL j) hv (hfit j)
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, boxFlatten L S, fun j => mu (e.symm j).1,
    finsetPartition_flatten L (fun j => lastProductSet (R j).carrier I.carrier)
      (lastProductSet T.carrier I.carrier) (fun j a => (S j a).carrier)
      (lastProductSet_partition _ _ _ hRpart) hSpart,
    fun j => hSproper _ _, fun j c => hmu _ c, ?_⟩
  intro j z hz hD hG
  have hp := (hSproduct (e.symm j).1 (e.symm j).2).1
  change z ∈ (S (e.symm j).1 (e.symm j).2).carrier at hz
  rw [hp] at hz
  exact hcover _ z (Finset.mem_filter.mp hz).2.1 hD hG

end LeanProofs.GowersSzemeredi
