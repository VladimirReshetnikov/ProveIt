import GowersSzemeredi.Proofs16SynchronizedCover

/-! Declarations of `Proofs16SynchronizedCover` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

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
  obtain ⟨L, S, nu, hpart, hS, hnu, hcov⟩ := section16_synchronize_base_cover_family (ι := Unit)
    T I hI R hRpart hR B axis u hBstep hIstep hsub hshort hL hv hfit (fun _ => D) (fun _ => G)
    (fun _ => phi) mu hmu (fun _ => hcover)
  exact ⟨L, S, nu, hpart, hS, hnu, hcov ()⟩

end LeanProofs.GowersSzemeredi
