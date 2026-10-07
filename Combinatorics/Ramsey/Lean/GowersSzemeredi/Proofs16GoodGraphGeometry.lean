import GowersSzemeredi.Proofs16GoodDomainTransport

/-! The selected common-base graph has an exact mass-preserving realization
inside the original relation, independently of its eventual cover bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16TranslatedGoodGraph {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) : Finset (Point N (k + 1) × ZMod N) :=
  (partialGraph (section16GoodDomain B H Y x0) (section16PhiOne phi x0)).image
    (fun z => (z.1 + appendCoordinate x0 0, z.2))

theorem section16TranslatedGoodGraph_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) :
    (section16TranslatedGoodGraph B phi H Y x0).card = section16GoodInducedPairCount B H Y x0 := by
  have hinj : Function.Injective (fun z : Point N (k + 1) × ZMod N => (z.1 + appendCoordinate x0 0, z.2)) := by
    intro a b hab
    exact Prod.ext (add_right_cancel (Prod.mk.inj hab).1) (Prod.mk.inj hab).2
  rw [section16TranslatedGoodGraph, Finset.card_image_of_injective _ hinj, partialGraph_card,
    section16GoodDomain_card]

theorem section16TranslatedGoodGraph_subset {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N (k + 1) × ZMod N))
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) (hgraph : GraphContained B phi Gamma) :
    section16TranslatedGoodGraph B phi H Y x0 ⊆ Gamma := by
  classical
  intro z hz
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hab
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hv := section16GoodDomain_vertex_mem B H Y x0 hx (fun _ => true)
  have hp : appendCoordinate (fun i => x0 i + section16Init x i) (section16Last x) =
      x + appendCoordinate x0 0 := by
    rw [appendCoordinate_eq_snoc]
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [appendCoordinate_eq_snoc, section16Last]
    · simp [appendCoordinate_eq_snoc, section16Init, add_comm]
  simp only [ite_true] at hv
  rw [hp] at hv
  simpa only [section16PhiOne_eq_translate] using hgraph _ hv

end LeanProofs.GowersSzemeredi
