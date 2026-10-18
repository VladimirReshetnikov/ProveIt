import GowersSzemeredi.Proofs16GoodDomainTransport
import GowersSzemeredi.Proofs16TranslationsSide

/-! Declarations of `Proofs16GoodDomainTransport` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The all-ones vertex map is exactly a translation in the first k
coordinates; its final coordinate is unchanged. -/
theorem section16PhiOne_eq_translate {N k : Nat}
    (phi : Point N (k + 1) → ZMod N) (x0 : Point N k) (z : Point N (k + 1)) :
    section16PhiOne phi x0 z = phi (z + appendCoordinate x0 0) := by
  unfold section16PhiOne
  apply congrArg phi
  rw [appendCoordinate_eq_snoc, appendCoordinate_eq_snoc]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [section16Last]
  · simp [section16Init, add_comm]

/-- A multiply-linear all-ones graph on the good domain yields a subrelation
of the original input with the same mass and the same cover parameter. -/
theorem section16_good_domain_subrelation {N k : Nat} [NeZero N] [Fact N.Prime]
    (Gamma : Finset (Point N (k + 1) × ZMod N))
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) {gamma r delta : Real}
    (hgraph : GraphContained B phi Gamma)
    (hmass : delta * (N : Real) ^ (k + 1) ≤ section16GoodInducedPairCount B H Y x0)
    (hML : MultiplyLinearFunction gamma r (section16GoodDomain B H Y x0)
      (section16PhiOne phi x0)) :
    ∃ D ⊆ Gamma, delta * (N : Real) ^ (k + 1) ≤ D.card ∧ MultiplyLinear gamma r D := by
  let t := appendCoordinate x0 (0 : ZMod N)
  let G := partialGraph (section16GoodDomain B H Y x0) (section16PhiOne phi x0)
  let D := G.image (fun z => (z.1 + t, z.2))
  have hinj : Function.Injective (fun z : Point N (k + 1) × ZMod N => (z.1 + t, z.2)) := by
    intro a b hab
    exact Prod.ext (add_right_cancel (Prod.mk.inj hab).1) (Prod.mk.inj hab).2
  refine ⟨D, ?_, ?_, MultiplyLinear.translate hML t⟩
  · intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hab
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    have hv := section16GoodDomain_vertex_mem B H Y x0 hx (fun _ => true)
    have hp : appendCoordinate (fun i => x0 i + section16Init x i) (section16Last x) = x + t := by
      rw [appendCoordinate_eq_snoc]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [t, appendCoordinate_eq_snoc, section16Last]
      · simp [t, appendCoordinate_eq_snoc, section16Init, add_comm]
    simp only [ite_true] at hv
    rw [hp] at hv
    have hh := hgraph (x + t) hv
    simpa only [section16PhiOne_eq_translate, t] using hh
  · rw [show D.card = (section16GoodDomain B H Y x0).card by
      dsimp only [D, G]
      rw [Finset.card_image_of_injective _ hinj, partialGraph_card]]
    rw [section16GoodDomain_card]
    exact hmass

end LeanProofs.GowersSzemeredi
