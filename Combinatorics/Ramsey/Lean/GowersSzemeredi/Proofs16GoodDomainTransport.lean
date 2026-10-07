import GowersSzemeredi.Proofs16Translations
import GowersSzemeredi.Proofs16FaceInduction

/-! Transport the selected common-base domain and its all-ones graph back
into the original relation without cardinality or cover-parameter loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16GoodDomain_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) (x0 : Point N k) :
    (section16GoodDomain B H Y x0).card = section16GoodInducedPairCount B H Y x0 := by
  classical
  unfold section16GoodDomain section16GoodInducedPairCount countWhere
  apply Finset.card_bij (fun z _ => (section16Init z, section16Last z))
  · intro z hz
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hz
  · intro z hz w hw heq
    have hi := congrArg Prod.fst heq
    have hl := congrArg Prod.snd heq
    dsimp only at hi hl
    have hz' : appendCoordinate (section16Init z) (section16Last z) = z := by
      rw [appendCoordinate_eq_snoc]; exact Fin.snoc_init_self z
    have hw' : appendCoordinate (section16Init w) (section16Last w) = w := by
      rw [appendCoordinate_eq_snoc]; exact Fin.snoc_init_self w
    rw [← hz', ← hw', hi, hl]
  · intro z hz
    refine ⟨appendCoordinate z.1 z.2, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        section16Init_appendCoordinate, section16Last_appendCoordinate] using hz
    · simp

/-- Every translated vertex of a selected cube still lies in the original
partial-function domain. -/
theorem section16GoodDomain_vertex_mem {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) (x0 : Point N k)
    {z : Point N (k + 1)} (hz : z ∈ section16GoodDomain B H Y x0)
    (e : Fin k → Bool) :
    appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0)
      (section16Last z) ∈ B := by
  classical
  obtain ⟨_, C, _, hbase, hx⟩ := (Finset.mem_filter.mp hz).2
  have hC := (Finset.mem_filter.mp C.property).2
  have hh := hC.2 e
  change appendCoordinate (fun i => C.val.1.base i + if e i then C.val.1.side i else 0)
    C.val.2 ∈ B at hh
  simpa only [hbase, hC.1, hx] using hh

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
  classical
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
