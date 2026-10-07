import GowersSzemeredi.Proofs16CoordinateMaskFaces
import GowersSzemeredi.Proofs16GoodDomainTransport

/-! Every non-top translated cube vertex has an ambient multiply-linear
cover on the actual selected good domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The final coordinate is always active; the other active coordinates
are exactly the true entries of the cube vertex. -/
def section16VertexDirections {k : Nat} (e : Fin k → Bool) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun j => Fin.lastCases true e j = true)

@[simp] theorem section16VertexDirections_last {k : Nat} (e : Fin k → Bool) :
    Fin.last k ∈ section16VertexDirections e := by
  simp [section16VertexDirections]

@[simp] theorem section16VertexDirections_castSucc {k : Nat} (e : Fin k → Bool) (i : Fin k) :
    i.castSucc ∈ section16VertexDirections e ↔ e i = true := by
  simp [section16VertexDirections]

theorem section16VertexDirections_card_lt {k : Nat} {e : Fin k → Bool}
    (he : e ≠ fun _ => true) : (section16VertexDirections e).card < k + 1 := by
  have hne : section16VertexDirections e ≠ Finset.univ := by
    intro hh
    apply he
    funext i
    exact (section16VertexDirections_castSucc e i).mp (by rw [hh]; exact Finset.mem_univ _)
  have hsub : section16VertexDirections e ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩
  simpa using Finset.card_lt_card hsub

/-- The mask representation agrees with the original translated vertex,
including the unchanged final coordinate. -/
theorem section16_vertex_coordinate_mask {N k : Nat}
    (x0 : Point N k) (e : Fin k → Bool) (z : Point N (k + 1)) :
    (fun j => if j ∈ section16VertexDirections e then (z + appendCoordinate x0 0) j
      else appendCoordinate x0 0 j) =
      appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0)
        (section16Last z) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [appendCoordinate_eq_snoc, section16Last]
  · simp only [section16VertexDirections_castSucc, Pi.add_apply, appendCoordinate_eq_snoc,
      Fin.snoc_castSucc, section16Init]
    cases e i <;> simp [add_comm]

/-- The proper-face hypothesis suffices for each non-top vertex, without
any line-cover or common-base spectral hypothesis. -/
theorem ProperCrossSectionsMultiplyLinear.good_domain_vertex_cover
    {N k : Nat} [NeZero N] [Fact N.Prime] {gamma r : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (hfaces : ProperCrossSectionsMultiplyLinear gamma r B phi)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 2 ≤ r)
    (hgraphs : ((3 ^ (k + 1) : Nat) : Real) ≤ r)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) (e : Fin k → Bool) (he : e ≠ fun _ => true) :
    MultiplyLinearFunction gamma r (section16GoodDomain B H Y x0)
      (section16TranslatedVertex phi x0 e) := by
  have hp := hfaces.coordinate_mask_cover hg hg1 hr hgraphs (section16VertexDirections e)
    (section16VertexDirections_card_lt he) (appendCoordinate x0 0) (appendCoordinate x0 0)
    (section16GoodDomain B H Y x0) (by
      intro z hz
      rw [section16_vertex_coordinate_mask]
      exact section16GoodDomain_vertex_mem B H Y x0 hz e)
  simp only [section16_vertex_coordinate_mask] at hp
  exact hp

/-- The actual structured-pair parameter automatically pays for every
non-top vertex cover. -/
theorem Section16StructuredPair.good_domain_vertex_cover
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (h : Section16StructuredPair theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (H : Finset (Point N k)) (Y : (a : Point N k) → Finset (Section16CubeElement B a))
    (x0 : Point N k) (e : Fin k → Bool) (he : e ≠ fun _ => true) :
    MultiplyLinearFunction gamma
      (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
      (section16GoodDomain B H Y x0) (section16TranslatedVertex phi x0 e) := by
  obtain ⟨hr, hreserve⟩ := section16_face_parameter_lift_reserve k ht ht1 hg hg1
  exact h.1.good_domain_vertex_cover hg hg1 hr (hreserve (k + 1) le_rfl) H Y x0 e he

end LeanProofs.GowersSzemeredi
