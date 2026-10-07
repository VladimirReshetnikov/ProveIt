import GowersSzemeredi.Proofs16SlabArrangements
import GowersSzemeredi.Proofs16VertexIdentity

/-! The full cube selection on a slab has every admissible common-base pair.
These are geometric identities, without a spectral cover or mass hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_slab_cube_mem {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (h : Point N k) (C : AxisCube N k × ZMod N) :
    C ∈ section16CubeDomain (lastProductSet Finset.univ A) h ↔
      C.1.side = h ∧ C.2 ∈ A := by
  simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ, true_and,
    lastProductSet, section16Last_appendCoordinate]
  exact and_congr_right fun _ =>
    ⟨fun hh => hh (fun _ => false), fun hh _ => hh⟩

theorem section16_slab_cube_card {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (h : Point N k) :
    (section16CubeDomain (lastProductSet Finset.univ A) h).card = N ^ k * A.card := by
  classical
  have heq : section16CubeDomain (lastProductSet Finset.univ A) h =
      ((Finset.univ : Finset (Point N k)) ×ˢ A).image (fun z => ((z.1, h), z.2)) := by
    ext C
    rw [section16_slab_cube_mem]
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hh, hx⟩
      refine ⟨(C.1.base, C.2), hx, ?_⟩
      exact Prod.ext (Prod.ext rfl hh.symm) rfl
    · rintro ⟨z, hz, rfl⟩
      exact ⟨rfl, hz⟩
  rw [heq, Finset.card_image_of_injective]
  · simp [Finset.card_product, Point, ZMod.card]
  · intro z w he
    exact Prod.ext (congrArg (fun C => C.1.1) he) (congrArg (fun C : AxisCube N k × ZMod N => C.2) he)

theorem section16_slab_induced_value {N k : Nat} [NeZero N]
    (hk : 1 ≤ k) (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (h : Point N k) (C : Section16CubeElement (lastProductSet Finset.univ A) h) :
    section16InducedCubeMap (lastProductSet Finset.univ A) h
      (fun z => f (section16Last z)) C = 0 := by
  simp only [section16InducedCubeMap, section16Last_appendCoordinate,
    ← Finset.sum_mul, section16_cube_sign_sum hk, zero_mul]

theorem section16_slab_value_at_base {N k : Nat} [NeZero N]
    (hk : 1 ≤ k) (f : ZMod N → ZMod N) (x0 h : Point N k) (x : ZMod N) :
    section16CubeValueAtBase (fun z => f (section16Last z)) x0 h x = 0 := by
  simp only [section16CubeValueAtBase, section16Last_appendCoordinate,
    ← Finset.sum_mul, section16_cube_sign_sum hk, zero_mul]

theorem section16_slab_full_good_pair {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x0 : Point N k) (z : Point N k × ZMod N) :
    Section16GoodInducedPair (lastProductSet Finset.univ A) Finset.univ
      (fun _ => Finset.univ) x0 z ↔ z.2 ∈ A := by
  classical
  constructor
  · rintro ⟨_, C, _, _, hx⟩
    simpa only [hx] using (section16_slab_cube_mem A z.1 C.val).mp C.property |>.2
  · intro hx
    refine ⟨Finset.mem_univ _, ?_⟩
    let C : Section16CubeElement (lastProductSet Finset.univ A) z.1 :=
      ⟨((x0, z.1), z.2), (section16_slab_cube_mem A z.1 _).mpr ⟨rfl, hx⟩⟩
    exact ⟨C, Finset.mem_univ _, rfl, rfl⟩

theorem section16_slab_full_good_domain {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x0 : Point N k) :
    section16GoodDomain (lastProductSet Finset.univ A) Finset.univ
      (fun _ => Finset.univ) x0 = lastProductSet Finset.univ A := by
  classical
  ext z
  simp only [section16GoodDomain, Finset.mem_filter, Finset.mem_univ, true_and]
  change Section16GoodInducedPair (lastProductSet Finset.univ A) Finset.univ
    (fun _ => Finset.univ) x0 (section16Init z, section16Last z) ↔ z ∈ lastProductSet Finset.univ A
  rw [section16_slab_full_good_pair]
  simp [lastProductSet]

theorem section16_slab_full_good_count {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x0 : Point N k) :
    section16GoodInducedPairCount (lastProductSet Finset.univ A) Finset.univ
      (fun _ => Finset.univ) x0 = N ^ k * A.card := by
  rw [← section16GoodDomain_card, section16_slab_full_good_domain, lastProductSet_card]
  simp [Point, ZMod.card]

theorem section16_slab_full_induced_selection {N k : Nat} [NeZero N]
    (hk : 1 ≤ k) (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (K : Point N k → Finset (ZMod N)) (zeta : Real) :
    Section16InducedSelection (lastProductSet Finset.univ A)
      (fun z => f (section16Last z)) Finset.univ (fun _ => Finset.univ)
      K zeta (fun _ _ => 0) := by
  refine ⟨?_, ?_⟩
  · intro h hh C hC
    exact (section16_slab_induced_value hk A f h C).symm
  · intro h hh m hm d hd I hstep hlen
    exact ⟨0, 0, by simp⟩

theorem section16_slab_full_common_base_identity {N k : Nat} [NeZero N]
    (hk : 1 ≤ k) (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (x0 : Point N k) :
    Section16PhiOneIdentity
      (section16GoodDomain (lastProductSet Finset.univ A) Finset.univ
        (fun _ => Finset.univ) x0)
      (fun z => f (section16Last z)) x0 (fun _ _ => 0) := by
  apply section16_phi_one_identity_of_common_base
  intro z hz
  exact (section16_slab_value_at_base hk f x0 z.1 z.2).symm

end LeanProofs.GowersSzemeredi
