import GowersSzemeredi.Proofs16FreimanFamilyRestriction
import GowersSzemeredi.Proofs16FinalSections

/-! Transport fixed Freiman families into the common-base good domain.
The original section families survive both translation and deletion; their
count is independent of the inner loss in the later affine lift. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every final-coordinate section has a fixed-size Freiman graph cover. -/
def Section16FinalFreimanFamilies {N : Nat} [NeZero N] (q : Nat)
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N) : Prop :=
  ∀ t, Section16FreimanFamilyCover q (section16FinalCoordinateSection B t)
    (section16FinalCoordinateRestriction phi t)

theorem Section16FinalFreimanFamilies.mono {N q : Nat} [NeZero N]
    {B C : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q B phi) (hCB : C ⊆ B) :
    Section16FinalFreimanFamilies q C phi := by
  intro t
  apply (h t).mono
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCB (Finset.mem_filter.mp hx).2⟩

/-- The same family count works for the translated sections of any selected
common-base good domain. -/
theorem Section16FinalFreimanFamilies.good_domain {N q : Nat} [NeZero N]
    {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q B phi)
    (H : Finset (Point N 1)) (Y : (a : Point N 1) → Finset (Section16CubeElement B a))
    (x0 : Point N 1) :
    Section16FinalFreimanFamilies q (section16GoodDomain B H Y x0)
      (section16PhiOne phi x0) := by
  classical
  intro t
  have hp := (h t).translate (-x0)
  have heq : (fun y => section16FinalCoordinateRestriction phi t (y - -x0)) =
      section16FinalCoordinateRestriction (section16PhiOne phi x0) t := by
    funext y
    simp [section16FinalCoordinateRestriction, section16PhiOne,
      section16Init_appendCoordinate, section16Last_appendCoordinate, sub_neg_eq_add, add_comm]
    rfl
  rw [heq] at hp
  apply hp.mono
  intro y hy
  have hv := section16GoodDomain_vertex_mem B H Y x0 (Finset.mem_filter.mp hy).2 (fun _ => true)
  have hb : appendCoordinate (y + x0) t ∈ B := by
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate,
      ite_true, ← Pi.add_def, add_comm] using hv
  apply Finset.mem_image.mpr
  refine ⟨y + x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩

/-- Concrete section-family witnesses discharge the cubic slice provider. -/
theorem Section16FinalFreimanFamilies.cubic_slice_provider {N q : Nat} [Fact N.Prime]
    {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q B phi) (hq : 0 < q) :
    Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => cubicBaseExponent (max 1 r * q)) := by
  classical
  choose D f hf hc using h
  exact section16_cubic_slice_provider_of_freiman_families hq B phi D f hf hc

end LeanProofs.GowersSzemeredi
