import GowersSzemeredi.Proofs16FibreGeometry
import GowersSzemeredi.Proofs16WidthMonotonicity

/-! # Affine extensions and the selected fibre domain for Lemma 16.9 -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Choose a globally affine map agreeing on the domain whenever the fibre
is selected; unselected fibres may use the zero map. -/
theorem conditional_affine_extension {N : Nat} [NeZero N]
    (C : Prop) (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (h : C → LinearOn A f) :
    ∃ ell : ZMod N → ZMod N, LinearOn Finset.univ ell ∧
      (C → ∀ x ∈ A, f x = ell x) := by
  classical
  by_cases hC : C
  · obtain ⟨ell, hlin, heq⟩ := (h hC).exists_extension
    exact ⟨ell, hlin, fun _ => heq⟩
  · exact ⟨fun _ => 0, ⟨0, 0, by simp⟩, fun hc => False.elim (hC hc)⟩

/-- A good pair lies in the selected base and in the induced value domain. -/
theorem section16GoodDomain_fibre_mem {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H H1 : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 h : Point N k) (x : ZMod N) (hH : H1 ⊆ H)
    (hz : appendCoordinate h x ∈ section16GoodDomain B H1 Y x0) :
    h ∈ H1 ∧ (h, x) ∈ section16InducedDomain B H Y := by
  classical
  have hz' : Section16GoodInducedPair B H1 Y x0 (h, x) := by
    have hmem := (Finset.mem_filter.mp hz).2
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using hmem
  refine ⟨hz'.1, ?_⟩
  obtain ⟨C, hC, _, hx⟩ := hz'.2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH hz'.1, C, hC, hx⟩

/-- Adding a fixed affine map to each multilinear fibre preserves the
number of globally affine covering functions. -/
theorem affine_plus_multilinear_fibres {N k q : Nat} [NeZero N]
    (mu : Fin q → Point N (k + 1) → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (h : Point N k) (ell : ZMod N → ZMod N) (hell : LinearOn Finset.univ ell)
    (c : ZMod N) :
    ∀ i, LinearOn Finset.univ (fun x => c * ell x + mu i (appendCoordinate h x)) := by
  intro i
  exact (hell.const_mul c).add ((hmu i).linearOn_last_fibre h)

end LeanProofs.GowersSzemeredi
