import GowersSzemeredi.Proofs16GoodDomainTransport

/-! The fixed-final-coordinate premise of Lemma 16.10 follows from the
proper cross-sections of the actual structured pair and translation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def CoordinateFace.lastSlice {N k : Nat} (x : ZMod N) : CoordinateFace N (k + 1) k where
  free := ⟨Fin.castSucc, Fin.castSucc_injective k⟩
  anchor := appendCoordinate 0 x
  map h := appendCoordinate h x
  map_free := by
    intro h i
    rw [appendCoordinate_eq_snoc]
    simp
  map_fixed := by
    intro h j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · intro _; simp [appendCoordinate_eq_snoc]
    · intro hj; exact (hj i rfl).elim

/-- Translate each fixed-final-coordinate cross-section and restrict it to
the selected good domain. The same parameter is retained exactly. -/
theorem ProperCrossSectionsMultiplyLinear.good_domain_final_sections
    {N k : Nat} [NeZero N] [Fact N.Prime] {gamma r : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (h : ProperCrossSectionsMultiplyLinear gamma r B phi)
    (H : Finset (Point N k)) (Y : (a : Point N k) → Finset (Section16CubeElement B a))
    (x0 : Point N k) :
    FinalCoordinateSectionsMultiplyLinear gamma r (section16GoodDomain B H Y x0)
      (section16PhiOne phi x0) := by
  classical
  intro x
  let F : CoordinateFace N (k + 1) k := CoordinateFace.lastSlice x
  have hp := (h k (Nat.lt_succ_self k) F).translate (-x0)
  have heq : (fun y => F.pullback phi (y + -(-x0))) =
      section16FinalCoordinateRestriction (section16PhiOne phi x0) x := by
    funext y
    simp [F, CoordinateFace.lastSlice, CoordinateFace.pullback,
      section16FinalCoordinateRestriction, section16PhiOne,
      section16Init_appendCoordinate, section16Last_appendCoordinate, add_comm]
    rfl
  rw [heq] at hp
  apply hp.mono
  intro y hy
  have hv := section16GoodDomain_vertex_mem B H Y x0 (Finset.mem_filter.mp hy).2 (fun _ => true)
  have hb : appendCoordinate (y + x0) x ∈ B := by
    simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate,
      ite_true, ← Pi.add_def, add_comm] using hv
  apply Finset.mem_image.mpr
  refine ⟨y + x0, ?_, by simp⟩
  exact (F.mem_domain B _).mpr hb

/-- The first packaged premise of Lemma 16.10 is a theorem for the genuine
structured pair, independently of any line-cover or lifting assumption. -/
theorem Section16StructuredPair.good_domain_final_sections
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (h : Section16StructuredPair theta gamma B phi)
    (H : Finset (Point N k)) (Y : (a : Point N k) → Finset (Section16CubeElement B a))
    (x0 : Point N k) :
    FinalCoordinateSectionsMultiplyLinear gamma
      (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
      (section16GoodDomain B H Y x0) (section16PhiOne phi x0) :=
  h.1.good_domain_final_sections H Y x0

end LeanProofs.GowersSzemeredi
