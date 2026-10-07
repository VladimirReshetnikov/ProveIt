import GowersSzemeredi.Proofs16GlobalGraphCover

/-! Choosing every cube in the full domain makes the good induced domain
full as well. Translation leaves a function of the final coordinate unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16GoodDomain_full {N k : Nat} [NeZero N] (x0 : Point N k) :
    section16GoodDomain (Finset.univ : Finset (Point N (k + 1))) Finset.univ
      (fun _ => Finset.univ) x0 = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro z
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
  let C : AxisCube N k := ⟨x0, section16Init z⟩
  have hC : (C, section16Last z) ∈ section16CubeDomain Finset.univ (section16Init z) := by
    simp [section16CubeDomain, C, AxisCube.side]
  exact ⟨⟨(C, section16Last z), hC⟩, Finset.mem_univ _, rfl, rfl⟩

theorem section16PhiOne_last_function {N k : Nat} (f : ZMod N → ZMod N) (x0 : Point N k) :
    section16PhiOne (fun z : Point N (k + 1) => f (section16Last z)) x0 =
      (fun z => f (section16Last z)) := by
  funext z
  simp only [section16PhiOne, section16Last, appendCoordinate_eq_snoc, Fin.snoc_last]

end LeanProofs.GowersSzemeredi
