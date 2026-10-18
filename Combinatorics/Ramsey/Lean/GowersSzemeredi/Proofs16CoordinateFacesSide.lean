import GowersSzemeredi.Proofs16CoordinateFaces

/-! Declarations of `Proofs16CoordinateFaces` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

theorem CoordinateFace.map_injective {N d l : Nat} (F : CoordinateFace N d l) :
    Function.Injective F.map := by
  intro x y hxy
  funext i
  have h := congrFun hxy (F.free i)
  simpa only [F.map_free] using h

theorem CoordinateFace.domain_mono {N d l : Nat} [NeZero N]
    (F : CoordinateFace N d l) {B C : Finset (Point N d)} (hBC : B ⊆ C) :
    F.domain B ⊆ F.domain C := by
  intro x hx
  exact (F.mem_domain C x).mpr (hBC ((F.mem_domain B x).mp hx))

end LeanProofs.GowersSzemeredi
