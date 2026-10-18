import GowersSzemeredi.Proofs05BoxTransport
import GowersSzemeredi.Proofs16LocalizedCover
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Bertrand

/-! Multiple multilinearity with arbitrary controls passes to subrelations
(`MultiplyLinearWith.subset`).

Finite unions of such relations (`MultiplyLinearWith.union`,
`MultiplyLinearWith.finsetUnion`) are in `Proofs16WithUnionSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Multiple multilinearity passes to subrelations with the same controls. -/
theorem MultiplyLinearWith.subset {N k : Nat} [NeZero N]
    {Q E : Real → Real} {Gamma Delta : Finset (Point N k × ZMod N)}
    (h : MultiplyLinearWith Q E Gamma) (hsub : Delta ⊆ Gamma) :
    MultiplyLinearWith Q E Delta := by
  intro s hs hs1 P hP
  obtain ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu, hcover⟩ :=
    h s hs hs1 P hP
  exact ⟨M, q, H, R, mu, hH, hmass, hpart, hproper, hq, hwidth, hmu,
    fun j x hx hxH y hxy => hcover j x hx hxH y (hsub hxy)⟩

end LeanProofs.GowersSzemeredi
