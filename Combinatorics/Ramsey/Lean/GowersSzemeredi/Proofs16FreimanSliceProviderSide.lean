import GowersSzemeredi.Proofs16FreimanSliceProvider
import GowersSzemeredi.Proofs16WithLiftSide

/-! Declarations of `Proofs16FreimanSliceProvider` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- Two-dimensional affine lifting with the concrete Freiman-family provider.
Only the line-cover and individual-section Freiman-cover inputs remain. -/
theorem section16_two_dimensional_cover_of_freiman_families
    {N q : Nat} [Fact N.Prime] (hq : 0 < q)
    {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    {theta gamma : Real} {Qd Ed : Real → Real}
    (hline : Section16AllBoxLineCoversWith theta gamma Qd Ed B phi)
    (D : ZMod N → Fin q → Finset (Point N 1))
    (f : ZMod N → Fin q → Point N 1 → ZMod N)
    (hfreiman : ∀ t i, FreimanHom 8 (pointOneDomain (D t i)) (pointOneMap (f t i)))
    (hcover : ∀ t, partialGraph (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) ⊆
        section16FinsetUnion (fun i => partialGraph (D t i) (f t i)))
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hEd : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Ed s)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (m : Nat) (P : Box N 2) (hP : P.IsProper) (hm : m ≤ P.width) :
    let sigma := rho / 4
    ∃ qGamma qDelta : Nat,
      (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma 1 ∧
      (qDelta : Real) ≤ Qd (sigma / 2) ∧
      let l := lemma9WidthWith m qDelta 1 sigma theta gamma (Ed (sigma / 2))
        (section16Zeta theta gamma 1)
      let r := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
      let p : Real := ((3 * (max 1 r * q) : Nat) : Real)
      ∃ (n : Nat) (H : Finset (Point N 2)) (L : Nat)
        (Q : Fin L → Box N 2) (mu : Fin L → Fin n → Point N 2 → ZMod N),
        (n : Real) ≤ max p ((r.choose 2 : Real) * p * p) ∧
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, Real.sqrt (((Nat.floor l : Real) / 8) ^
          (polyBaseExponent (max 1 r * q) sigma)) / 4 ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  exact hline.explicit_multilinear_cover_with
    (section16_slice_provider_of_freiman_families hq B phi D f hfreiman hcover)
    (section16_freiman_slice_provider_ranges hq) (by decide)
    ht ht1 hg hg1 hEd hrho hrho1 m P hP hm

end

end LeanProofs.GowersSzemeredi
