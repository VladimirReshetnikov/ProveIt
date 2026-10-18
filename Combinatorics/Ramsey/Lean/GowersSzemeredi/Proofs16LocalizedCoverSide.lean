import GowersSzemeredi.Proofs16LocalizedCover

/-! Declarations of `Proofs16LocalizedCover` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The source's multiple multilinearity is the instance with its own
control functions. -/
theorem multiplyLinear_iff_with {N k : Nat} [NeZero N] (gamma r : Real)
    (Gamma : Finset (Point N k × ZMod N)) :
    MultiplyLinear gamma r Gamma ↔
      MultiplyLinearWith (fun theta => (multipleQ (r⁻¹ * theta) gamma k) ^ r)
        (fun theta => (multipleC (r⁻¹ * theta) gamma k) ^ r) Gamma :=
  Iff.rfl

/-- Multiple multilinearity can be applied on every preliminary cell with
one graph count and one good set for the entire original box. Parent labels
are retained so subsequent retile arguments can use their short axes. -/
theorem MultiplyLinear.on_partition {N k J : Nat} [NeZero N]
    {gamma t : Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinear gamma t Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (P : Box N k)
    (B : Fin J → Box N k) (hBpart : IsBoxPartition B P) (hBproper : ∀ j, (B j).IsProper) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ M : Fin J → Nat,
      ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ (multipleQ (t⁻¹ * sigma) gamma k) ^ t ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧
      (∀ j a, (R j a).IsProper) ∧
      (∀ j a, ((B j).width : Real) ^ ((multipleC (t⁻¹ * sigma) gamma k) ^ t) ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  have hc : 0 ≤ multipleC (t⁻¹ * sigma) gamma k :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 8) ≠ 0)).pow_nonneg _
  exact MultiplyLinearWith.on_partition ((multiplyLinear_iff_with gamma t Gamma).mp hML)
    sigma hs hs1 (Real.rpow_nonneg (inv_nonneg.mpr hc) _) P B hBpart hBproper

/-- The preliminary short-parent partition, uniform graph count, and global
good set are obtained directly from multiple multilinearity. Every refined
cell retains its short parent for the subsequent relative-step argument. -/
theorem MultiplyLinear.short_parent_cover {N k m : Nat} [NeZero N]
    {gamma t : Real} {Gamma : Finset (Point N k × ZMod N)}
    (hML : MultiplyLinear gamma t Gamma) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1)
    (P : Box N k) (I : ModAP N) (hP : P.IsProper) (hI : I.IsProper)
    (hk : 0 < k) (hm : 4 ≤ m) (hmP : m ≤ P.width) (hmI : m ≤ I.length) :
    ∃ q : Nat, ∃ G : Finset (Point N k), ∃ J : Nat, ∃ B : Fin J → Box N k,
      ∃ M : Fin J → Nat, ∃ R : (j : Fin J) → Fin (M j) → Box N k,
      ∃ mu : (j : Fin J) → Fin (M j) → Fin q → Point N k → ZMod N,
      (q : Real) ≤ (multipleQ (t⁻¹ * sigma) gamma k) ^ t ∧
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsBoxPartition B P ∧ (∀ j, (B j).IsProper) ∧
      (∀ j i, 0 < ((B j).axis i).length ∧
        2 * ((B j).axis i).length ≤ N ∧ ((B j).axis i).length ≤ I.length) ∧
      (∀ j, (B j).commonDiff = P.commonDiff) ∧
      (∀ j, IsBoxPartition (R j) (B j)) ∧ (∀ j a, (R j a).IsProper) ∧
      (∀ j a, ((m : Real) / 8) ^ ((multipleC (t⁻¹ * sigma) gamma k) ^ t) ≤ (R j a).width) ∧
      (∀ j a i, IsMultilinear (mu j a i)) ∧
      ∀ j a x, x ∈ (R j a).carrier → x ∈ G → ∀ y,
        (x, y) ∈ Gamma → ∃ i, y = mu j a i x := by
  have hc : 0 ≤ multipleC (t⁻¹ * sigma) gamma k :=
    (even_two.pow_of_ne_zero (by positivity : (2 : Nat) ^ (k + 8) ≠ 0)).pow_nonneg _
  exact MultiplyLinearWith.short_parent_cover ((multiplyLinear_iff_with gamma t Gamma).mp hML)
    sigma hs hs1 (Real.rpow_nonneg (inv_nonneg.mpr hc) _) (Real.rpow_nonneg hc _)
    P I hP hI hk hm hmP hmI

end LeanProofs.GowersSzemeredi
