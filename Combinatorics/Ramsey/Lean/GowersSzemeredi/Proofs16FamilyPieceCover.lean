import GowersSzemeredi.Proofs16FamilyLemma6
import GowersSzemeredi.Proofs16FamilyAffineLift

/-! **The simultaneous union: one cover for a whole family of pieces.**

Step (B) of Notes L.3, final assembly. A finite family of structured pieces
`(B c, φ c, H c, H1 c, Y c, φ′ c, x₀ c, D c)`, `c : ι`, has common inputs:
* one relation `Γ` covering all large spectra, with controls `(Qb, Eb)`;
* one relation `Γr` containing all remainder graphs, with controls
  `(Qr, Er)`;
* a stacked slice provider `Gs` whose relations contain all members'
  sampled slices, with controls `(Pb, Es)`.

Then the union `⋃_c graph(D c, φ₁ c)` is `MultiplyLinearWith` at every
scale. The width exponent is the single-piece one at the sample bound
`famPieceSamples ≈ 24·Qr(ρ/8)·|ι|/ρ`. The count is
`|ι|·max(Pb, C(S,2)·Pb²)`, or `3^(k+1)·|ι|` on short boxes. Nothing is
refined sequentially, so the exponent is not raised to the power `|ι|`.
That is the difference from `MultiplyLinearWith.union`, which this
replaces for unions of pieces (Part H.2).
* `card_biUnion_partialGraph_fiber_le`.

The assembly itself is stated for abstract members in
`Proofs16AbstractFamily` (`abstract_family_piece_large_box_profile`,
`abstract_family_piece_cover_with`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The sample bound for a family of `n` members at loss `ρ`. -/
def famPieceSamples (Qr : Real → Real) (n : Nat) (rho : Real) : Nat :=
  ⌈6 * max 1 (Qr (rho / 8)) * ((max 1 n : Nat) : Real) / (rho / 4)⌉₊

/-- The graph count of the family cover on large boxes. -/
def famPieceGraphBound (Qr : Real → Real) (Pb : Nat → Real → Real) (n : Nat) (rho : Real) :
    Real :=
  (n : Real) * max (Pb (famPieceSamples Qr n rho) (rho / 4))
    (((famPieceSamples Qr n rho).choose 2 : Nat) * Pb (famPieceSamples Qr n rho) (rho / 4) *
      Pb (famPieceSamples Qr n rho) (rho / 4))

/-- The slice exponent at the family sample bound. -/
def famPieceSliceExponent (Qr : Real → Real) (Es : Nat → Real → Real) (n : Nat)
    (rho : Real) : Real :=
  Es (famPieceSamples Qr n rho) (rho / 4)

theorem famPieceSamples_pos {Qr : Real → Real} {n : Nat} {rho : Real} (hrho : 0 < rho) :
    0 < famPieceSamples Qr n rho := by
  unfold famPieceSamples
  apply Nat.ceil_pos.mpr
  positivity

/-- A union of `|ι|` partial graphs has at most `|ι|` values over each point. -/
theorem card_biUnion_partialGraph_fiber_le {N k : Nat} {ι : Type} [Fintype ι]
    (D : ι → Finset (Point N k)) (f : ι → Point N k → ZMod N) (x : Point N k) :
    ((Finset.univ.biUnion fun c => partialGraph (D c) (f c)).filter
      fun z => z.1 = x).card ≤ Fintype.card ι := by
  rw [Finset.filter_biUnion]
  calc (Finset.univ.biUnion fun c => (partialGraph (D c) (f c)).filter fun z => z.1 = x).card
      ≤ ∑ c, ((partialGraph (D c) (f c)).filter fun z => z.1 = x).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c : ι, 1 := Finset.sum_le_sum fun c _ => partialGraph_fiber_card_le_one _ _ x
    _ = Fintype.card ι := by simp

end LeanProofs.GowersSzemeredi
