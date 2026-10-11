import GowersSzemeredi.Proofs16PolyPieceTwoData

/-! **The simultaneous cover of finitely many dimension-two pieces.**

Let `m` pieces of one relation `Γ` be given as `PolyPieceTwoData`. Then the
union of their graphs is `MultiplyLinearWith` at every scale. The controls
are polynomial in `m` and in the pieces' Freiman counts `qs, qr, ql`.

The three common relations of `abstract_family_piece_cover_with` are
unions of the pieces' Freiman covers, each padded by one empty graph:
* spectra, with count `m·qs + 1` (`famTwoQb`, `famTwoEb`);
* remainders, a cylinder over a dimension-one union with count `m·qr + 1`,
  lifted by `MultiplyLinearWith.last_cylinder` (`famTwoQr`, `famTwoEr`);
* stacked slices of all members' samples, with count `m·r·ql + 1`
  (`famTwoPb`, `famTwoEs`).
* `stackedSlices_relFreimanCover`, `section16_poly_family_two_cover`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

def famTwoQb (m qs : Nat) : Real → Real := fun _ => ((3 * (m * qs + 1) : Nat) : Real)
def famTwoEb (m qs : Nat) : Real → Real := cubicBaseExponent (m * qs + 1)
def famTwoQr (m qr : Nat) : Real → Real :=
  fun _ => max ((3 * (m * qr + 1) : Nat) : Real) ((3 ^ (1 + 1) * (m * qr + 1) : Nat) : Real)
def famTwoEr (m qr : Nat) : Real → Real := fun t => cubicBaseExponent (m * qr + 1) t / 16
def famTwoPb (m ql : Nat) : Nat → Real → Real :=
  fun r _ => ((3 * (m * (r * ql) + 1) : Nat) : Real)
def famTwoEs (m ql : Nat) : Nat → Real → Real := fun r => cubicBaseExponent (m * (r * ql) + 1)

/-- Stacked slices of a set with final-coordinate Freiman families. -/
theorem stackedSlices_relFreimanCover {N r ql : Nat} [NeZero N]
    {D : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies ql D phi) (sample : Fin r → ZMod N) :
    RelFreimanCover (r * ql) (section16StackedSlices D phi sample) := by
  classical
  have hu := relFreimanCover_union (fun i : Fin r =>
    partialGraph (section16FinalCoordinateSection D (sample i))
      (section16FinalCoordinateRestriction phi (sample i)))
    (fun i => relFreimanCover_of_familyCover (h (sample i)))
  refine hu.mono ?_
  intro z hz
  unfold section16StackedSlices section16FinsetUnion at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩

theorem famTwoPb_monotone (m ql : Nat) (ε : Real) : Monotone (fun r => famTwoPb m ql r ε) := by
  intro r r' hrr
  simp only [famTwoPb]
  exact_mod_cast Nat.mul_le_mul_left 3 (Nat.add_le_add_right
    (Nat.mul_le_mul_left m (Nat.mul_le_mul_right ql hrr)) 1)

theorem famTwoEs_antitone (m ql : Nat) {ε : Real} (hε : 0 < ε) :
    Antitone (fun r => famTwoEs m ql r ε) := by
  intro r r' hrr
  simp only [famTwoEs]
  unfold cubicBaseExponent
  have hle : ((m * (r * ql) + 1 : Nat) : Real) ≤ ((m * (r' * ql) + 1 : Nat) : Real) := by
    exact_mod_cast Nat.add_le_add_right
      (Nat.mul_le_mul_left m (Nat.mul_le_mul_right ql hrr)) 1
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) hle 4

theorem famTwo_slice_ranges (m ql : Nat) : Section16SliceProviderRanges (famTwoPb m ql) (famTwoEs m ql) := by
  intro r ε _ hε hε1
  have hp : 0 < m * (r * ql) + 1 := Nat.succ_pos _
  refine ⟨?_, cubicBaseExponent_pos hp hε, cubicBaseExponent_le_one hp hε hε1⟩
  simp only [famTwoPb]
  exact_mod_cast (show 1 ≤ 3 * (m * (r * ql) + 1) by omega)

/-- **The simultaneous cover of finitely many dimension-two pieces.** -/
theorem section16_poly_family_two_cover
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {mass : Real} {qs qr ql : Nat}
    {N : Nat} [NeZero N] [Fact N.Prime] {Gamma : Finset (Point N 2 × ZMod N)}
    {m : Nat} (P : Fin m → PolyPieceTwoData Gamma zeta mass qs qr ql) :
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (famTwoQr m qr) (famTwoPb m ql) m rho)
        ((3 ^ (1 + 1) * m : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qr) rho *
          famPieceSliceExponent (famTwoQr m qr) (famTwoEs m ql) m rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A (famTwoQb m qs) zeta rho)
          (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qr) rho)
          (famPieceSliceExponent (famTwoQr m qr) (famTwoEs m ql) m rho)))
      (Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi) := by
  classical
  -- spectra
  set Gspec := Finset.univ.biUnion fun c : Fin m =>
    ((P c).H1 ×ˢ (Finset.univ : Finset (ZMod N))).filter fun z => z.2 ∈ (P c).K z.1 with hGspec
  have hspec : RelFreimanCover (m * qs + 1) Gspec :=
    (relFreimanCover_union _ (fun c => (P c).spec)).pad (Nat.le_succ _)
  have hMLspec : MultiplyLinearWith (famTwoQb m qs) (famTwoEb m qs) Gspec :=
    hspec.cubic_cover (Nat.succ_pos _)
  -- remainders
  set Λ := Finset.univ.biUnion fun c : Fin m =>
    (P c).D.image fun w => (lastPt w, (P c).rem w) with hΛ
  have hrem1 : RelFreimanCover (m * qr + 1) Λ :=
    (relFreimanCover_union _ (fun c => (P c).remc)).pad (Nat.le_succ _)
  have hMLrem := (hrem1.cubic_cover (Nat.succ_pos _)).last_cylinder (m * qr + 1)
    hrem1.fiber_le (fun t _ _ => by positivity)
    (fun t ht ht1 => ⟨cubicBaseExponent_pos (Nat.succ_pos _) ht,
      cubicBaseExponent_le_one (Nat.succ_pos _) ht ht1⟩)
  have hMLrem' : MultiplyLinearWith (famTwoQr m qr) (famTwoEr m qr) (lastCylinder Λ) := hMLrem
  -- stacked slices
  let Gs : (r : Nat) → (Fin m → Fin r → ZMod N) → Finset (Point N 1 × ZMod N) :=
    fun r sample => Finset.univ.biUnion fun c =>
      section16StackedSlices (P c).D (P c).phi (sample c)
  have hslice : ∀ r sample, MultiplyLinearWith (famTwoPb m ql r) (famTwoEs m ql r) (Gs r sample) := by
    intro r sample
    have h := (relFreimanCover_union _ (fun c => stackedSlices_relFreimanCover (P c).slices
      (sample c))).pad (Nat.le_succ (m * (r * ql)))
    exact h.cubic_cover (Nat.succ_pos _)
  have hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ (P c).D →
      (h, (P c).phi (appendCoordinate h (sample c i))) ∈ Gs r sample := by
    intro r sample c h i hi
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, section16StackedSlices_mem h i hi⟩
  have hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ famTwoQb m qs s ∧ 0 < famTwoEb m qs s ∧
      famTwoEb m qs s ≤ 1 := fun s hs hs1 =>
    ⟨Nat.cast_nonneg _, cubicBaseExponent_pos (Nat.succ_pos _) hs,
      cubicBaseExponent_le_one (Nat.succ_pos _) hs hs1⟩
  have hEr : ∀ s, 0 < s → s ≤ 1 → 0 < famTwoEr m qr s := by
    intro s hs _
    have := cubicBaseExponent_pos (Nat.succ_pos (m * qr)) hs
    simp only [famTwoEr]
    positivity
  have hcover := abstract_family_piece_cover_with (k := 1) le_rfl hA hB hlemma6 hz hzHalf hQb hEr
    hMLspec hMLrem' (ι := Fin m) (H1 := fun c => (P c).H1) (K := fun c => (P c).K)
    (Adom := fun c => (P c).A) (f := fun c => (P c).f) (D := fun c => (P c).D)
    (phi := fun c => (P c).phi) (rem := fun c => (P c).rem)
    (fun c x hx r hr => Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, hr⟩⟩)
    (fun c => (P c).linear) (fun c => (P c).dom) (fun c => (P c).ident)
    (fun c z hz => mem_lastCylinder.mpr (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩))
    Gs hslice hGs (famTwo_slice_ranges m ql) (fun ε => famTwoPb_monotone m ql ε)
    (fun ε hε => famTwoEs_antitone m ql hε)
  simpa only [Fintype.card_fin] using hcover

end LeanProofs.GowersSzemeredi
