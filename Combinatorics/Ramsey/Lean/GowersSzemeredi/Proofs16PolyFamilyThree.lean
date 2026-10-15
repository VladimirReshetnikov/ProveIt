import GowersSzemeredi.Proofs16ThreeSlices
import GowersSzemeredi.Proofs16ThreeCylinders

/-! **The simultaneous cover of finitely many dimension-three pieces**
(Notes L.5, D4).

`PolyPieceThreeData` is a three-dimensional piece in the original frame with
its data exposed, the analogue of `PolyPieceTwoData`:
* the abstract member data of `abstract_family_piece_cover_with` at `k = 2`
  (frequencies `K`, linearity domains `A`, the Bohr-linear part `f`, the
  remainder `rem`);
* the spectrum relation inside the graphs of pieces of the uniform class at
  `(θₛ, γₛ)`;
* the remainder split as `g₁(z₀,z₂) + g₂(z₁,z₂) − g₃(z₂)`. The first two
  relations lie inside piece graphs of the class at `(θ_F, γ_F)`, the third
  in a Freiman cover;
* every final-coordinate slice inside piece graphs of the class at
  `(θ_F, γ_F)`.

`section16_poly_family_three_cover`: the union of the graphs of `m` such
pieces is multiply multilinear. The common relations are covered as follows:
* spectra: the uniform cover at `m·polyTwoPieces` pieces;
* remainders: `MultiplyLinearWith.three_remainder` over the unions of the
  face relations and of the Freiman covers;
* stacked slices of all members' samples: `section16_slices_envelope_cover`
  at `m·r` relations, with power envelopes monotone in `r`.

The inputs are the abstract family Lemma 16.6 in dimension one (for the
two-dimensional pieces) and in dimension two (for the lift). -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The spectrum relation of member data. -/
def specRelTwo {N : Nat} [NeZero N] (H1 : Finset (Point N 2)) (K : Point N 2 → Finset (ZMod N)) :
    Finset (Point N 2 × ZMod N) := by
  classical
  exact (H1 ×ˢ (Finset.univ : Finset (ZMod N))).filter fun z => z.2 ∈ K z.1

/-- **A dimension-three piece with its data, in the original frame.** -/
structure PolyPieceThreeData {N : Nat} [NeZero N] (Gamma : Finset (Point N 3 × ZMod N))
    (zeta mass thS gS thF gF : Real) (q3 : Nat) where
  D : Finset (Point N 3)
  phi : Point N 3 → ZMod N
  graph_sub : partialGraph D phi ⊆ Gamma
  card_ge : mass * (N : Real) ^ 3 ≤ D.card
  H1 : Finset (Point N 2)
  K : Point N 2 → Finset (ZMod N)
  A : Point N 2 → Finset (ZMod N)
  f : Point N 2 → ZMod N → ZMod N
  rem : Point N 3 → ZMod N
  linear : ∀ x ∈ H1, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
    J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x)
  dom : ∀ z ∈ D, section16Init z ∈ H1 ∧ section16Last z ∈ A (section16Init z)
  ident : ∀ z ∈ D,
    phi z = (-1 : ZMod N) ^ 2 * f (section16Init z) (section16Last z) + rem z
  spec : Fin (polyTwoPieces gS thS) → PolyPieceTwo N thS gS
  spec_sub : specRelTwo H1 K ⊆ polyPieceTwoGraphs spec
  g1 : Point N 2 → ZMod N
  g2 : Point N 2 → ZMod N
  g3 : Point N 1 → ZMod N
  rem_eq : ∀ z ∈ D, rem z = g1 (dropMid z) + g2 (dropFirst z) - g3 (lastPt3 z)
  P1 : Fin (polyTwoPieces gF thF) → PolyPieceTwo N thF gF
  P2 : Fin (polyTwoPieces gF thF) → PolyPieceTwo N thF gF
  rel1 : D.image (fun z => (dropMid z, g1 (dropMid z))) ⊆ polyPieceTwoGraphs P1
  rel2 : D.image (fun z => (dropFirst z, g2 (dropFirst z))) ⊆ polyPieceTwoGraphs P2
  rel3 : RelFreimanCover q3 (D.image fun z => (lastPt3 z, g3 (lastPt3 z)))
  slices : ZMod N → Fin (polyTwoPieces gF thF) → PolyPieceTwo N thF gF
  slices_sub : ∀ t, partialGraph (section16FinalCoordinateSection D t)
    (section16FinalCoordinateRestriction phi t) ⊆ polyPieceTwoGraphs (slices t)

/-! ### Flattening families of pieces -/

/-- A family of families of pieces, flattened. -/
def flattenPieces {N : Nat} [NeZero N] {theta gamma : Real} {m n : Nat}
    (Q : Fin m → Fin n → PolyPieceTwo N theta gamma) : Fin (m * n) → PolyPieceTwo N theta gamma :=
  fun i => Q (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem polyPieceTwoGraphs_flatten {N : Nat} [NeZero N] {theta gamma : Real} {m n : Nat}
    (Q : Fin m → Fin n → PolyPieceTwo N theta gamma) (c : Fin m) :
    polyPieceTwoGraphs (Q c) ⊆ polyPieceTwoGraphs (flattenPieces Q) := by
  classical
  intro z hz
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hz
  refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (c, j), Finset.mem_univ _, ?_⟩
  simp only [flattenPieces, Equiv.symm_apply_apply]
  exact hj

/-! ### The controls -/

/-- The slice count envelope of a family of `m` pieces. -/
def famThreePb (thF gF : Real) (K1 p1 m : Nat) : Nat → Real → Real :=
  fun r => threeSlicePb thF gF K1 p1 (m * r)

/-- The slice exponent envelope of a family of `m` pieces. -/
def famThreeEs (thF gF : Real) (K1 p1 m : Nat) : Nat → Real → Real :=
  fun r => threeSliceEs thF gF K1 p1 (m * r)

theorem famThree_slice_ranges {thF gF : Real} (ht : 0 < thF) (ht1 : thF ≤ 1) (hg : 0 < gF)
    (hg1 : gF ≤ 1) (K1 p1 m : Nat) :
    Section16SliceProviderRanges (famThreePb thF gF K1 p1 m) (famThreeEs thF gF K1 p1 m) ∧
      (∀ eps, Monotone fun r => famThreePb thF gF K1 p1 m r eps) ∧
      (∀ eps, 0 < eps → Antitone fun r => famThreeEs thF gF K1 p1 m r eps) := by
  obtain ⟨-, hmono, hanti⟩ := threeSlice_ranges ht ht1 hg hg1 K1 p1
  refine ⟨?_, fun eps r r' h => hmono eps (Nat.mul_le_mul_left m h),
    fun eps he r r' h => hanti eps he (Nat.mul_le_mul_left m h)⟩
  intro r eps _ he he1
  have h2 := threeSliceBase_two_le ht ht1 hg hg1 K1 p1 (m * r) he he1
  have hpos : 0 < threeSliceBase thF gF K1 p1 (m * r) eps := lt_of_lt_of_le (by norm_num) h2
  refine ⟨one_le_pow₀ (le_trans (by norm_num) h2), inv_pos.mpr (pow_pos hpos _), ?_⟩
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_trans (by norm_num) h2))

/-- The spectrum count of a family. -/
def famThreeQb (thS gS : Real) (m : Nat) : Real → Real :=
  uniTwoCount thS gS (m * polyTwoPieces gS thS)

/-- The spectrum exponent of a family. -/
def famThreeEb (A Bq : Nat → Real) (thS gS : Real) (m : Nat) : Real → Real :=
  uniTwoExp A Bq thS gS (m * polyTwoPieces gS thS)

/-- The remainder count of a family. -/
def famThreeQr (thF gF : Real) (q3 m : Nat) : Real → Real :=
  threeRemQ (uniTwoCount thF gF (m * polyTwoPieces gF thF))
    (uniTwoCount thF gF (m * polyTwoPieces gF thF))
    (fun _ => ((3 * (m * q3 + 1) : Nat) : Real))
    (m * polyTwoPieces gF thF) (m * polyTwoPieces gF thF) (m * q3 + 1)

/-- The remainder exponent of a family. -/
def famThreeEr (A Bq : Nat → Real) (thF gF : Real) (q3 m : Nat) : Real → Real :=
  threeRemE (uniTwoExp A Bq thF gF (m * polyTwoPieces gF thF))
    (uniTwoExp A Bq thF gF (m * polyTwoPieces gF thF)) (cubicBaseExponent (m * q3 + 1))

theorem uniTwoCount_nonneg (theta gamma : Real) (M : Nat) (rho : Real) :
    0 ≤ uniTwoCount theta gamma M rho :=
  le_max_of_le_right (Nat.cast_nonneg _)

theorem uniTwoExp_le_one (A Bq : Nat → Real) (theta gamma : Real) (M : Nat) (rho : Real) :
    uniTwoExp A Bq theta gamma M rho ≤ 1 := by
  unfold uniTwoExp
  exact section16CappedWidthExponent_le_one _ _

/-- **The simultaneous cover of finitely many dimension-three pieces.** -/
theorem section16_poly_family_three_cover
    {A2 Bq2 : Nat → Real} (hA2 : ∀ q, 0 < A2 q) (hB2 : ∀ q, 0 < Bq2 q)
    (hlemma6 : AbstractFamilyLemma166At 2 (section16PowerWidth A2 Bq2))
    {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hlemma6' : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {mass thS gS thF gF : Real} (htS : 0 < thS) (htS1 : thS ≤ 1) (hgS : 0 < gS) (hgS1 : gS ≤ 1)
    (htF : 0 < thF) (htF1 : thF ≤ 1) (hgF : 0 < gF) (hgF1 : gF ≤ 1) {q3 : Nat}
    {N : Nat} [NeZero N] [Fact N.Prime] {Gamma : Finset (Point N 3 × ZMod N)}
    {m : Nat} (P : Fin m → PolyPieceThreeData Gamma zeta mass thS gS thF gF q3) :
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (famThreeQr thF gF q3 m) (famThreePb thF gF K1 p1 m) m rho)
        ((3 ^ (2 + 1) * m : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq2 (famThreeQb thS gS m)
            (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thS gS m)
            (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thF gF q3 m) rho *
          famPieceSliceExponent (famThreeQr thF gF q3 m) (famThreeEs thF gF K1 p1 m) m rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A2 (famThreeQb thS gS m) zeta rho)
          (pieceLineExponent Bq2 (famThreeQb thS gS m)
            (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thS gS m)
            (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thF gF q3 m) rho)
          (famPieceSliceExponent (famThreeQr thF gF q3 m) (famThreeEs thF gF K1 p1 m) m rho)))
      (Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi) := by
  classical
  have hA1 : ∀ q, 0 < familyWidthPrefactor K1 q := familyWidthPrefactor_pos (by omega)
  have hB1 : ∀ q, 0 < familyWidthDivisor 1 p1 q := familyWidthDivisor_pos hp1
  -- spectra
  set Gspec := Finset.univ.biUnion fun c : Fin m => specRelTwo (P c).H1 (P c).K
  have hMLspec : MultiplyLinearWith (famThreeQb thS gS m)
      (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thS gS m) Gspec := by
    refine MultiplyLinearWith.subset (section16_poly_piece_two_family_cover hA1 hB1 hlemma6'
      htS htS1 hgS hgS1 (flattenPieces fun c => (P c).spec)) ?_
    intro z hz
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hz
    exact polyPieceTwoGraphs_flatten (fun c => (P c).spec) c ((P c).spec_sub hc)
  -- remainders
  set mf := polyTwoPieces gF thF
  set Λ1 := Finset.univ.biUnion fun c : Fin m =>
    (P c).D.image fun z => (dropMid z, (P c).g1 (dropMid z)) with hΛ1
  set Λ2 := Finset.univ.biUnion fun c : Fin m =>
    (P c).D.image fun z => (dropFirst z, (P c).g2 (dropFirst z)) with hΛ2
  set Λ3 := Finset.univ.biUnion fun c : Fin m =>
    (P c).D.image fun z => (lastPt3 z, (P c).g3 (lastPt3 z)) with hΛ3
  have hΛ1sub : Λ1 ⊆ polyPieceTwoGraphs (flattenPieces fun c => (P c).P1) := by
    intro z hz
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hz
    exact polyPieceTwoGraphs_flatten (fun c => (P c).P1) c ((P c).rel1 hc)
  have hΛ2sub : Λ2 ⊆ polyPieceTwoGraphs (flattenPieces fun c => (P c).P2) := by
    intro z hz
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hz
    exact polyPieceTwoGraphs_flatten (fun c => (P c).P2) c ((P c).rel2 hc)
  have hML1 := MultiplyLinearWith.subset (section16_poly_piece_two_family_cover hA1 hB1 hlemma6'
    htF htF1 hgF hgF1 (flattenPieces fun c => (P c).P1)) hΛ1sub
  have hML2 := MultiplyLinearWith.subset (section16_poly_piece_two_family_cover hA1 hB1 hlemma6'
    htF htF1 hgF hgF1 (flattenPieces fun c => (P c).P2)) hΛ2sub
  have hrem3 : RelFreimanCover (m * q3 + 1) Λ3 :=
    (relFreimanCover_union _ (fun c => (P c).rel3)).pad (Nat.le_succ _)
  have hML3 := hrem3.cubic_cover (Nat.succ_pos _)
  have hEuni : ∀ M : Nat, ∀ t, 0 < t → t ≤ 1 →
      0 < uniTwoExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thF gF M t ∧
        uniTwoExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thF gF M t ≤ 1 :=
    fun M t ht _ => ⟨uniTwoExp_pos hB1 M ht, uniTwoExp_le_one _ _ _ _ _ _⟩
  have hMLrem := MultiplyLinearWith.three_remainder hML1 hML2 hML3
    (fiber_le_of_subset hΛ1sub (polyPieceTwoGraphs_fiber_le _))
    (fiber_le_of_subset hΛ2sub (polyPieceTwoGraphs_fiber_le _)) hrem3.fiber_le
    (fun t _ _ => uniTwoCount_nonneg _ _ _ _) (fun t _ _ => uniTwoCount_nonneg _ _ _ _)
    (fun t _ _ => Nat.cast_nonneg _) (hEuni _) (hEuni _)
    (fun t ht ht1 => ⟨cubicBaseExponent_pos (Nat.succ_pos _) ht,
      cubicBaseExponent_le_one (Nat.succ_pos _) ht ht1⟩)
  have hMLrem' : MultiplyLinearWith (famThreeQr thF gF q3 m)
      (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thF gF q3 m)
      (threeRemainderRel Λ1 Λ2 Λ3) := hMLrem
  -- stacked slices
  let Gs : (r : Nat) → (Fin m → Fin r → ZMod N) → Finset (Point N 2 × ZMod N) :=
    fun r sample => Finset.univ.biUnion fun j : Fin (m * r) =>
      partialGraph (section16FinalCoordinateSection (P (finProdFinEquiv.symm j).1).D
          (sample (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))
        (section16FinalCoordinateRestriction (P (finProdFinEquiv.symm j).1).phi
          (sample (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))
  have hslice : ∀ r sample, MultiplyLinearWith (famThreePb thF gF K1 p1 m r)
      (famThreeEs thF gF K1 p1 m r) (Gs r sample) := by
    intro r sample
    exact section16_slices_envelope_cover hK1 hp1 hlemma6' htF htF1 hgF hgF1 _
      (fun j => (P (finProdFinEquiv.symm j).1).slices
        (sample (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2))
      (fun j => (P (finProdFinEquiv.symm j).1).slices_sub _)
  have hGs : ∀ r sample c h i, appendCoordinate h (sample c i) ∈ (P c).D →
      (h, (P c).phi (appendCoordinate h (sample c i))) ∈ Gs r sample := by
    intro r sample c h i hi
    refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (c, i), Finset.mem_univ _, ?_⟩
    simp only [Equiv.symm_apply_apply]
    refine Finset.mem_image.mpr ⟨h, ?_, rfl⟩
    unfold section16FinalCoordinateSection
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hQb : ∀ s, 0 < s → s ≤ 1 → 0 ≤ famThreeQb thS gS m s ∧
      0 < famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thS gS m s ∧
      famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thS gS m s ≤ 1 :=
    fun s hs _ => ⟨uniTwoCount_nonneg _ _ _ _, uniTwoExp_pos hB1 _ hs, uniTwoExp_le_one _ _ _ _ _ _⟩
  have hEr : ∀ s, 0 < s → s ≤ 1 →
      0 < famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) thF gF q3 m s := by
    intro s hs _
    have h4 : 0 < s / 4 := by positivity
    have h2 : 0 < s / 2 := by positivity
    have a := uniTwoExp_pos (A := familyWidthPrefactor K1) hB1 (theta := thF) (gamma := gF)
      (m * polyTwoPieces gF thF) h4
    have b := cubicBaseExponent_pos (Nat.succ_pos (m * q3)) h2
    unfold famThreeEr threeRemE
    positivity
  obtain ⟨hranges, hPbmono, hEsanti⟩ := famThree_slice_ranges htF htF1 hgF hgF1 K1 p1 m
  have hcover := abstract_family_piece_cover_with (k := 2) (by norm_num) hA2 hB2 hlemma6 hz hzHalf
    hQb hEr hMLspec hMLrem' (ι := Fin m) (H1 := fun c => (P c).H1) (K := fun c => (P c).K)
    (Adom := fun c => (P c).A) (f := fun c => (P c).f) (D := fun c => (P c).D)
    (phi := fun c => (P c).phi) (rem := fun c => (P c).rem)
    (fun c x hx r hr => Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, hr⟩⟩)
    (fun c => (P c).linear) (fun c => (P c).dom) (fun c => (P c).ident)
    (fun c z hz => by
      rw [(P c).rem_eq z hz]
      exact mem_threeRemainderRel
        (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩)
        (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩)
        (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩))
    Gs hslice hGs hranges hPbmono hEsanti
  simpa only [Fintype.card_fin] using hcover

end LeanProofs.GowersSzemeredi
