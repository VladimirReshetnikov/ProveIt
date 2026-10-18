import GowersSzemeredi.Proofs16SinglePieceRemainder
import GowersSzemeredi.Proofs16DenseSelection
import GowersSzemeredi.Proofs16CommonBase
import GowersSzemeredi.Proofs16SpectrumInduction
import GowersSzemeredi.Proofs16GoodDomainTransport
import GowersSzemeredi.Proofs16VertexIdentity
import GowersSzemeredi.Proofs08AffineFrequencyProgression

/-! The single-piece lift, step 5 (Notes L.1): the assembly with Gowers's
own objects.

Take a pair `(B, φ)` with Lemma 16.4's arrangement conditions (ii) and
(iii) and the product property; condition (i), the cover-form
cross-section hypothesis, is not used. `single_piece_lift` produces one
proper `(k+1)`-box `S` and one multilinear `μ` with
`ρ·|S| ≤ |{z ∈ B ∩ S : φ z = μ z}|`, where `ρ` is polynomial in the input
densities whenever the providers are. The chain:
1. Lemma 16.5 without (i) (`section16_dense_induced_selection_of_arrangements`)
   and Lemma 16.7 (`lemma_16_7_holds`) give `H`, `Y`, `φ′`, `x₀`. The good
   domain `B₁` has density `θ₂` in the full box, and
   `φ₁ = (−1)^k φ′ + φ″` on `B₁`.
2. `remainder_piece`: one multilinear `M″` for `φ″` on a
   `C^[2^k−1](θ₂)` fraction of a sub-box.
3. A short-parent cell of that sub-box (`exists_short_parent_dense_cell`).
4. `single_piece_of_spectrum_cover`, with the spectrum relation `Δ`
   (product property by Lemma 14.3, fibres `≤ δ⁻²` by Parseval). The slice
   providers for `φ₁(·, x)` come from translated last-coordinate faces
   (`slice_localPieceFor`).
5. Translate the piece of `φ₁` back to a piece of `φ`.

**Warning.** `single_piece_lift` assumes the box-local inputs
`LocalRelationCoverAt` and `LocalMultilinearPieceAt`, which are false for
growing widths (Notes L.2). It is therefore vacuous as stated. The
provider form `single_piece_lift_core` (`Proofs16SinglePieceGlobal`) is the
usable statement. The helpers here (`lastSliceFace`, `fullSpaceBox`,
`exists_short_parent_dense_cell`, `section16SpectrumRelation_fibre_le`)
remain valid. The inputs of `single_piece_lift`:
* `LocalRelationCoverAt k δ`;
* `LocalMultilinearPieceAt k` for the slices;
* vertex providers `(C, W)`, which `vertex_localPieceFor` supplies from
  lower-dimensional inputs;
* the retiled linearity bound, supplied by
  `exists_polynomial_retiled_linearity_profile`.

`LocalMultilinearPieceAt.slice_localPieceFor`, `liftRemainderRho`,
`liftRemainderWidth`, `section16SpectrumRelation_fibre_le`, `single_piece_lift`
and `vertex_providers_of_low` are in `Proofs16SinglePieceLiftSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The face of `(k+1)`-space with free first coordinates and last coordinate `x`. -/
def lastSliceFace {N : Nat} (k : Nat) (x : ZMod N) : CoordinateFace N (k + 1) k where
  free := ⟨Fin.castSucc, Fin.castSucc_injective k⟩
  anchor := appendCoordinate 0 x
  map h := appendCoordinate h x
  map_free := by
    intro h i
    simp [appendCoordinate_eq_snoc]
  map_fixed := by
    intro h j hj
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact ((hj i) rfl).elim
    · simp [appendCoordinate_eq_snoc]

/-- The full box of `(ℤ/N)^d`. -/
def fullSpaceBox (N d : Nat) : Box N d where
  axis := fun _ => modInterval N 0 N
  commonDiff := 1
  axis_step := fun _ => rfl

theorem fullSpaceBox_carrier (N d : Nat) [NeZero N] :
    (fullSpaceBox N d).carrier = Finset.univ := by
  ext x
  simp [fullSpaceBox, Box.carrier, modInterval_zero_modulus_carrier]

theorem fullSpaceBox_isProper (N d : Nat) [NeZero N] : (fullSpaceBox N d).IsProper := by
  intro i
  change (modInterval N 0 N).carrier.card = N
  rw [modInterval_zero_modulus_carrier, Finset.card_univ, ZMod.card]

theorem fullSpaceBox_width (N d : Nat) (hd : 0 < d) : (fullSpaceBox N d).width = N := by
  apply Nat.le_antisymm
  · exact (fullSpaceBox N d).width_le_axis_length ⟨0, hd⟩
  · exact Box.le_width_of_le_axis _ hd (fun _ => le_rfl)

/-- **A short-parent dense cell** of a proper `(k+1)`-box. -/
theorem exists_short_parent_dense_cell {N k : Nat} [NeZero N] [Fact N.Prime] (hk : 0 < k)
    (R : Box N (k + 1)) (hR : R.IsProper) (h4 : 4 ≤ R.width)
    (E : Finset (Point N (k + 1))) (hER : E ⊆ R.carrier) (hEne : E.Nonempty)
    {ρ : Real} (hρ : ρ * R.carrier.card ≤ E.card) :
    ∃ Q : Box N k, Q.IsProper ∧ Q.carrier ⊆ (boxInit R).carrier ∧
      (R.width : Real) / 8 ≤ Q.width ∧
      2 * (Q.axis ⟨0, hk⟩).length ≤ N ∧
      (Q.axis ⟨0, hk⟩).length ≤ (R.axis (Fin.last k)).length ∧
      Q.commonDiff = R.commonDiff ∧ Q.commonDiff ≠ 0 ∧
      ρ * (lastProductSet Q.carrier (R.axis (Fin.last k)).carrier).card ≤
        (E.filter fun z => z ∈ lastProductSet Q.carrier (R.axis (Fin.last k)).carrier).card := by
  set I := R.axis (Fin.last k)
  have hI : I.IsProper := hR (Fin.last k)
  have hIlen : R.width ≤ I.length := R.width_le_axis_length (Fin.last k)
  obtain ⟨L, Q, hQpart, hQprop, hQaxes, hQstep⟩ :=
    (boxInit R).short_parent_partition I (boxInit_isProper R hR) hI hk h4
      (boxInit_width R hk) hIlen
  have hRcarrier : R.carrier = lastProductSet (boxInit R).carrier I.carrier :=
    (boxInit_last_product R).1
  obtain ⟨l, hl⟩ := exists_dense_cell (fun l => lastProductSet (Q l).carrier I.carrier)
    _ (lastProductSet_partition _ _ _ hQpart) E id
    (fun z hz => by rw [← hRcarrier]; exact hER hz) hEne (by rw [← hRcarrier]; exact hρ)
  have hu := I.step_isUnit_of_prime hI (by omega)
  refine ⟨Q l, (hQprop l).1, IsPartition.cell_subset hQpart l, (hQprop l).2,
    (hQaxes l _).2.1, (hQaxes l _).2.2, hQstep l, ?_, hl⟩
  rw [hQstep l]
  have hstep : I.step = R.commonDiff := R.axis_step (Fin.last k)
  rw [hstep] at hu
  exact hu.ne_zero

theorem appendCoordinate_add {N k : Nat} (a b : Point N k) (x y : ZMod N) :
    appendCoordinate a x + appendCoordinate b y = appendCoordinate (a + b) (x + y) := by
  funext i
  by_cases hi : i.val < k
  · simp [appendCoordinate, hi]
  · simp [appendCoordinate, hi]

end LeanProofs.GowersSzemeredi
