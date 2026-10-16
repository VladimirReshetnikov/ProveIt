import GowersSzemeredi.Proofs16SinglePieceSections
import GowersSzemeredi.Proofs16JointCovers

/-! **Joint slices: the two anchor sections covered together** (Notes L.16q).

`single_piece_on_line_cell_of_slices` applies the dimension-`k` provider to
the cross-section `φ(·, a)`, and then to `φ(·, b)` inside the first agreement
set. The second application works at the density `c(θ₁)` that the first one
left, so the density is `θ₁·c(c(θ₁))` and the `t`-degrees of the slice
control multiply. Here the two cross-sections are given by covers
(`MultiplyLinearWith Qb Eb`). `joint_cover_on` composes them at the common
precision `θ₁/4`, and one pigeonhole (`JointCoverOn.piece`) gives one box
carrying both maps:
* density `jointSliceDensity Qb θ q = θ₁·(θ₁/2)/Qb(θ₁/4)²`: the degrees add;
* width `jointSliceWidth Eb θ q L = ⌈L^(Eb(θ₁/4)²)⌉`.

This is the slice scheme `jointSliceScheme`. The line-cell, affine-cell,
spectrum-cover and core lemmas of the single-piece lift hold for every slice
scheme (`single_piece_on_line_cell_of_scheme` and its successors), so the
joint-slice lift is their instance (`single_piece_lift_global_cover_with_joint`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The density of the joint-slice step: `θ₁·(θ₁/2)/Qb(θ₁/4)²`, `θ₁ = θ³/(4q²)`. -/
def jointSliceDensity (Qb : Real → Real) (theta : Real) (q : Nat) : Real :=
  singlePieceTheta theta q *
    ((singlePieceTheta theta q - (singlePieceTheta theta q / 4 + singlePieceTheta theta q / 4)) /
      (Qb (singlePieceTheta theta q / 4) * Qb (singlePieceTheta theta q / 4)))

/-- The width of the joint-slice step: `⌈L^(Eb(θ₁/4)²)⌉`. -/
def jointSliceWidth (Eb : Real → Real) (theta : Real) (q L : Nat) : Nat :=
  ⌈(L : Real) ^ (Eb (singlePieceTheta theta q / 4) * Eb (singlePieceTheta theta q / 4))⌉₊

/-- The two sections covered jointly at the common precision `θ/4`
(`joint_cover_on`, then one pigeonhole by `JointCoverOn.piece`): width
`⌈L^(Eb(θ/4)²)⌉`, density `(θ − θ/2)/Qb(θ/4)²`. -/
def jointSliceScheme {N k : Nat} [NeZero N] (Qb Eb : Real → Real)
    (hQ : ∀ t, 0 < t → t ≤ 1 → 1 ≤ Qb t) (hE : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Eb t) :
    SliceScheme N k where
  SL D g := MultiplyLinearWith Qb Eb (partialGraph D g)
  wid θ L := ⌈(L : Real) ^ (Eb (θ / 4) * Eb (θ / 4))⌉₊
  dens θ := (θ - (θ / 4 + θ / 4)) / (Qb (θ / 4) * Qb (θ / 4))
  wid_mono θ hθ hθ1 L1 L2 h := by
    have he := hE (θ / 4) (by positivity) (by linarith)
    exact Nat.ceil_le_ceil
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (mul_nonneg he he))
  dens_pos θ hθ hθ1 := by
    have hQ1 := hQ (θ / 4) (by positivity) (by linarith)
    exact div_pos (by linarith) (by nlinarith)
  step θ hθ hθ1 T H Da Db ga gb hT hTne hHT hHa hHb hHc ha hb := by
    have hρ0 : 0 < θ / 4 := by positivity
    have hρ1 : θ / 4 ≤ 1 := by linarith
    have hJC := joint_cover_on (ι := Bool) (fun e => bif e then Da else Db)
      (fun e => bif e then ga else gb) (fun _ => Qb) (fun _ => Eb) (fun _ => θ / 4) Finset.univ
      (fun e _ => by cases e <;> assumption) (fun _ _ => ⟨hρ0, hρ1⟩)
      (fun _ _ => zero_le_one.trans (hQ _ hρ0 hρ1)) (fun _ _ => hE _ hρ0 hρ1) T hT
    simp only [Fintype.sum_bool, Fintype.prod_bool] at hJC
    obtain ⟨R, nu, hR, hRT, hRw, hnu, hRc⟩ := hJC.piece (theta := θ) (by linarith) H hHT
      (fun e _ => by cases e <;> assumption) hHc hTne
    refine ⟨R, nu true, nu false, hR, hRT, Nat.ceil_le.mpr hRw, hnu _ (Finset.mem_univ _),
      hnu _ (Finset.mem_univ _), hRc.trans ?_⟩
    exact_mod_cast Finset.card_le_card fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, forall_const, Bool.forall_bool, cond_false,
        cond_true] at hx ⊢
      exact ⟨hx.1, hx.2.1, hx.2.2.2, hx.2.2.1⟩

end LeanProofs.GowersSzemeredi
