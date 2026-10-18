import GowersSzemeredi.Proofs16ClassPieceCover

/-! The step of route (II): pieces of `(k+1)`-dimensional relations
(Notes L.6, E4).

Let `C` be a uniform class of dimension `k ≥ 1`.
* `class_piece_of_subrelation`: above `classStepThreshold`, every
  sub-relation `Δ ⊆ Γ` of a product relation with projection of size
  `≥ θN^(k+1)` contains a `ClassPiece` of mass `θ′`. The input is Lemma 15.6
  at dimension `k` with `β = θ/2`, whose arrangement parameter is exactly
  `section16ThetaOne θ γ k`.
* `class_step_decomp`: the greedy decomposition. Off a good set `J` with
  `|J| ≥ (1-θ)N^(k+1)`, the restriction of `Γ` is covered by
  `classPieces γ θ k = ⌊γ⁻²/θ′⌋` pieces of the universal class `StepPiece`.
* `class_step_cover`: any `n` relations so covered have one cover, the
  family cover of their `n·classPieces γ θ k` pieces
  (`class_piece_family_cover`).

So the relations covered by `classPieces γ θ k` step pieces form the next
uniform class, with the raw controls of the family cover. E5 bounds those
controls by powers.

`StepPiece`, `classPieces`, `classStepThr`, `classStepThreshold`,
`classStepThreshold_eq`, `class_piece_of_subrelation`, `class_step_cover`,
`class_step_cover_gen`, `class_step_decomp`, `stepPieceGraphs` and
`thetaOne_half_eq` are in `Proofs16ClassStepSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

variable {k : Nat} {Thr : Real → Real → Real} {Cnt Exp : Real → Real → Nat → Real → Real}

/-! ### Operations on pieces -/

/-- A piece of a sub-relation is a piece of the relation. -/
def ClassPiece.widen (C : UniformClassWith k Thr Cnt Exp) {N : Nat} [NeZero N]
    {Gamma Gamma' : Finset (Point N (k + 1) × ZMod N)} {zeta mass thS gS thF gF : Real}
    (P : ClassPiece C Gamma' zeta mass thS gS thF gF) (hsub : Gamma' ⊆ Gamma) :
    ClassPiece C Gamma zeta mass thS gS thF gF :=
  { P with graph_sub := P.graph_sub.trans hsub }

/-- Forget the mass bound. -/
def ClassPiece.toMassZero (C : UniformClassWith k Thr Cnt Exp) {N : Nat} [NeZero N]
    {Gamma : Finset (Point N (k + 1) × ZMod N)} {zeta mass thS gS thF gF : Real}
    (P : ClassPiece C Gamma zeta mass thS gS thF gF) :
    ClassPiece C Gamma zeta 0 thS gS thF gF :=
  { P with card_ge := by simp }

/-- The empty piece. -/
def ClassPiece.empty (C : UniformClassWith k Thr Cnt Exp) {N : Nat} [NeZero N]
    (Gamma : Finset (Point N (k + 1) × ZMod N)) (zeta thS gS thF gF : Real) :
    ClassPiece C Gamma zeta 0 thS gS thF gF where
  D := ∅
  phi := 0
  graph_sub := by
    intro z hz
    simp [partialGraph] at hz
  card_ge := by simp
  H1 := ∅
  K := fun _ => ∅
  A := fun _ => ∅
  f := fun _ _ => 0
  linear := by intro x hx; simp at hx
  dom := by intro z hz; simp at hz
  G := fun _ _ => 0
  ident := by intro z hz; simp at hz
  spec_U := by
    have h : pieceSpecRel (∅ : Finset (Point N k)) (fun _ => ∅) = ∅ := by
      ext z; simp [pieceSpecRel]
    rw [h]; exact C.empty N thS gS
  face_U := by
    intro e _
    have h : pieceFaceRel (∅ : Finset (Point N (k + 1))) (fun _ _ => (0 : ZMod N)) e = ∅ := by
      ext z; simp [pieceFaceRel]
    rw [h]; exact C.empty N thF gF
  slice_U := by
    intro t
    have h : partialGraph (section16FinalCoordinateSection (∅ : Finset (Point N (k + 1))) t)
        (section16FinalCoordinateRestriction (0 : Point N (k + 1) → ZMod N) t) = ∅ := by
      ext z; simp [partialGraph, section16FinalCoordinateSection]
    rw [h]; exact C.empty N thF gF

end LeanProofs.GowersSzemeredi
