import GowersSzemeredi.Proofs16ClassPieceCover

/-! Declarations of `Proofs16ClassPieceCover` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- The spectrum count of a family of `n` pieces. -/
def classQb (V : Real) (dC n : Nat) (thS gS : Real) : Real → Real :=
  fun rho => uniformBase V n thS gS rho ^ dC

/-- The spectrum width exponent of a family of `n` pieces. -/
def classEb (V : Real) (dE n : Nat) (thS gS : Real) : Real → Real :=
  fun rho => (uniformBase V n thS gS rho ^ dE)⁻¹

/-- The remainder count: one factor per vertex. -/
def classQr (V : Real) (dC k n : Nat) (thF gF : Real) : Real → Real :=
  fun rho => ∏ _i : Fin (classVertexNum k + 1),
    max (uniformBase V n thF gF (rho / ((classVertexNum k : Real) + 1)) ^ dC)
      ((3 ^ (k + 1) * n : Nat) : Real)

/-- The slice count envelope at `r` samples. -/
def classPb (V : Real) (dC n : Nat) (thF gF : Real) : Nat → Real → Real :=
  fun r eps => uniformBase V (n * r) thF gF |eps| ^ dC

/-- The slice width-exponent envelope at `r` samples. -/
def classEs (V : Real) (dE n : Nat) (thF gF : Real) : Nat → Real → Real :=
  fun r eps => (uniformBase V (n * r) thF gF |eps| ^ dE)⁻¹

theorem uniformBase_nonneg {V : Real} (hV : 1 ≤ V) (n : Nat) {theta gamma rho : Real}
    (ht : 0 < theta) (hg : 0 < gamma) (hr : 0 ≤ rho) : 0 ≤ uniformBase V n theta gamma rho := by
  unfold uniformBase
  have : (0 : Real) ≤ (n : Real) + 1 := by positivity
  have : 0 ≤ 2 / (gamma * theta * rho) := div_nonneg (by norm_num) (by positivity)
  positivity

theorem uniformBase_mono_n {V : Real} (hV : 1 ≤ V) {theta gamma rho : Real} (ht : 0 < theta)
    (hg : 0 < gamma) (hr : 0 ≤ rho) {n n' : Nat} (h : n ≤ n') :
    uniformBase V n theta gamma rho ≤ uniformBase V n' theta gamma rho := by
  unfold uniformBase
  have hc : 0 ≤ V * (2 / (gamma * theta * rho)) :=
    mul_nonneg (by linarith) (div_nonneg (by norm_num) (by positivity))
  have hn : ((n : Real) + 1) ≤ (n' : Real) + 1 := by
    have : (n : Real) ≤ n' := by exact_mod_cast h
    linarith
  calc ((n : Real) + 1) * V * (2 / (gamma * theta * rho))
      = ((n : Real) + 1) * (V * (2 / (gamma * theta * rho))) := by ring
    _ ≤ ((n' : Real) + 1) * (V * (2 / (gamma * theta * rho))) :=
        mul_le_mul_of_nonneg_right hn hc
    _ = _ := by ring

/-- **The family cover of pieces over a uniform class with power controls.** -/
theorem class_piece_family_cover {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V)
    {dC dE dT : Nat} (C : PowerUniformClass k V dC dE dT)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {N : Nat} [NeZero N] [Fact N.Prime] {zeta : Real} (hz : 0 < zeta) (hzHalf : zeta ≤ 1 / 2)
    {mass thS gS thF gF : Real} (htS : 0 < thS) (htS1 : thS ≤ 1) (hgS : 0 < gS) (hgS1 : gS ≤ 1)
    (htF : 0 < thF) (htF1 : thF ≤ 1) (hgF : 0 < gF) (hgF1 : gF ≤ 1)
    {n : Nat} {Gamma : Finset (Point N (k + 1) × ZMod N)}
    (P : Fin n → ClassPiece C Gamma zeta mass thS gS thF gF) :
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (classQr V dC k n thF gF) (classPb V dC n thF gF) n rho)
        ((3 ^ (k + 1) * n : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (classQb V dC n thS gS) (classEb V dE n thS gS)
            (classEr V dE k n thF gF) rho *
          famPieceSliceExponent (classQr V dC k n thF gF) (classEs V dE n thF gF) n rho / 4)
        (section16RoundedPowerThreshold (pieceWidthScale A (classQb V dC n thS gS) zeta rho)
          (pieceLineExponent Bq (classQb V dC n thS gS) (classEb V dE n thS gS)
            (classEr V dE k n thF gF) rho)
          (famPieceSliceExponent (classQr V dC k n thF gF) (classEs V dE n thF gF) n rho)))
      (Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi) := by
  refine class_piece_family_cover_gen hk C ?_ ?_ ?_ ?_ hA hB hlemma6 hz hzHalf htS htS1 hgS hgS1
    htF htF1 hgF hgF1 P
  · intro theta gamma n s ht ht1 hg hg1 hs hs1
    have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hs hs1
    exact one_le_pow₀ (by linarith)
  · intro theta gamma n s ht ht1 hg hg1 hs hs1
    have h2 := uniformBase_two_le hV n ht ht1 hg hg1 hs hs1
    exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))⟩
  · intro theta gamma s ht _ hg _ hs n n' hnn
    exact pow_le_pow_left₀ (uniformBase_nonneg hV _ ht hg hs)
      (uniformBase_mono_n hV ht hg hs hnn) dC
  · intro theta gamma s ht _ hg _ hs n n' hnn
    have h0 : 0 < uniformBase V n theta gamma s := by
      unfold uniformBase
      have : (0 : Real) < (n : Real) + 1 := by positivity
      positivity
    exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_left₀ h0.le
      (uniformBase_mono_n hV ht hg hs.le hnn) dE)

end

end LeanProofs.GowersSzemeredi
