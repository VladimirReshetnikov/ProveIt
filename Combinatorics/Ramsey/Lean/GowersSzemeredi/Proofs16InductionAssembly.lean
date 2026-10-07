import GowersSzemeredi.Proofs16GreedyRelations
import GowersSzemeredi.Proofs16Union
import GowersSzemeredi.Proofs16GlobalGraphCover
import GowersSzemeredi.Proofs16CoverParameterMonotonicity

/-! Closing Theorem 16.2 from a large unit-multiply-linear piece.
The conclusion is the exact catalogue type, conditional on the unresolved
large-piece input. Empty extracted families are handled explicitly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem multiplyLinear_empty {N k : Nat} [NeZero N] {gamma r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 1 ≤ r) :
    MultiplyLinear gamma r (∅ : Finset (Point N k × ZMod N)) := by
  have h := (isMultilinear_constant (N := N) (d := k) 0).multiplyLinearFunction
    ∅ hg hg1 hr
  simpa [MultiplyLinearFunction, partialGraph] using h

/-- Arbitrary-dimensional assembly from a uniform positive mass per good
piece. The control parameter only needs to bound the total number of pieces. -/
theorem section16_multiplyLinear_of_large_pieces {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) {gamma theta mass r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hmass : 0 < mass) (hr : 1 ≤ r)
    (hcard : (Gamma.card : Real) ≤ r * mass)
    (hextract : ∀ Delta ⊆ Gamma,
      theta * (N : Real) ^ k ≤ (relationProjection Delta).card →
      ∃ D ⊆ Delta, mass ≤ D.card ∧ MultiplyLinear gamma 1 D) :
    ∃ J : Finset (Point N k), (1 - theta) * (N : Real) ^ k ≤ J.card ∧
      MultiplyLinear gamma r (restrictRelation Gamma J) := by
  classical
  obtain ⟨q, G, J, hG, hq, hJ, hcover⟩ :=
    section16_greedy_relation_decomposition (MultiplyLinear gamma 1) theta mass hmass
      Gamma hextract
  refine ⟨J, hJ, ?_⟩
  have hqr : (q : Real) ≤ r := (mul_le_mul_iff_left₀ hmass).mp (hq.trans hcard)
  by_cases hq0 : q = 0
  · subst q
    have hempty : section16FinsetUnion G = ∅ := by simp [section16FinsetUnion]
    rw [hempty] at hcover
    exact multiplyLinear_downward_closed_holds N k gamma r _ _ hcover
      (multiplyLinear_empty hg hg1 hr)
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hu := BaseCase.properMultiplyLinear_finsetUnion gamma 1 le_rfl G hqpos
      (fun i => (hG i).2)
    simp only [mul_one] at hu
    have hqone : (1 : Real) ≤ q := by exact_mod_cast hqpos
    exact multiplyLinear_downward_closed_holds N k gamma r _ _ hcover
      (hu.mono_parameter hg hg1 hqone hqr)

/-- The remaining large-piece assertion sufficient for the exact fixed-
dimension Theorem 16.2. Its modulus threshold must be uniform in the input
relation, as required by the finite extraction argument. -/
def Section16LargePieceAt (k : Nat) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N k × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
        RelationProductProperty gamma Gamma →
        theta * (N : Real) ^ k ≤ (relationProjection Gamma).card →
        ∃ D ⊆ Gamma, (N : Real) ^ k / multipleS theta gamma k ≤ D.card ∧
          MultiplyLinear gamma 1 D

/-- All finite iteration and union bookkeeping in Theorem 16.2 is discharged;
only the large structured-piece theorem remains an input. -/
theorem theorem_16_2_of_large_piece {k : Nat} (hpiece : Section16LargePieceAt k) :
    Theorem162At k := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨N0, hN0⟩ := hpiece gamma theta hg hg1 ht ht1
  refine ⟨N0, fun N _ _ hN Gamma hcard hprod => ?_⟩
  have hs := one_le_multipleS k ht ht1 hg hg1
  have hs0 : 0 < multipleS theta gamma k := zero_lt_one.trans_le hs
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hr : 1 ≤ gamma ^ (-(2 : Int)) * multipleS theta gamma k :=
    one_le_mul_of_one_le_of_one_le hginv hs
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply section16_multiplyLinear_of_large_pieces Gamma hg hg1
    (by positivity : 0 < (N : Real) ^ k / multipleS theta gamma k) hr
  · calc
      (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k := hcard
      _ = (gamma ^ (-(2 : Int)) * multipleS theta gamma k) *
          ((N : Real) ^ k / multipleS theta gamma k) := by field_simp
  · intro Delta hDelta hlarge
    exact hN0 N hN Delta ((Nat.cast_le.mpr (Finset.card_le_card hDelta)).trans hcard)
      (hprod.mono hDelta) hlarge

end LeanProofs.GowersSzemeredi
