import GowersSzemeredi.Proofs16BaseCaseRestriction
import GowersSzemeredi.Proofs14HigherArrangements

/-! At height zero, two-arrangements are ordinary additive quadruples.
The product property and the moment amplification therefore supply the
eight-arrangement input needed for the one-dimensional extraction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def zeroArrangementEquiv (N d : Nat) : GeneralArrangement N 0 d ≃ (Fin (2 * d) → ZMod N) where
  toFun R := R.crossSection
  invFun x := (default, default, x)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl

theorem zeroArrangement_vertex {N d : Nat} (R : GeneralArrangement N 0 d)
    (e : Fin 0 → Bool) (j : Fin (2 * d)) :
    R.vertex e j = (BaseCase.pointOneEquiv N).symm (R.crossSection j) := by
  funext i
  fin_cases i
  simp [GeneralArrangement.vertex, appendCoordinate, BaseCase.pointOneEquiv]

theorem zeroArrangement_cubeValue {N d : Nat} [NeZero N]
    (R : GeneralArrangement N 0 d) (phi : Point N 1 → ZMod N) (j : Fin (2 * d)) :
    R.cubeValue phi j = BaseCase.pointOneMap phi (R.crossSection j) := by
  classical
  unfold GeneralArrangement.cubeValue
  rw [Fintype.sum_unique]
  simp [zeroArrangement_vertex, boolWeight, countWhere, BaseCase.pointOneMap]

theorem isAdditiveTuple_two_iff {N : Nat} (q : Fin 4 → ZMod N) :
    IsAdditiveTuple (k := 2) q ↔ IsAdditiveQuadruple q := by
  simp [IsAdditiveTuple, IsAdditiveQuadruple, Fin.sum_univ_succ, Finset.sum_filter]

theorem respectedGeneralArrangementCount_two_zero {N : Nat} [NeZero N]
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N) :
    respectedGeneralArrangementCount 2 B phi =
      phiAdditiveCount (BaseCase.pointOneDomain B) (BaseCase.pointOneMap phi) := by
  classical
  unfold respectedGeneralArrangementCount phiAdditiveCount countWhere
  apply Finset.card_equiv (zeroArrangementEquiv N 2)
  intro R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hvertices : (∀ (e : Fin 0 → Bool) j, R.vertex e j ∈ B) ↔
      ∀ j, R.crossSection j ∈ BaseCase.pointOneDomain B := by
    simp only [zeroArrangement_vertex, BaseCase.mem_pointOneDomain]
    constructor
    · intro h j
      exact h default j
    · intro h e j
      exact h j
  simp only [GeneralArrangement.IsIn, GeneralArrangement.IsRespected,
    zeroArrangement_cubeValue, isAdditiveTuple_two_iff, hvertices,
    IsPhiAdditive, IsAdditiveQuadruple, zeroArrangementEquiv]
  tauto

theorem productProperty_zero_eight_arrangements {N : Nat} [NeZero N]
    (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N) {beta gamma : Real}
    (hb : 0 < beta) (hg : 0 < gamma)
    (hB : beta * (N : Real) ≤ B.card) (hprod : HasProductProperty B phi gamma) :
    beta ^ 28 * gamma ^ 56 * (N : Real) ^ 15 ≤ respectedGeneralArrangementCount 8 B phi := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hquad := BaseCase.productProperty_one_additive gamma B phi hprod
  have htwo : (beta ^ 4 * gamma ^ 8) * (N : Real) ^ (5 * 0 + 3) ≤
      respectedGeneralArrangementCount 2 B phi := by
    rw [respectedGeneralArrangementCount_two_zero]
    calc
      (beta ^ 4 * gamma ^ 8) * (N : Real) ^ (5 * 0 + 3) =
          gamma ^ 8 * (N : Real)⁻¹ * (beta * N) ^ 4 := by
        field_simp
      _ ≤ gamma ^ 8 * (N : Real)⁻¹ * (B.card : Real) ^ 4 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB 4) (by positivity)
      _ ≤ _ := hquad
  have hheight := lemma_14_7_holds N 0 (beta ^ 4 * gamma ^ 8) B phi (by positivity) htwo
  simpa only [mul_pow, ← pow_mul, Nat.reduceMul, Nat.zero_add] using hheight

end LeanProofs.GowersSzemeredi
