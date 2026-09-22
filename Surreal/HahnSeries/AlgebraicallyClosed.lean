import Surreal.HahnSeries.PolynomialNormalization
import Surreal.HahnSeries.Characteristic
import Surreal.HahnSeries.PolynomialFactorLifting
import Surreal.Algebra.RealClosedPolynomialFactors
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraic closedness of characteristic-zero Hahn fields

For an algebraically closed coefficient field of characteristic zero and a
divisible ordered exponent group, every nonconstant Hahn polynomial has a
root. Translation removes the next-to-leading coefficient. Unless the result
is a pure power, monomial scaling gives a nontrivial depressed residue
polynomial. Its coprime factors lift by the proved Hahn Hensel theorem, and
induction on degree supplies a root of a proper factor.

This constructs the closedness assertion for the fixed Hahn workspaces in
`found:thm:workspace` and `polynomial:prop:workspace`. It does not assume a
surreal normal-form equivalence or prove algebraic closedness of the actual
surcomplex carrier.
-/

namespace Surreal.HahnSeries

open Polynomial Surreal.FinitePolynomial
open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ] [Field K] [CharZero K] [IsAlgClosed K]

/-- The monic root theorem uses strictly smaller-degree lifted factors,
with no algebraic-closedness premise on the Hahn field. -/
theorem exists_root_of_monic_of_isAlgClosed
    {P : Polynomial K⟦Γ⟧} (hP : P.Monic) (hpos : 0 < P.natDegree) :
    ∃ x : K⟦Γ⟧, P.IsRoot x := by
  have h (n : ℕ) : ∀ P : Polynomial K⟦Γ⟧,
      P.natDegree = n → P.Monic → 0 < P.natDegree → ∃ x : K⟦Γ⟧, P.IsRoot x := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hPn hPm hPpos
      let D := depress P
      have hDm : D.Monic := monic_depress hPm
      have hDn : D.natDegree = P.natDegree := natDegree_depress P
      have hDpos : 0 < D.natDegree := hDn.symm ▸ hPpos
      have hDd : D.coeff (D.natDegree - 1) = 0 := by
        simpa only [hDn] using coeff_depress_pred_eq_zero hPm hPpos
      by_cases hPure : D = X ^ D.natDegree
      · have hzero : D.IsRoot 0 := by
          rw [hPure]
          simp only [IsRoot.def, eval_pow, eval_X, zero_pow hDpos.ne']
        exact ⟨0 - depressionShift P, isRoot_of_isRoot_depress hzero⟩
      · obtain ⟨γ, Q, hQm, _, _, hRm, hRn, hRd, hRne, hpull⟩ :=
          exists_monic_depressed_reduction hDm hDd hPure
        let R := Q.map (standardPart Γ K)
        have hRpos : 0 < R.natDegree := hRn.symm ▸ hDpos
        have hRdep : R.coeff (R.natDegree - 1) = 0 := by
          change (Q.map (standardPart Γ K)).coeff ((Q.map (standardPart Γ K)).natDegree - 1) = 0
          simpa only [hRn] using hRd
        have hRnontrivial : R ≠ X ^ R.natDegree := by
          change Q.map (standardPart Γ K) ≠ X ^ (Q.map (standardPart Γ K)).natDegree
          simpa only [hRn] using hRne
        obtain ⟨f, g, hfg, hfm, hgm, hcop, hfpos, hgpos⟩ :=
          exists_coprime_monic_factors hRm
            (IsAlgClosed.exists_root R (degree_ne_of_natDegree_ne hRpos.ne'))
            (depressed_ne_linear_pow hRpos hRdep hRnontrivial)
        have hsum : n = f.natDegree + g.natDegree := by
          rw [← hPn, ← hDn, ← hRn, hfg, natDegree_mul hfm.ne_zero hgm.ne_zero]
        obtain ⟨⟨F, G⟩, ⟨hFm, _, hFn, _, _, _, _, hprod⟩, _⟩ :=
          existsUnique_monic_factorization_of_standardPart f g hfm hgm hcop Q hQm hfg
        let F₀ := F.map (nonnegativeSubring Γ K).subtype
        have hF₀n : F₀.natDegree = f.natDegree :=
          (hFm.natDegree_map (nonnegativeSubring Γ K).subtype).trans hFn
        obtain ⟨x, hx⟩ := ih f.natDegree (by omega) F₀ hF₀n
          (hFm.map _) (hF₀n.symm ▸ hfpos)
        have hxQ : (Q.map (nonnegativeSubring Γ K).subtype).IsRoot x := by
          rw [← hprod, Polynomial.map_mul, IsRoot.def, eval_mul, hx.eq_zero, zero_mul]
        exact ⟨single γ 1 * x - depressionShift P,
          isRoot_of_isRoot_depress ((hpull x).mp hxQ)⟩
  exact h P.natDegree P rfl hP hpos

/-- Every nonconstant polynomial has a root; leading-coefficient normalization
reduces to the constructed monic theorem. -/
theorem exists_root_of_isAlgClosed_coefficients
    {P : Polynomial K⟦Γ⟧} (hpos : 0 < P.natDegree) :
    ∃ x : K⟦Γ⟧, P.IsRoot x := by
  have hP : P ≠ 0 := by
    rintro rfl
    simp only [natDegree_zero, lt_self_iff_false] at hpos
  obtain ⟨x, hx⟩ := exists_root_of_monic_of_isAlgClosed (monic_monicNormalize hP)
    (by simpa only [natDegree_monicNormalize hP] using hpos)
  exact ⟨x, (isRoot_monicNormalize_iff hP x).mp hx⟩

/-- The Hahn field is algebraically closed when the coefficient field is
algebraically closed of characteristic zero and the exponent group is divisible. -/
instance hahnIsAlgClosed : IsAlgClosed K⟦Γ⟧ :=
  IsAlgClosed.of_exists_root K⟦Γ⟧ fun _ hP hIrred =>
    exists_root_of_monic_of_isAlgClosed hP hIrred.natDegree_pos

end

end Surreal.HahnSeries
