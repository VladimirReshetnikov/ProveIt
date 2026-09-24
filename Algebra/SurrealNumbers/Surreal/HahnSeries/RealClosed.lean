import Surreal.Algebra.RealClosedPolynomialFactors
import Surreal.Algebra.PolynomialDepression
import Surreal.HahnSeries.PolynomialNormalization
import Surreal.HahnSeries.PolynomialFactorLifting
import Surreal.HahnSeries.SquareRoots
import Surreal.HahnSeries.Characteristic

/-!
# Real closedness of Hahn fields

An ordered real closed coefficient field and a divisible ordered abelian
exponent group give a real closed Hahn field. The odd-degree root proof is
induction on polynomial degree: translation and monomial scaling produce a
nontrivial depressed residue polynomial; a coprime odd-degree residue factor
lifts by the proved Hahn Hensel theorem and has strictly smaller degree.

The previously constructed nonnegative square roots then complete Mathlib's
`IsRealClosed` interface. This concerns the actual set-sized Hahn field, not
an assumed infinite normal-form map into the sign-sequence surreal field.
-/

namespace Surreal.HahnSeries

open Polynomial
open _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The order synonym leaves the Hahn ring operations unchanged. -/
def hahnToLexRingEquiv : K⟦Γ⟧ ≃+* Lex K⟦Γ⟧ where
  toFun := toLex
  invFun := ofLex
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] [DivisibleBy Γ ℕ]

/-- Every monic odd-degree Hahn polynomial has a root. The recursive call
is on a strictly smaller odd-degree factor, not on a sequence of approximations. -/
theorem exists_isRoot_of_monic_odd_natDegree (P : Polynomial K⟦Γ⟧)
    (hP : P.Monic) (hodd : Odd P.natDegree) : ∃ x : K⟦Γ⟧, P.IsRoot x := by
  classical
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    let D := FinitePolynomial.depress P
    have hD : D.Monic := FinitePolynomial.monic_depress hP
    have hDd : D.natDegree = P.natDegree := FinitePolynomial.natDegree_depress P
    have hdep : D.coeff (D.natDegree - 1) = 0 := by
      rw [hDd]
      exact FinitePolynomial.coeff_depress_pred_eq_zero hP hodd.pos
    apply (FinitePolynomial.exists_root_depress_iff P).mp
    by_cases hpower : D = X ^ D.natDegree
    · refine ⟨0, ?_⟩
      change D.IsRoot 0
      rw [hpower, IsRoot.def, eval_pow, eval_X, zero_pow (by simpa only [hDd] using hodd.pos.ne')]
    · obtain ⟨γ, Q, hQ, _, _, hR, hRd, hRdep, hRne, hroot⟩ :=
        exists_monic_depressed_reduction hD hdep hpower
      obtain ⟨f, g, hfg, hf, hg, hcop, hfodd, _, hflt, _⟩ :=
        FinitePolynomial.realClosed_depressed_odd_coprime_factorization hR
          (by simpa only [hRd, hDd] using hodd)
          (by simpa only [hRd] using hRdep)
          (by simpa only [hRd] using hRne)
      obtain ⟨⟨F, G⟩, ⟨hF, _, hFd, _, _, _, _, hFG⟩, _⟩ :=
        existsUnique_monic_factorization_of_standardPart f g hf hg hcop Q hQ hfg
      let F' := F.map (nonnegativeSubring Γ K).subtype
      have hF' : F'.Monic := hF.map _
      have hF'd : F'.natDegree = f.natDegree := (hF.natDegree_map _).trans hFd
      have hsmaller : F'.natDegree < n := by
        simpa only [hF'd, hRd, hDd, hn] using hflt
      obtain ⟨x, hx⟩ := ih F'.natDegree hsmaller F' hF'
        (by simpa only [hF'd] using hfodd) rfl
      refine ⟨single γ 1 * x, (hroot x).mp ?_⟩
      rw [← hFG, Polynomial.map_mul, IsRoot.def, eval_mul, hx.eq_zero, zero_mul]

/-- Leading-coefficient normalization removes the monicity restriction from
the Hahn odd-degree root theorem. -/
theorem exists_isRoot_of_odd_natDegree (P : Polynomial K⟦Γ⟧)
    (hodd : Odd P.natDegree) : ∃ x : K⟦Γ⟧, P.IsRoot x := by
  have hP : P ≠ 0 := by
    intro h
    simp only [h, natDegree_zero, Nat.not_odd_zero] at hodd
  obtain ⟨x, hx⟩ := exists_isRoot_of_monic_odd_natDegree (FinitePolynomial.monicNormalize P)
    (FinitePolynomial.monic_monicNormalize hP)
    (by simpa only [FinitePolynomial.natDegree_monicNormalize hP] using hodd)
  exact ⟨x, (FinitePolynomial.isRoot_monicNormalize_iff hP x).mp hx⟩

/-- Odd-degree root existence transported to the actual lexicographic Hahn field. -/
theorem exists_isRoot_of_odd_natDegree_lex (P : Polynomial (Lex K⟦Γ⟧))
    (hodd : Odd P.natDegree) : ∃ x : Lex K⟦Γ⟧, P.IsRoot x := by
  let Q := P.map (hahnToLexRingEquiv (Γ := Γ) (K := K)).symm.toRingHom
  have hQd : Q.natDegree = P.natDegree :=
    natDegree_map_eq_of_injective hahnToLexRingEquiv.symm.injective P
  obtain ⟨x, hx⟩ := exists_isRoot_of_odd_natDegree Q (by simpa only [hQd] using hodd)
  refine ⟨toLex x, ?_⟩
  exact hx.of_map (f := (hahnToLexRingEquiv (Γ := Γ) (K := K)).symm.toRingHom)
    (hahnToLexRingEquiv (Γ := Γ) (K := K)).symm.injective

/-- Divisible-group Hahn fields over ordered real closed coefficients are real
closed. Both square roots and odd-degree polynomial roots have been constructed. -/
instance hahnLexIsRealClosed : IsRealClosed (Lex K⟦Γ⟧) :=
  IsRealClosed.of_linearOrderedField
    (fun hx => isSquare_of_nonneg_lex hx)
    (fun hf => exists_isRoot_of_odd_natDegree_lex _ hf)

/-- Real closedness is algebraic, so the same construction also equips the
underlying Hahn field without its order synonym. -/
instance hahnIsRealClosed : IsRealClosed K⟦Γ⟧ :=
  hahnLexIsRealClosed (Γ := Γ) (K := K)

end

end Surreal.HahnSeries
