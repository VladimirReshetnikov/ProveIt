import Surreal.Foundations.SignSequencePolynomialNormalization
import Surreal.Algebra.PolynomialDepression
import Surreal.Algebra.RealPolynomialFactors

/-!
# Finite preparation of the actual odd-degree-root problem

This combines the finite steps in Conway, *On Numbers and Games*, Chapter 3,
Theorem 25: translate to depressed form, scale by an actual Conway monomial,
and factor the ordinary-real reduction. It is progress toward the
real-closedness obligation distinguished in `found:sub:realclosed`.

For a monic odd-degree polynomial, the pure-power case gives an explicit
root. Otherwise the reduction has two coprime monic real factors, one of
positive odd degree strictly below the original degree. The affine change
of variables and the exact root pullback are part of the conclusion.

The residue factors are not asserted to lift to the actual sign field.
No odd-degree-root existence theorem or `IsRealClosed` instance is claimed.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

open Polynomial Surreal.FinitePolynomial

/-- The two finite changes of variable give an explicit affine scaling formula. -/
theorem scalePolynomial_depress_eq (P : Polynomial SignSequence.{u}) (t : SignSequence.{u}) :
    scalePolynomial (depress P) t =
      C ((t ^ P.natDegree)⁻¹) * P.comp (C t * X - C (depressionShift P)) := by
  exact FinitePolynomial.scalePolynomial_depress_eq P t

/-- A root of the scaled depressed polynomial pulls back by the specified affine map. -/
theorem isRoot_scalePolynomial_depress_iff (P : Polynomial SignSequence.{u})
    {t : SignSequence.{u}} (ht : t ≠ 0) (x : SignSequence.{u}) :
    (scalePolynomial (depress P) t).IsRoot x ↔
      P.IsRoot (t * x - depressionShift P) :=
  (isRoot_scalePolynomial_iff (depress P) ht x).trans (isRoot_depress_iff P (t * x))

/-- Complete finite preparation for a monic odd-degree sign-field polynomial.
The first alternative is an explicit root. The second supplies a positive
monomial scale, its finite monic polynomial with the exact affine formula,
and coprime ordinary-real residue factors with the induction degree bounds. -/
theorem explicit_root_or_coprime_residue_preparation
    {P : Polynomial SignSequence.{u}} (hm : P.Monic) (hodd : Odd P.natDegree) :
    P.IsRoot (-depressionShift P) ∨
      ∃ (s γ : SignSequence.{u}) (Q : Polynomial SignSequence.{u})
        (hfinite : ∀ j, IsFinite (Q.coeff j)) (f g : ℝ[X]),
        s = depressionShift P ∧ 0 < omegaPower γ ∧
        Q = C (((omegaPower γ) ^ P.natDegree)⁻¹) * P.comp (C (omegaPower γ) * X - C s) ∧
        Q.Monic ∧ Q.natDegree = P.natDegree ∧ Q.coeff (Q.natDegree - 1) = 0 ∧
        (∀ x, Q.IsRoot x ↔ P.IsRoot (omegaPower γ * x - s)) ∧
        reducePolynomial Q hfinite = f * g ∧
        (reducePolynomial Q hfinite).natDegree = P.natDegree ∧
        f.Monic ∧ g.Monic ∧ IsCoprime f g ∧ Odd f.natDegree ∧
        0 < f.natDegree ∧ f.natDegree < P.natDegree ∧ 0 < g.natDegree ∧
        P.natDegree = f.natDegree + g.natDegree := by
  let D := depress P
  have hDm : D.Monic := monic_depress hm
  have hDn : D.natDegree = P.natDegree := natDegree_depress P
  have hDpos : 0 < D.natDegree := hDn.symm ▸ hodd.pos
  have hDd : D.coeff (D.natDegree - 1) = 0 := by
    simpa only [hDn] using coeff_depress_pred_eq_zero hm hodd.pos
  by_cases hPure : D = X ^ D.natDegree
  · left
    have hzero : D.IsRoot 0 := by
      rw [hPure]
      simp only [IsRoot.def, eval_pow, eval_X, zero_pow hDpos.ne']
    simpa only [zero_sub] using isRoot_of_isRoot_depress (P := P) hzero
  · right
    obtain ⟨γ, hfinite, hRm, hRn, _, hRd, hRne⟩ :=
      exists_monic_depressed_reduction hDm hDpos hDd hPure
    let Q := scalePolynomial D (omegaPower γ)
    let R := reducePolynomial Q hfinite
    have hRodd : Odd R.natDegree := by
      rw [show R.natDegree = D.natDegree from hRn, hDn]
      exact hodd
    obtain ⟨f, g, hfg, hfm, hgm, hcop, hfodd, hfpos, hflt, hgpos⟩ :=
      real_depressed_odd_coprime_factorization hRm hRodd hRd hRne
    have hQn : Q.natDegree = P.natDegree :=
      (scalePolynomial_natDegree D (omegaPower_ne_zero γ)).trans hDn
    have hRdegree : R.natDegree = P.natDegree := hRn.trans hDn
    have hsum : P.natDegree = f.natDegree + g.natDegree := by
      rw [← hRdegree, show R = f * g from hfg, natDegree_mul hfm.ne_zero hgm.ne_zero]
    refine ⟨depressionShift P, γ, Q, hfinite, f, g, rfl, omegaPower_pos γ,
      scalePolynomial_depress_eq P (omegaPower γ),
      scalePolynomial_monic hDm (omegaPower_ne_zero γ), hQn,
      scalePolynomial_depressed (omegaPower_ne_zero γ) hDd, ?_, hfg, hRdegree,
      hfm, hgm, hcop, hfodd, hfpos, hflt.trans_eq hRdegree, hgpos, hsum⟩
    exact fun x => isRoot_scalePolynomial_depress_iff P (omegaPower_ne_zero γ) x

end

end Surreal.Foundations.SignSequence
