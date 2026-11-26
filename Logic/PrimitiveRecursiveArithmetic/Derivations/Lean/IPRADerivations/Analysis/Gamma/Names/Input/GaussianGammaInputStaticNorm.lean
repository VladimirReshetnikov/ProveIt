import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaExponentCoefficientPolynomial
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianPolynomialNormBuffers
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower

/-!
# A numerical input coefficient-norm envelope for Gamma

For actual canonical buffers the original unit weighted norm is the
ordinary coefficient norm. The unchanged original Gamma weighted-mass
supplier at radius one therefore gives ||input(q,N,L)||_1 <= N+2 for
N>=2, independently of precision and degree horizon. In particular,
the original C19 cutoff N=2R has envelope 2R+2.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaInputStaticNorm

open_ipra
open GaussianRationalSyntheticDivision (qone qmul_congr canonicalCoefficients canonical_coefficient_at)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianRationalPolynomialDilation (dilated weightedNorm)
open GaussianRationalSyntheticBounds (natCode)
open GaussianGammaExponentCoefficientPolynomial (polynomial massNumerator)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianEuclideanDistanceName (fraction fraction_order)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem unit_weighted_norm (C N : PTm n) (hL : Γ ⊢[PRAAx] length C ≐ succ N)
    (hc : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx] weightedNorm C N qone ≐ coefficientNorm C := by
  have hl : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hL.shift
  have hh : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by simpa [Fm.shift,Syn.shift] using hc.shift
  apply GaussianPolynomialNormBuffers.norm_entries _ _ (succ N) (GaussianRationalPolynomialDilation.dilated_length _ _ _) hL
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) := by simpa [Δ,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans range
  have canonical := canonical_coefficient_at (Syn.shift C) (var 0) hh.wk (lt_congr (.eqRefl _) hl.wk.eqSymm range)
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialDilation.subst_dilated,GaussianRationalSyntheticDivision.subst_qone] using
    (GaussianRationalPolynomialDilation.dilated_lookup (Syn.shift C) (Syn.shift N) qone (var 0) hi).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianRationalRoundedPower.qone_power _)).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ canonical))

theorem input_norm (q N L : PTm n) (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (polynomial q N L)) (natCode (N+two)) := by
  have pos := le_trans (le_succ_self one) hN
  have actual := GaussianGammaExponentCoefficientPolynomial.polynomial_weighted_bound (Γ := Γ) q N L one pos
    (le_congr (by ipra_ring) (.eqRefl N) hN)
  have unit := unit_weighted_norm (Γ := Γ) (polynomial q N L) (degree L)
    (GaussianGammaExponentCoefficientPolynomial.polynomial_length q N L) (GaussianRationalMonicReduction.added_canonical _ _ _)
  have cleared : Γ ⊢[PRAAx] le (massNumerator one N*one) ((N+two)*N) := by
    refine le_of_eq_add (d := LeanProofs.IPRA.PTm.monus N one) ?_
    have form := natEq (eq_add_of_le (Γ := Γ) pos)
    apply deriveNat
    unfold massNumerator
    ipra_simps
    rw [form]
    ring
  exact RationalArgmin.transitive (RationalArgmin.rationalLE_congr unit (.eqRefl _) actual)
    (fraction_order (massNumerator one N) N (N+two) one pos (le_refl one)
      (le_congr (mul_comm _ _) (.eqRefl _) cleared))

theorem original_input_norm (q R L : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (polynomial q (two*R) L)) (natCode (two*R+two)) :=
  input_norm _ _ _ (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two hR))

theorem original_C19_canonical_input_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (coefficientNorm (polynomial (var 0) (two*succ (var 1)) (var 1))) (natCode (two*succ (var 1)+two))) :=
  closeUniv 2 (original_input_norm _ _ _ (zero_lt_succ _))

end LeanProofs.IPRA.Analysis.GaussianGammaInputStaticNorm
