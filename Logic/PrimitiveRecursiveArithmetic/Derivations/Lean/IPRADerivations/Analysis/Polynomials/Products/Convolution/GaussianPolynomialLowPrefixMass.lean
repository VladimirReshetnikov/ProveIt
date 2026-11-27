import IPRADerivations.Analysis.Polynomials.Products.Convolution.GaussianPolynomialLowPrefix
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianPolynomialNormBuffers

/-!
# Coefficient mass of a stored low-degree prefix

Padding the prefix with leading zero coefficients aligns its stored entries
with the original descending coefficient buffer. Termwise order then gives
the mass bound for the original stored prefix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialLowPrefixMass

open_ipra
open GaussianCoefficientL1 (coefficientNorm prefix_monotone qL1_congr)
open GaussianPolynomialLowPrefix (polynomial polynomial_length polynomial_lookup)
open GaussianRationalHorner (canonical_congr)
open GaussianRationalL1 (qL1)
open GaussianRationalPolynomialBuffers (leftPad pad_length pad_leading pad_tail)
open GaussianRationalSyntheticDivision (canonicalCoefficients canonical_coefficient_at subst_canonicalCoefficients)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr subst_length)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem padded_length (C N d : PTm n) (hd : Γ ⊢[PRAAx] le d N) :
    Γ ⊢[PRAAx] length (leftPad (polynomial C N d) (monus N d)) ≐ succ N := by
  refine (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (polynomial_length C N d)).eqTrans ?_)
  exact (add_succ (monus N d) d).eqTrans
    (congrSucc ((add_comm (monus N d) d).eqTrans (eq_add_of_le hd).eqSymm))

private theorem padded_term_bound (C N d i : PTm n) (hd : Γ ⊢[PRAAx] le d N)
    (hi : Γ ⊢[PRAAx] lt i (succ N)) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (leftPad (polynomial C N d) (monus N d)) i)) (qL1 (entry C i)) := by
  refine .orE (lt_or_le i (monus N d)) ?_ ?_
  · have h : lt i (monus N d) :: Γ ⊢[PRAAx] lt i (monus N d) := Prf.hyp0
    have eq := (qL1_congr (pad_leading (polynomial C N d) (monus N d) i h)).eqTrans
      GaussianRationalLinearProduct.qzero_norm
    exact rationalLE_congr eq.eqSymm (.eqRefl _) (GaussianCoefficientNormOrder.qL1_zero_lower _)
  · let Δ := le (monus N d) i :: Γ
    let j := monus i (monus N d)
    have ia : Δ ⊢[PRAAx] i ≐ monus N d+j := eq_add_of_le Prf.hyp0
    have iLeN : Δ ⊢[PRAAx] le i N := (succ_monus_succ _ _).eqSymm.eqTrans hi.wk
    have Nform := eq_add_of_le iLeN
    have dForm : Δ ⊢[PRAAx] d ≐ j+monus N i :=
      add_left_cancel ((add_comm (monus N d) d).eqTrans ((eq_add_of_le hd.wk).eqSymm.eqTrans
        (Nform.eqTrans ((congrAdd ia (.eqRefl _)).eqTrans (add_assoc _ _ _)))))
    have jLeD : Δ ⊢[PRAAx] le j d := le_of_eq_add dForm
    have jInside : Δ ⊢[PRAAx] lt j (length (polynomial C N d)) :=
      lt_congr (.eqRefl _) (polynomial_length C N d).eqSymm ((succ_monus_succ _ _).eqTrans jLeD)
    have index : Δ ⊢[PRAAx] monus N (monus d j) ≐ i :=
      (congrMonus (.eqRefl _) (Common.monus_of_eq dForm)).eqTrans
        (Common.monus_of_eq (Nform.eqTrans (add_comm _ _)))
    have eq := (entry_congr (.eqRefl _) ia).eqTrans
      ((pad_tail (polynomial C N d) (monus N d) j jInside).eqTrans
        ((polynomial_lookup C N d j jLeD).eqTrans (entry_congr (.eqRefl _) index)))
    exact rationalLE_congr (qL1_congr eq).eqSymm (.eqRefl _) (RationalArgmin.reflexive _)

theorem low_prefix_mass (C N d : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hd : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx] rationalLE (coefficientNorm (polynomial C N d)) (coefficientNorm C) := by
  let P := leftPad (polynomial C N d) (monus N d)
  have cmp : Γ ⊢[PRAAx] rationalLE (GaussianCoefficientL1.prefixNorm P (succ N))
      (GaussianCoefficientL1.prefixNorm C (succ N)) := by
    refine prefix_monotone P C (succ N) (.allI (.impI ?_))
    let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] le (Syn.shift d) (Syn.shift N) := by
      simpa only [Δ,Fm.shift,Syn.shift,subst_le] using hd.shift.wk
    simpa only [P,Δ,Syn.shift,GaussianPolynomialLowPrefix.subst_polynomial,
      GaussianRationalPolynomialBuffers.subst_leftPad,LeanProofs.IPRA.PTm.subst_monus,ConciseIPRA.PTm.subst_succ] using
      padded_term_bound (Syn.shift C) (Syn.shift N) (Syn.shift d) (var 0) hs (Prf.hyp0 (Γ := Γ.map Fm.shift))
  exact rationalLE_congr
    ((GaussianRationalLinearProduct.norm_length P (succ N) (padded_length C N d hd)).eqSymm.eqTrans
      (GaussianPolynomialNormBuffers.norm_padding (polynomial C N d) (monus N d)))
    (GaussianRationalLinearProduct.norm_length C (succ N) hLen).eqSymm cmp

theorem low_prefix_canonical (C N d : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx] canonicalCoefficients (polynomial C N d) := by
  refine .allI (.impI ?_)
  let E := polynomial (Syn.shift C) (Syn.shift N) (Syn.shift d)
  let Δ := lt (var 0) (length E) :: Γ.map Fm.shift
  have hsLen : Δ ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Δ,Fm.shift,Syn.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ] using hLen.shift.wk
  have hsCan : Δ ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Δ,Fm.shift,Syn.shift,subst_canonicalCoefficients] using hCan.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) (length E) := Prf.hyp0
  have iLe : Δ ⊢[PRAAx] le (var 0) (Syn.shift d) := (succ_monus_succ _ _).eqSymm.eqTrans
    (lt_congr (.eqRefl _) (polynomial_length (Syn.shift C) (Syn.shift N) (Syn.shift d)) hi)
  have inside : Δ ⊢[PRAAx] lt (monus (Syn.shift N) (monus (Syn.shift d) (var 0))) (length (Syn.shift C)) :=
    lt_congr (.eqRefl _) hsLen.eqSymm ((succ_monus_succ _ _).eqTrans (Common.monus_le_self _ _))
  simpa only [Δ,E,Syn.shift,GaussianPolynomialLowPrefix.subst_polynomial] using
    canonical_congr (polynomial_lookup (Syn.shift C) (Syn.shift N) (Syn.shift d) (var 0) iLe)
      (canonical_coefficient_at (Syn.shift C) _ hsCan inside)

theorem actual_stored_low_prefix_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶
      (le (var 2) (var 1) ⟶ rationalLE
        (coefficientNorm (polynomial (var 0) (var 1) (var 2))) (coefficientNorm (var 0)))) :=
  closeUniv 3 (.impI (.impI (low_prefix_mass _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialLowPrefixMass
