import IPRADerivations.Analysis.GaussianRationalDeflationError
import IPRADerivations.Analysis.GaussianRationalPolynomialBuffers

/-!
# Coefficient L1 norms of the actual polynomial buffers

Equal bounded entries preserve the computed norm. Zero padding and
appending a zero preserve the full norm, and actual coefficientwise
scaling satisfies the scalar L1 product bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialNormBuffers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientL1
  (normBody prefixNorm coefficientNorm norm_body_at prefix_succ qL1_congr subst_prefixNorm)
open GaussianCoefficientNormOrder (prefixNorm_congr)
open GaussianRationalDeflationError (zeroBody zero_sum zero_term)
open GaussianRationalLinearProduct (norm_length scalar_add_zero qzero_norm)
open GaussianRationalPolynomialBuffers
  (zeros zeros_length zeros_lookup appendZero append_length append_lookup
    leftPad pad_length pad_leading pad_tail added added_length added_lookup)
open GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup)
open GaussianRationalL1 (qL1)
open GaussianRationalL1Algebra (qL1_multiply)
open GaussianRationalSyntheticBounds (natCode)
open GaussianRationalSumSegments (entriesEqual)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem prefix_entries (C D N : PTm n) (h : Γ ⊢[PRAAx] entriesEqual C D N) :
    Γ ⊢[PRAAx] prefixNorm C N ≐ prefixNorm D N := by
  refine RationalFiniteSum.sum_ext _ _ _ _ _ (.allI (.impI ?_))
  have equality := Prf.impE h.allOpen.wk (Prf.hyp0 : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] _)
  simpa only [norm_body_at] using
    RationalArgmin.rationalEq_congr (qL1_congr equality).eqSymm (.eqRefl _) (.eqRefl _)

theorem norm_entries (C D N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N)
    (hD : Γ ⊢[PRAAx] length D ≐ N) (h : Γ ⊢[PRAAx] entriesEqual C D N) :
    Γ ⊢[PRAAx] coefficientNorm C ≐ coefficientNorm D :=
  (norm_length C N hC).eqTrans ((prefix_entries C D N h).eqTrans (norm_length D N hD).eqSymm)

theorem zero_prefix (C N : PTm n) (h : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶ entry (Syn.shift C) (var 0) ≐ GaussianRationalHorner.qzero)) :
    Γ ⊢[PRAAx] prefixNorm C N ≐ natCode zero := by
  have same : Γ ⊢[PRAAx] RationalFiniteSum.termwiseEq normBody zeroBody N C zero := by
    refine .allI (.impI ?_)
    have eq := Prf.impE h.allOpen.wk (Prf.hyp0 : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] _)
    simpa only [norm_body_at, zero_term] using
      RationalArgmin.rationalEq_congr ((qL1_congr eq).eqTrans qzero_norm).eqSymm (.eqRefl _) (.eqRefl _)
  exact (RationalFiniteSum.sum_ext _ _ _ _ _ same).eqTrans (zero_sum N zero)

theorem norm_zeros (N : PTm n) : Γ ⊢[PRAAx] coefficientNorm (zeros N) ≐ natCode zero := by
  refine (norm_length _ _ (zeros_length N)).eqTrans (zero_prefix _ _ (.allI (.impI ?_)))
  simpa only [Syn.shift, GaussianRationalPolynomialBuffers.subst_zeros] using
    zeros_lookup (Syn.shift N) (var 0) Prf.hyp0

theorem norm_append (C : PTm n) : Γ ⊢[PRAAx] coefficientNorm (appendZero C) ≐ coefficientNorm C := by
  let D := appendZero C
  let L := length C
  have before : Γ ⊢[PRAAx] entriesEqual D C L := by
    refine .allI (.impI ?_)
    simpa only [D, L, Syn.shift, GaussianRationalPolynomialBuffers.subst_appendZero,
      Foundations.SequenceComposition.subst_length] using
      (append_lookup (Syn.shift C) (var 0) (le_of_lt Prf.hyp0)).eqTrans
        (GaussianRationalLinearProduct.padded_inside _ _ _ Prf.hyp0)
  have term : Γ ⊢[PRAAx] entry D L ≐ GaussianRationalHorner.qzero :=
    (append_lookup _ _ (le_refl _)).eqTrans (GaussianRationalLinearProduct.padded_outside C L L (le_refl L))
  exact (norm_length _ _ (append_length C)).eqTrans ((prefix_succ D L).eqTrans
    ((RationalAlgebra.add_congr (prefix_entries _ _ _ before) ((qL1_congr term).eqTrans qzero_norm)).eqTrans
      (scalar_add_zero _ (GaussianCoefficientL1.norm_guard C))))

theorem padding_prefix_zero (C t : PTm n) : Γ ⊢[PRAAx] prefixNorm (leftPad C t) t ≐ natCode zero := by
  refine zero_prefix _ _ (.allI (.impI ?_))
  simpa only [Syn.shift, GaussianRationalPolynomialBuffers.subst_leftPad] using
    pad_leading (Syn.shift C) (Syn.shift t) (var 0) Prf.hyp0

def padLaw (C t r : PTm n) : Fm PTm n :=
  le r (length C) ⟶ prefixNorm (leftPad C t) (t + r) ≐ prefixNorm C r

@[simp] theorem subst_padLaw {k : ℕ} (σ : Fin n → PTm k) (C t r : PTm n) :
    (padLaw C t r).subst σ = padLaw (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ r) := by simp [padLaw]

theorem padding_prefix (C t r : PTm n) (hr : Γ ⊢[PRAAx] le r (length C)) :
    Γ ⊢[PRAAx] prefixNorm (leftPad C t) (t + r) ≐ prefixNorm C r := by
  have all : Γ ⊢[PRAAx] .all (padLaw (Syn.shift C) (Syn.shift t) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [subst_padLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI ?_
      exact (prefixNorm_congr (.eqRefl _) (add_zero t)).eqTrans
        ((padding_prefix_zero C t).eqTrans
          (GaussianRationalLinearProduct.scalar_zero_code.eqTrans (GaussianCoefficientL1.prefix_zero C).eqSymm))
    · simp only [subst_padLaw, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let A := Syn.shift C
      let T := Syn.shift t
      let k : PTm (n + 1) := var 0
      let Δ := le (succ k) (length A) :: padLaw A T k :: Γ.map Fm.shift
      have h : Δ ⊢[PRAAx] lt k (length A) := Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] padLaw A T k) (le_of_lt h)
      exact (prefixNorm_congr (.eqRefl _) (add_succ T k)).eqTrans
        ((prefix_succ _ _).eqTrans ((RationalAlgebra.add_congr ih
          (qL1_congr (pad_tail A T k h))).eqTrans (prefix_succ A k).eqSymm))
  have guarded : Γ ⊢[PRAAx] padLaw C t r := by
    simpa only [subst_padLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE r
  exact .impE guarded hr

theorem norm_padding (C t : PTm n) : Γ ⊢[PRAAx] coefficientNorm (leftPad C t) ≐ coefficientNorm C :=
  (norm_length _ _ (pad_length C t)).eqTrans (padding_prefix C t (length C) (le_refl _))

theorem norm_scaled (C z : PTm n) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (scaled C z)) (multiply (qL1 z) (coefficientNorm C)) := by
  have terms : Γ ⊢[PRAAx] RationalFiniteSum.termwiseLE normBody (RationalSumLinearity.scaledBody normBody)
      (length C) (scaled C z) (pairT (qL1 z) C) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (length (Syn.shift C)) :: Γ.map Fm.shift
    have left := qL1_congr (scaled_lookup (Γ := Δ) (Syn.shift C) (Syn.shift z) (var 0) Prf.hyp0)
    have right := RationalSumLinearity.scaled_term (Γ := Δ) normBody (var 0) (qL1 (Syn.shift z)) (Syn.shift C)
    simp only [norm_body_at] at right
    simpa only [Δ, Syn.shift, norm_body_at, GaussianRationalCoefficientScaling.subst_scaled,
      GaussianRationalL1.subst_qL1, subst_pairT, Foundations.SequenceComposition.subst_length] using
      rationalLE_congr left.eqSymm right.eqSymm (qL1_multiply _ _)
  exact rationalLE_congr (norm_length _ _ (scaled_length C z)).eqSymm
    (RationalSumLinearity.sum_homogeneous normBody _ _ _)
    (RationalFiniteSum.sum_monotone _ _ _ _ _ terms)

theorem norm_added (C D N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ N) (hD : Γ ⊢[PRAAx] length D ≐ N) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (added C D N)) (add (coefficientNorm C) (coefficientNorm D)) := by
  let E := GaussianCoefficientL1.addCoefficients C D N
  have entries : Γ ⊢[PRAAx] entriesEqual (added C D N) E N := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    simpa only [Δ, E, Syn.shift, GaussianRationalPolynomialBuffers.subst_added, GaussianCoefficientL1.subst_addCoefficients] using
      (added_lookup (Γ := Δ) (Syn.shift C) (Syn.shift D) (Syn.shift N) (var 0) Prf.hyp0).eqTrans
        (GaussianCoefficientL1.add_lookup _ _ _ _ Prf.hyp0).eqSymm
  exact rationalLE_congr (norm_entries _ _ _ (GaussianCoefficientL1.zip_length _ _ _ _) (added_length _ _ _)
    (by
      refine .allI (.impI ?_)
      exact (Prf.impE entries.allOpen.wk Prf.hyp0).eqSymm))
    (RationalAlgebra.add_congr (norm_length _ _ hC).eqSymm (norm_length _ _ hD).eqSymm)
    (GaussianCoefficientL1.coefficient_add C D N)

theorem actual_polynomial_padding_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coefficientNorm (leftPad (var 0) (var 1)) ≐ coefficientNorm (var 0)) :=
  closeUniv 2 (norm_padding _ _)
theorem actual_polynomial_append_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (coefficientNorm (appendZero (var 0)) ≐ coefficientNorm (var 0)) :=
  closeUniv 1 (norm_append _)
theorem actual_polynomial_scaled_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (coefficientNorm (scaled (var 0) (var 1)))
      (multiply (qL1 (var 1)) (coefficientNorm (var 0)))) :=
  closeUniv 2 (norm_scaled _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialNormBuffers
