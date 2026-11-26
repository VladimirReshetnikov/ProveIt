import IPRADerivations.Analysis.Polynomials.Evaluation.RationalPolynomialNonvanishing
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProductDegree

/-!
# The original rational leading coefficient after a successful scan

The selected original coefficient is normalized in the original rational
representation. The successful first index and its Gaussian counterpart
agree, so their actual normalized leading coefficients embed exactly.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialLeadingGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed)
open RationalPolynomialDegreeGaussianEmbedding (first flag)
open RationalPolynomialBuffersGaussianEmbedding (embeddedEntries)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leading (C N : PTm n) : PTm n := RationalArithmetic.recode (entry C (first C N))

ipra_subst leading

theorem leading_canonical (C N : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (leading C N) :=
  RationalArithmetic.recode_guard _

theorem coefficient_list_embedding (C N : PTm n) :
    Γ ⊢[PRAAx] embeddedEntries C (coefficients C N) N := by
  refine .allI (.impI ?_)
  simpa [Syn.shift] using (coefficient_lookup (Syn.shift C) (Syn.shift N) (var 0) Prf.hyp0).eqSymm

theorem leading_embedding (C D N : PTm n) (h : Γ ⊢[PRAAx] embeddedEntries C D (succ N))
    (hf : Γ ⊢[PRAAx] flag C N ≐ one) : Γ ⊢[PRAAx]
    embed (leading C N) ≐ GaussianRationalPolynomialProductDegree.leading D N := by
  let i := first C N
  let j := GaussianRationalPolynomialDegree.first D N
  have hi := RationalPolynomialNonvanishing.found_of_flag C N hf
  have same := RationalPolynomialDegreeGaussianEmbedding.first_conjugacy C D N h
  have stored := RationalPolynomialDegreeGaussianEmbedding.bounded_entry C D N i h hi
  have aligned : Γ ⊢[PRAAx] recode (entry D j) ≐ embed (entry C i) :=
    (recode_congr (entry_congr (.eqRefl D) same.eqSymm)).eqTrans
      ((recode_congr stored.eqSymm).eqTrans (recode_eq _ (RationalGaussianEmbedding.embed_canonical _)))
  exact ((RationalGaussianEmbedding.embed_eq_iff (leading C N) (entry C i)).iffMpr
    (RationalArithmetic.recode_equal _)).eqTrans aligned.eqSymm

theorem actual_rational_leading_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (embeddedEntries (var 0) (var 1) (succ (var 2)) ⟶ flag (var 0) (var 2) ≐ one ⟶
      embed (leading (var 0) (var 2)) ≐ GaussianRationalPolynomialProductDegree.leading (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (leading_embedding _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalPolynomialLeadingGaussianEmbedding
