import IPRADerivations.Analysis.Polynomials.Annihilators.GaussianAnnihilatorPolynomial
import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialConstantInjectionGaussianEmbedding
import IPRADerivations.Core.CongruenceTactic

/-!
# Original rational weighted annihilator polynomial

The numerical basis and its retained ranks are shared. At each stored
position the compiler reads the corresponding original rational coefficient,
recodes it canonically, and stores the original scalar zero off the basis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalAnnihilatorPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianWeightedMonomialBasis (count keep label position)
open GaussianAnnihilatorPolynomial (data fields subst_fields fields_at)
open GaussianPolynomialMultiplicationMatrix (slot)
open GaussianPolynomialMonicCompanion (rowShape)
open GaussianPolynomialDeterminantTerms (cell subst_cell)
open RationalGaussianEmbedding (embed scalarZero)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup embed_congr)
open RationalPolynomialMonicCompanionGaussianEmbedding (rowsEmbedded)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open GaussianRationalFiberVandermonde (table table_length table_row_length table_lookup)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (a m e L i j : PTm n) : PTm n := RationalArithmetic.select (keep m e L (label L i j))
  scalarZero (RationalArithmetic.recode (entry a (position m e L i j)))

def body : PTm 3 := coefficient (fields (var 2) 0) (fields (var 2) 1) (fields (var 2) 2) (fields (var 2) 3)
  (slot (fields (var 2) 1) (var 0)) (monus (fields (var 2) 3) (var 1))

def polynomial (a m e L : PTm n) : PTm n := table body m (succ L) (data a m e L)

@[simp] theorem subst_coefficient {q : ℕ} (σ : Fin n → PTm q) (a m e L i j : PTm n) :
    Syn.subst σ (coefficient a m e L i j) = coefficient (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ e)
      (Syn.subst σ L) (Syn.subst σ i) (Syn.subst σ j) := by simp [coefficient,RationalArithmetic.recode]

@[simp] theorem subst_polynomial {q : ℕ} (σ : Fin n → PTm q) (a m e L : PTm n) :
    Syn.subst σ (polynomial a m e L) = polynomial (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) := by
  simp [polynomial]

private theorem coefficient_congr {a a' m m' e e' L L' i i' j j' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hm : Γ ⊢[PRAAx] m ≐ m') (he : Γ ⊢[PRAAx] e ≐ e')
    (hL : Γ ⊢[PRAAx] L ≐ L') (hi : Γ ⊢[PRAAx] i ≐ i') (hj : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] coefficient a m e L i j ≐ coefficient a' m' e' L' i' j' := by
  ipra_congr (coefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [ha, hm, he, hL, hi, hj] using [GaussianAnnihilatorPolynomial.val_five]

theorem polynomial_length (a m e L : PTm n) : Γ ⊢[PRAAx] length (polynomial a m e L) ≐ m :=
  table_length body m (succ L) (data a m e L)

theorem polynomial_shape (a m e L : PTm n) : Γ ⊢[PRAAx] rowShape (polynomial a m e L) m L := by
  refine .allI (.impI ?_)
  simpa [polynomial,Syn.shift] using table_row_length (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
    body (Syn.shift m) (succ (Syn.shift L)) (data (Syn.shift a) (Syn.shift m) (Syn.shift e) (Syn.shift L)) (var 0) Prf.hyp0

theorem stored_coefficient (a m e L r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] lt s (succ L)) :
    Γ ⊢[PRAAx] cell (polynomial a m e L) r s ≐ coefficient a m e L (slot m r) (monus L s) := by
  refine (table_lookup body m (succ L) (data a m e L) r s hr hs).eqTrans ?_
  have f j := fields_at (Γ := Γ) a m e L j
  simpa only [body,subst_coefficient,subst_fields,GaussianPolynomialMultiplicationMatrix.subst_slot,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    LeanProofs.IPRA.PTm.subst_monus,ConciseIPRA.PTm.subst_succ,slot] using
    coefficient_congr (f 0) (f 1) (f 2) (f 3) (congrMonus (f 1) (.eqRefl (succ r))) (congrMonus (f 3) (.eqRefl s))

theorem coefficient_embedding (a m e L i j : PTm n) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] le j L) :
    Γ ⊢[PRAAx] embed (coefficient a m e L i j) ≐
      GaussianAnnihilatorPolynomial.coefficient (coefficients a (count m e L)) m e L i j := by
  let bit := keep m e L (label L i j)
  let p := position m e L i j
  let a' := coefficients a (count m e L)
  refine .orE (eq_or_ne bit zero) ?_ ?_
  · exact (embed_congr (RationalArithmetic.select_zero _ _ _ Prf.hyp0)).eqTrans
      (RationalGaussianEmbedding.embed_zero.eqTrans (GaussianAnnihilatorPolynomial.coefficient_rejected a' m e L i j Prf.hyp0).eqSymm)
  · have hWeight := GaussianWeightedMonomialBasis.keep_bound (Γ := neg (bit ≐ zero) :: Γ) m e L (label L i j) Prf.hyp0
    have decoded := GaussianWeightedMonomialBasis.decode_label (Γ := neg (bit ≐ zero) :: Γ) L i j hj.wk
    have he := congrAdd (congrMul (.eqRefl m) (.andE₂ decoded)) (congrMul (.eqRefl e) (.andE₁ decoded))
    have hAd : neg (bit ≐ zero) :: Γ ⊢[PRAAx] GaussianWeightedMonomialBasis.admissible m e L i j :=
      .andI hi.wk (le_congr he (.eqRefl L) hWeight)
    have hRank := Prf.andE₁ (GaussianWeightedMonomialBasis.listed_label _ _ _ _ _ hAd)
    have hx := (GaussianTranslatedNonconstant.recode_congr (coefficient_lookup a (count m e L) p hRank)).eqTrans
      (GaussianTranslatedNonconstant.recode_eq _ (RationalGaussianEmbedding.embed_canonical _))
    have hs := RationalArithmetic.select_one bit scalarZero (RationalArithmetic.recode (entry a p))
      (GaussianWeightedMonomialBasis.label_keep _ _ _ _ _ hAd)
    exact (embed_congr hs).eqTrans ((RationalGaussianEmbedding.embed_recode _).eqTrans (hx.eqSymm.eqTrans
      (GaussianAnnihilatorPolynomial.coefficient_kept _ _ _ _ _ _ hAd).eqSymm))

theorem stored_embedding (a m e L r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] lt s (succ L)) :
    Γ ⊢[PRAAx] embed (cell (polynomial a m e L) r s) ≐
      cell (GaussianAnnihilatorPolynomial.polynomial (coefficients a (count m e L)) m e L) r s := by
  let a' := coefficients a (count m e L)
  have leSlot := (succ_monus_succ s L).eqSymm.eqTrans hs
  have stored := (entry_congr (GaussianAnnihilatorPolynomial.outer_lookup a' m e L r hr) (.eqRefl s)).eqTrans
    (GaussianAnnihilatorPolynomial.row_lookup a' m e L (slot m r) s leSlot)
  exact (embed_congr (stored_coefficient _ _ _ _ _ _ hr hs)).eqTrans
    ((coefficient_embedding _ _ _ _ _ _ (GaussianPolynomialMultiplicationMatrix.slot_range m r hr)
      (GaussianRationalMonicReconstruction.monus_le_left L s)).eqTrans stored.eqSymm)

theorem coefficient_canonical (a m e L i j : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (coefficient a m e L i j) := by
  let bit := keep m e L (label L i j)
  let c := RationalArithmetic.recode (entry a (position m e L i j))
  refine .orE (eq_or_ne bit zero) ?_ ?_
  · exact RationalArithmetic.guard_congr (RationalArithmetic.select_zero bit scalarZero c Prf.hyp0)
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
  · have hw := GaussianWeightedMonomialBasis.keep_bound (Γ := neg (bit ≐ zero) :: Γ) m e L (label L i j) Prf.hyp0
    exact RationalArithmetic.guard_congr
      (RationalArithmetic.select_one bit scalarZero c (GaussianWeightedMonomialBasis.keep_one _ _ _ _ hw))
        (RationalArithmetic.recode_guard _)

theorem stored_canonical (a m e L r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] lt s (succ L)) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (cell (polynomial a m e L) r s) :=
  RationalArithmetic.guard_congr (stored_coefficient _ _ _ _ _ _ hr hs) (coefficient_canonical _ _ _ _ _ _)

theorem rows_embedding (a m e L : PTm n) : Γ ⊢[PRAAx]
    rowsEmbedded (polynomial a m e L) (GaussianAnnihilatorPolynomial.polynomial (coefficients a (count m e L)) m e L) m L := by
  refine .allI (.impI (.allI (.impI ?_)))
  let r := Syn.shift (var 0 : PTm (n + 1))
  let Δ := lt (var 0) (Syn.shift (succ (Syn.shift L))) ::
    (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift).map Fm.shift
  have hr : Δ ⊢[PRAAx] lt r (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,r,List.map_cons,Fm.shift,subst_lt,Syn.shift,Syn.subst_var] using (Prf.hyp1 : Δ ⊢[PRAAx] _)
  have hs : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift (Syn.shift L))) := by
    simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
  simpa only [Δ,r,Syn.shift,subst_polynomial,GaussianAnnihilatorPolynomial.subst_polynomial,
    RationalPolynomialGaussianEmbedding.subst_coefficients,GaussianWeightedMonomialBasis.subst_count,
    RationalGaussianEmbedding.subst_embed,subst_cell,cell,subst_entry,Syn.subst_var,ConciseIPRA.PTm.subst_succ] using
    stored_embedding (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift L)) r (var 0) hr hs

theorem evaluation_embedding (a m e L x y : PTm n) : Γ ⊢[PRAAx]
    embed (RationalBivariateGaussianEmbedding.bivariate (polynomial a m e L) m x y) ≐
      GaussianRationalHorner.evaluate
        (GaussianPolynomialMonicCompanion.values (GaussianAnnihilatorPolynomial.polynomial (coefficients a (count m e L)) m e L) m (embed x))
        (embed y) :=
  RationalPolynomialConstantInjectionGaussianEmbedding.bivariate_transport _ _ m L x y
    (polynomial_shape a m e L) (GaussianAnnihilatorPolynomial.polynomial_shape _ _ _ _) (rows_embedding a m e L)

def polynomialF : PR 4 := PTm.toPR (polynomial (var 0) (var 1) (var 2) (var 3))

theorem polynomial_at (a m e L : PTm n) : Γ ⊢[PRAAx] app polynomialF ![a,m,e,L] ≐ polynomial a m e L := by
  simpa [polynomialF] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) (var 2) (var 3) : PTm 4) ![a,m,e,L]

theorem actual_rational_annihilator_polynomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (polynomial (var 0) (var 1) (var 2) (var 3)) ≐ var 1 ⋏
      rowShape (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3)) :=
  closeUniv 4 (.andI (polynomial_length _ _ _ _) (polynomial_shape _ _ _ _))

theorem actual_rational_annihilator_polynomial_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rowsEmbedded (polynomial (var 0) (var 1) (var 2) (var 3))
      (GaussianAnnihilatorPolynomial.polynomial (coefficients (var 0) (count (var 1) (var 2) (var 3)))
        (var 1) (var 2) (var 3)) (var 1) (var 3)) := closeUniv 4 (rows_embedding _ _ _ _)

theorem actual_rational_annihilator_polynomial_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (app polynomialF ![var 0,var 1,var 2,var 3] ≐ polynomial (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (polynomial_at _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalAnnihilatorPolynomial
