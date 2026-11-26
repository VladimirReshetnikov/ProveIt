import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialBuffersGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProduct

/-!
# Actual original rational convolution and coefficient transport

Both truncation guards belong to the rational producer: a first-index
guard prevents spurious terms from truncated subtraction, and the second
factor is read through an actual entry-or-zero branch. Literal coefficient
embedding, rather than a supplied evaluation law, identifies the original
stored product with the Gaussian convolution of the embedded inputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialProductGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed scalarZero)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup coefficients_length embed_congr)
open RationalPolynomialBuffersGaussianEmbedding (padded padded_embedding)
open GaussianRationalPolynomialProduct (data stageData)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def contribution (P Q M k i : PTm n) : PTm n := RationalArithmetic.select
  (Signum.sg (monus (succ k) i)) scalarZero
  (RationalArithmetic.multiply (entry P i) (padded Q (succ M) (monus k i)))
def contributionBody : PTm 2 := contribution (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)
def coefficient (P Q M t k : PTm n) : PTm n := RationalFiniteSum.sum contributionBody t (data P Q M k)
def coefficientF : PR 5 := PTm.toPR (coefficient (var 0) (var 1) (var 2) (var 3) (var 4))
def stageBody : PTm 2 := PTm.app coefficientF ![fstT (var 1),fstT (sndT (var 1)),
  fstT (sndT (sndT (var 1))),sndT (sndT (sndT (var 1))),var 0]
def stage (P Q M t : PTm n) : PTm n := sequence stageBody (M+t) (stageData P Q M t)
def product (P Q N M : PTm n) : PTm n := stage P Q M (succ N)

ipra_subst contribution [Signum.sg]
ipra_subst coefficient
ipra_subst stage
ipra_subst product

theorem contribution_congr {P P' Q Q' M M' k k' i i' : PTm n}
    (hP : Γ ⊢[PRAAx] P ≐ P') (hQ : Γ ⊢[PRAAx] Q ≐ Q') (hM : Γ ⊢[PRAAx] M ≐ M')
    (hk : Γ ⊢[PRAAx] k ≐ k') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    contribution P Q M k i ≐ contribution P' Q' M' k' i' := by
  ipra_congr (contribution (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hP, hQ, hM, hk, hi]
theorem contribution_body_at (P Q M k i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term contributionBody i (data P Q M k) ≐ contribution P Q M k i := by
  simp only [RationalFiniteSum.term,contributionBody,inst2,subst_contribution,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) P (pairT Q (pairT M k))
  have f := (congrSnd e).eqTrans (snd_pair Q (pairT M k))
  exact contribution_congr (fst_pair _ _) e.fstE
    f.fstE f.sndE (.eqRefl _)
theorem contribution_inside (P Q M k i : PTm n) (hi : Γ ⊢[PRAAx] le i k) : Γ ⊢[PRAAx]
    contribution P Q M k i ≐ RationalArithmetic.multiply (entry P i) (padded Q (succ M) (monus k i)) :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans hi))
theorem contribution_outside (P Q M k i : PTm n) (hi : Γ ⊢[PRAAx] lt k i) : Γ ⊢[PRAAx]
    contribution P Q M k i ≐ scalarZero := RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hi)

theorem coefficient_zero (P Q M k : PTm n) : Γ ⊢[PRAAx] coefficient P Q M zero k ≐ scalarZero :=
  RationalGaussianRealPart.rational_sum_zero _ _
theorem coefficient_succ (P Q M t k : PTm n) : Γ ⊢[PRAAx]
    coefficient P Q M (succ t) k ≐ RationalArithmetic.add (coefficient P Q M t k) (contribution P Q M k t) :=
  (RationalFiniteSum.sum_succ _ _ _).eqTrans (RationalAlgebra.add_congr (.eqRefl _) (contribution_body_at P Q M k t))
theorem coefficient_well_formed (P Q M t k : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (coefficient P Q M t k) := RationalFiniteSum.sum_well_formed _ _ _

theorem coefficient_program (P Q M t k : PTm n) : Γ ⊢[PRAAx]
    PTm.app coefficientF ![P,Q,M,t,k] ≐ coefficient P Q M t k := by
  simpa [coefficientF] using toPR_eq (Γ := Γ)
    (coefficient (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![P,Q,M,t,k]
theorem stage_body_at (P Q M t k : PTm n) : Γ ⊢[PRAAx]
    inst2 stageBody k (stageData P Q M t) ≐ coefficient P Q M t k := by
  simp only [stageBody,inst2,ConciseIPRA.PTm.subst_app]
  have vector : (fun i => Syn.subst ![k,stageData P Q M t]
      ((![fstT (var 1),fstT (sndT (var 1)),fstT (sndT (sndT (var 1))),
        sndT (sndT (sndT (var 1))),var 0] : Fin 5 → PTm 2) i)) =
      ![fstT (stageData P Q M t),fstT (sndT (stageData P Q M t)),
        fstT (sndT (sndT (stageData P Q M t))),sndT (sndT (sndT (stageData P Q M t))),k] := by
    funext i
    fin_cases i <;> simp
  rw [vector]
  have e := snd_pair (Γ := Γ) P (pairT Q (pairT M t))
  have f := (congrSnd e).eqTrans (snd_pair Q (pairT M t))
  have h := congrApp (Γ := Γ) coefficientF
    (ts := ![fstT (stageData P Q M t),fstT (sndT (stageData P Q M t)),
      fstT (sndT (sndT (stageData P Q M t))),sndT (sndT (sndT (stageData P Q M t))),k]) (us := ![P,Q,M,t,k])
    (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact e.fstE
      · exact f.fstE
      · exact f.sndE
      · exact .eqRefl _)
  exact h.eqTrans (coefficient_program P Q M t k)
theorem stage_length (P Q M t : PTm n) : Γ ⊢[PRAAx] length (stage P Q M t) ≐ M+t := sequence_length _ _ _
theorem stage_lookup (P Q M t k : PTm n) (hk : Γ ⊢[PRAAx] lt k (M+t)) : Γ ⊢[PRAAx]
    entry (stage P Q M t) k ≐ coefficient P Q M t k := (sequence_decode stageBody hk).eqTrans (stage_body_at P Q M t k)
theorem product_length (P Q N M : PTm n) : Γ ⊢[PRAAx] length (product P Q N M) ≐ succ (N+M) :=
  (stage_length P Q M (succ N)).eqTrans (by ipra_ring)
theorem product_lookup (P Q N M k : PTm n) (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    entry (product P Q N M) k ≐ coefficient P Q M (succ N) k :=
  stage_lookup P Q M (succ N) k (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] succ (N+M) ≐ M+succ N)
    ((succ_monus_succ _ _).eqTrans hk))

theorem contribution_embedding (P Q N M k i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N)) : Γ ⊢[PRAAx]
    embed (contribution P Q M k i) ≐ GaussianRationalPolynomialProduct.contribution
      (coefficients P (succ N)) (coefficients Q (succ M)) M k i := by
  refine .orE (lt_or_le k i) ?_ ?_
  · exact (embed_congr (contribution_outside P Q M k i Prf.hyp0)).eqTrans
      (RationalGaussianEmbedding.embed_zero.eqTrans (GaussianRationalPolynomialProduct.contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm)
  · exact (embed_congr (contribution_inside P Q M k i Prf.hyp0)).eqTrans
      ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr (coefficient_lookup P _ i hi.wk).eqSymm (padded_embedding Q (succ M) (monus k i))).eqTrans
          (GaussianRationalPolynomialProduct.contribution_inside _ _ _ _ _ Prf.hyp0).eqSymm))

theorem coefficient_embedding (P Q N M t k : PTm n) (ht : Γ ⊢[PRAAx] le t (succ N)) : Γ ⊢[PRAAx]
    embed (coefficient P Q M t k) ≐ GaussianRationalPolynomialProduct.coefficient
      (coefficients P (succ N)) (coefficients Q (succ M)) M t k := by
  refine (RationalGaussianRealPart.embed_sum contributionBody t (data P Q M k)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ t _ _ ?_)
  have hts : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (succ (Syn.shift N)) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,Syn.shift] using ht.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift
  have lo := (embed_congr (contribution_body_at (Γ := Δ) (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0))).eqTrans
    (contribution_embedding (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift k) (var 0) (le_trans Prf.hyp0 hts.wk))
  have hi := GaussianRationalPolynomialProduct.contribution_body_at (Γ := Δ)
    (coefficients (Syn.shift P) (succ (Syn.shift N))) (coefficients (Syn.shift Q) (succ (Syn.shift M))) (Syn.shift M) (Syn.shift k) (var 0)
  simpa only [Δ,Syn.shift,RationalGaussianRealPart.embedBody,inst2,RationalGaussianEmbedding.subst_embed,RationalFiniteSum.term,
    GaussianRationalPolynomialProduct.subst_data,RationalPolynomialGaussianEmbedding.subst_coefficients,ConciseIPRA.PTm.subst_succ] using lo.eqTrans hi.eqSymm

theorem product_embedding (P Q N M k : PTm n) (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    embed (entry (product P Q N M) k) ≐ entry (GaussianRationalPolynomialProduct.product
      (coefficients P (succ N)) (coefficients Q (succ M)) N M) k :=
  (embed_congr (product_lookup P Q N M k hk)).eqTrans ((coefficient_embedding P Q N M (succ N) k (le_refl _)).eqTrans
    (GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _ hk).eqSymm)

theorem product_embedded_entries (P Q N M : PTm n) : Γ ⊢[PRAAx]
    RationalPolynomialBuffersGaussianEmbedding.embeddedEntries (product P Q N M)
      (GaussianRationalPolynomialProduct.product (coefficients P (succ N)) (coefficients Q (succ M)) N M) (succ (N+M)) := by
  refine .allI (.impI ?_)
  have bound : lt (var 0) (succ (Syn.shift N+Syn.shift M)) :: Γ.map Fm.shift ⊢[PRAAx]
      le (var 0) (Syn.shift N+Syn.shift M) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_product,GaussianRationalPolynomialProduct.subst_product,RationalPolynomialGaussianEmbedding.subst_coefficients,
    ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    product_embedding (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (var 0) bound

theorem product_evaluation (P Q N M z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    RationalPolynomialGaussianEmbedding.evaluate (product P Q N M) z ≐ RationalArithmetic.multiply
      (RationalPolynomialGaussianEmbedding.evaluate P z) (RationalPolynomialGaussianEmbedding.evaluate Q z) := by
  apply RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _
    (RationalPolynomialGaussianEmbedding.horner_canonical _ _ _) (RationalArithmetic.multiply_guard _ _)
  exact (RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ (succ (N+M)) z
    (product_length P Q N M) (GaussianRationalPolynomialProduct.product_length _ _ _ _) (product_embedded_entries P Q N M)).eqTrans
      ((GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _ (coefficients_length _ _) (coefficients_length _ _)).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr
          (RationalPolynomialBuffersGaussianEmbedding.evaluation_at_width P (succ N) z hP).eqSymm
          (RationalPolynomialBuffersGaussianEmbedding.evaluation_at_width Q (succ M) z hQ).eqSymm).eqTrans
            (RationalGaussianEmbedding.embed_multiply _ _).eqSymm))

theorem product_coefficient_well_formed (P Q N M k : PTm n) (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (entry (product P Q N M) k) :=
  RationalArithmetic.guard_congr (product_lookup P Q N M k hk) (coefficient_well_formed _ _ _ _ _)

def productF : PR 4 := PTm.toPR (product (var 0) (var 1) (var 2) (var 3))
def run (P Q N M : PTm n) : PTm n := PTm.app productF ![P,Q,N,M]
ipra_subst run
theorem program_at (P Q N M : PTm n) : Γ ⊢[PRAAx] run P Q N M ≐ product P Q N M := by
  simpa only [run,productF,subst_product,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (product (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,Q,N,M]
theorem returned_length (P Q N M : PTm n) : Γ ⊢[PRAAx] length (run P Q N M) ≐ succ (N+M) :=
  (congrFst (program_at P Q N M)).eqTrans (product_length P Q N M)
theorem returned_coefficient (P Q N M k : PTm n) (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    entry (run P Q N M) k ≐ coefficient P Q M (succ N) k :=
  (entry_congr (program_at P Q N M) (.eqRefl _)).eqTrans (product_lookup P Q N M k hk)
theorem returned_embedding (P Q N M k : PTm n) (hk : Γ ⊢[PRAAx] le k (N+M)) : Γ ⊢[PRAAx]
    embed (entry (run P Q N M) k) ≐ entry (GaussianRationalPolynomialProduct.product
      (coefficients P (succ N)) (coefficients Q (succ M)) N M) k :=
  (embed_congr (entry_congr (program_at P Q N M) (.eqRefl _))).eqTrans (product_embedding P Q N M k hk)

theorem actual_rational_convolution_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coefficient (var 0) (var 1) (var 2) (succ (var 3)) (var 4) ≐ RationalArithmetic.add
      (coefficient (var 0) (var 1) (var 2) (var 3) (var 4)) (contribution (var 0) (var 1) (var 2) (var 4) (var 3))) :=
  closeUniv 5 (coefficient_succ _ _ _ _ _)
theorem actual_rational_convolution_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 4) (succ (var 2)) ⟶ embed (coefficient (var 0) (var 1) (var 3) (var 4) (var 5)) ≐
      GaussianRationalPolynomialProduct.coefficient (coefficients (var 0) (succ (var 2)))
        (coefficients (var 1) (succ (var 3))) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (coefficient_embedding _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_product_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (run (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 2+var 3)) := closeUniv 4 (returned_length _ _ _ _)
theorem actual_rational_product_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2+var 3) ⟶ entry (run (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      coefficient (var 0) (var 1) (var 3) (succ (var 2)) (var 4)) := closeUniv 5 (.impI (returned_coefficient _ _ _ _ _ Prf.hyp0))
theorem actual_rational_product_coefficient_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2+var 3) ⟶ embed (entry (run (var 0) (var 1) (var 2) (var 3)) (var 4)) ≐
      entry (GaussianRationalPolynomialProduct.product (coefficients (var 0) (succ (var 2)))
        (coefficients (var 1) (succ (var 3))) (var 2) (var 3)) (var 4)) := closeUniv 5 (.impI (returned_embedding _ _ _ _ _ Prf.hyp0))
theorem actual_rational_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶
      RationalPolynomialGaussianEmbedding.evaluate (product (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ RationalArithmetic.multiply
        (RationalPolynomialGaussianEmbedding.evaluate (var 0) (var 4)) (RationalPolynomialGaussianEmbedding.evaluate (var 1) (var 4))) :=
  closeUniv 5 (.impI (.impI (product_evaluation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_product_well_formed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 2+var 3) ⟶ RationalNormalForm.wellFormed (entry (product (var 0) (var 1) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (product_coefficient_well_formed _ _ _ _ _ Prf.hyp0))
theorem actual_rational_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ product (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalPolynomialProductGaussianEmbedding
