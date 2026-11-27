import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariatePowerExpansion
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalBlockSums
import IPRADerivations.Analysis.Inequalities.WeightedComparison.GaussianWeightedMonomialBasis

/-!
# The original bivariate power sum on one numerical interval

The unfiltered sum uses the same quotient and remainder labels as the
weighted monomial basis. Distributivity and the actual block sum identify
it with the original bivariate evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBivariateFlatSum

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBivariatePowerExpansion (bivariateSum rowBody row_body_at data)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion (values rowShape)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (slot)
open LeanProofs.IPRA.Analysis.GaussianRationalBlockSums (blockBody block_body_at sum_blocks)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum sum_index_congr sum_multiply multiplyBody multiply_body_at)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerAlgebra (qmul_commutative)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerExpansion (termBody term_body_at)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianReciprocalHorner (qmul_associative)
open LeanProofs.IPRA.Analysis.GaussianWeightedMonomialBasis (stride label horizon decodeY decodeX decode_label)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def monomialTerm (G m a x y i j : PTm n) : PTm n :=
  qmul (entry (entry G (slot m i)) (monus a j)) (qmul (power x j) (power y i))

def flatTerm (G m a x y h : PTm n) : PTm n := monomialTerm G m a x y (decodeY a h) (decodeX a h)

def flatBody : PTm 2 := flatTerm (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
  (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) (var 0)

def flatSum (G m a x y : PTm n) : PTm n := sum flatBody (horizon m a) (data G m a x y)

ipra_subst flatTerm [monomialTerm]

private theorem flat_congr {G G' m m' a a' x x' y y' h h' : PTm n}
    (hG : Γ ⊢[PRAAx] G ≐ G') (hm : Γ ⊢[PRAAx] m ≐ m') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') (hh : Γ ⊢[PRAAx] h ≐ h') :
    Γ ⊢[PRAAx] flatTerm G m a x y h ≐ flatTerm G' m' a' x' y' h' := by
  ipra_congr (flatTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with [hG, hm, ha, hx, hy, hh]

theorem flat_body_at (G m a x y h : PTm n) : Γ ⊢[PRAAx] inst2 flatBody h (data G m a x y) ≐ flatTerm G m a x y h := by
  have tail := snd_pair (Γ := Γ) G (pairT m (pairT a (pairT x y)))
  have second := (congrSnd tail).eqTrans (snd_pair m (pairT a (pairT x y)))
  have third := (congrSnd second).eqTrans (snd_pair a (pairT x y))
  simp only [flatBody,inst2,subst_flatTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact flat_congr (fst_pair _ _) tail.fstE
    second.fstE third.fstE
    third.sndE (.eqRefl _)

theorem flat_label_term (G m a x y i j : PTm n) (hj : Γ ⊢[PRAAx] le j a) : Γ ⊢[PRAAx]
    flatTerm G m a x y (label a i j) ≐ monomialTerm G m a x y i j := by
  have decoded := decode_label a i j hj
  have ySlot := congrMonus (.eqRefl m) (congrSucc (Prf.andE₁ decoded))
  have xSlot := congrMonus (.eqRefl a) (Prf.andE₂ decoded)
  exact qmul_congr (entry_congr (entry_congr (.eqRefl G) ySlot) xSlot)
    (qmul_congr (congrAp2 powerF (Prf.andE₂ decoded) (.eqRefl x)) (congrAp2 powerF (Prf.andE₁ decoded) (.eqRefl y)))

theorem multiplied_term (G m a x y i j : PTm n) : Γ ⊢[PRAAx]
    inst2 (multiplyBody termBody) j (pairT (power y i) (GaussianRationalPowerExpansion.data (entry G (slot m i)) a x)) ≐
      monomialTerm G m a x y i j := by
  have read := multiply_body_at (Γ := Γ) termBody (power y i) j (GaussianRationalPowerExpansion.data (entry G (slot m i)) a x)
  have oneTerm := term_body_at (Γ := Γ) (entry G (slot m i)) a x j
  exact read.eqTrans ((qmul_congr (.eqRefl _) oneTerm).eqTrans
    ((qmul_commutative _ _).eqTrans (qmul_associative _ _ _)))

theorem offset_term (G m a x y i j : PTm n) (hj : Γ ⊢[PRAAx] lt j (stride a)) : Γ ⊢[PRAAx]
    inst2 (offB flatBody) j (pairT (stride a*i) (data G m a x y)) ≐ monomialTerm G m a x y i j := by
  rw [inst2_offB]
  have offset := congrAdd (fst_pair (Γ := Γ) (stride a*i) (data G m a x y)) (.eqRefl j)
  have read := congrInst2 flatBody (offset.eqTrans (congrAdd (mul_comm _ _) (.eqRefl j)))
    (snd_pair (stride a*i) (data G m a x y))
  exact read.eqTrans ((flat_body_at G m a x y (label a i j)).eqTrans
    (flat_label_term G m a x y i j ((succ_monus_succ _ _).eqSymm.eqTrans hj)))

theorem same_block (G m a x y i : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody i (data G m a x y) ≐ inst2 (blockBody flatBody) i (pairT (stride a) (data G m a x y)) := by
  have rowTerm := row_body_at (Γ := Γ) G m a x y i
  have blockTerm := block_body_at (Γ := Γ) flatBody (stride a) i (data G m a x y)
  refine rowTerm.eqTrans ((qmul_commutative _ _).eqTrans ((sum_multiply termBody (power y i) (stride a)
    (GaussianRationalPowerExpansion.data (entry G (slot m i)) a x)).eqSymm.eqTrans (?_ : Γ ⊢[PRAAx] _ ≐ _)))
  refine (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ ?_).eqTrans blockTerm.eqSymm
  refine .allI (.impI ?_)
  simpa [Syn.shift] using (multiplied_term (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift x) (Syn.shift y)
    (Syn.shift i) (var 0)).eqTrans
      (offset_term (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift x) (Syn.shift y) (Syn.shift i) (var 0) Prf.hyp0).eqSymm

theorem flat_expansion (G m a x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hG : Γ ⊢[PRAAx] rowShape G m a) :
    Γ ⊢[PRAAx] evaluate (values G m x) y ≐ flatSum G m a x y := by
  have same : Γ ⊢[PRAAx] bivariateSum G m a x y ≐ GaussianRationalBlockSums.blockTotal flatBody (stride a) m (data G m a x y) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simpa [Syn.shift] using same_block (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift x) (Syn.shift y) (var 0)
  exact (GaussianBivariatePowerExpansion.bivariate_expansion G m a x y hm hG).eqTrans
    (same.eqTrans ((sum_blocks flatBody (stride a) m (data G m a x y)).eqSymm.eqTrans
      (sum_index_congr flatBody (mul_comm _ _) (.eqRefl _))))

theorem actual_flat_bivariate_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ rowShape (var 0) (var 1) (var 2) ⟶
      evaluate (values (var 0) (var 1) (var 3)) (var 4) ≐ flatSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (flat_expansion _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBivariateFlatSum
