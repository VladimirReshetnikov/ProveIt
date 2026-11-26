import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassFactors
import IPRADerivations.Analysis.Polynomials.Translation.GaussianInverseBinomialRows

/-!
# Original finite Gamma expressions respect native input values

Equality of decoded native Gaussian values gives literal equality of the
canonical fractions. Genuine QF inductions then follow the SAME original
Euler head and literal factor product. No raw native-code eta or supplied
factor/evaluator/output law is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteValueProperness

open_ipra
open GaussianRootAlgebra (equal)
open GaussianRationalHorner (ofGaussian canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianGammaWeierstrassFactors (localArgument literalPrefix)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_equal (z w D : PTm n) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    ofGaussian z D ≐ ofGaussian w D :=
  canonical_unique _ _ w D (GaussianRationalHorner.ofGaussian_canonical _ _ hD)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) h (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents _ _ hD))
    (GaussianRationalHorner.ofGaussian_represents _ _ hD)

theorem source_equal (z w R B : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source w R B :=
  .andI hz.andE₁ (.andI hz.andE₂.andE₁ (le_congr (GaussianRootAlgebra.normSq_equal h) (.eqRefl _) hz.andE₂.andE₂))

theorem head_factor_equal (i z w B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    GaussianGammaEulerHead.factor i z B ≐ GaussianGammaEulerHead.factor i w B :=
  qadd_congr (.eqRefl _) (fraction_equal z w _ (positive_product _ _ hB (zero_lt_succ i)) h)

def headLaw (z w B N : PTm n) : Fm PTm n := GaussianGammaEulerHead.head z B N ≐ GaussianGammaEulerHead.head w B N
ipra_subst headLaw

theorem head_zero (z w B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] headLaw z w B zero :=
  (GaussianGammaEulerHead.head_zero z B hB).eqTrans
    ((fraction_equal z w B hB h).eqTrans (GaussianGammaEulerHead.head_zero w B hB).eqSymm)
theorem head_step (z w B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w)
    (ih : Γ ⊢[PRAAx] headLaw z w B N) : Γ ⊢[PRAAx] headLaw z w B (succ N) :=
  (GaussianGammaEulerHead.head_succ z B N).eqTrans
    ((qmul_congr ih (head_factor_equal N z w B hB h)).eqTrans (GaussianGammaEulerHead.head_succ w B N).eqSymm)

theorem head_equal (z w B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] headLaw z w B N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] equal (Syn.shift z) (Syn.shift w) := by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (headLaw (Syn.shift z) (Syn.shift w) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using head_zero z w B hB h
    · simpa only [subst_headLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        head_step (Syn.shift z) (Syn.shift w) (Syn.shift B) (var 0) bs.wk hs.wk Prf.hyp0
  simpa only [subst_headLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem returned_head_equal (z w B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    GaussianGammaEulerHead.run z B N ≐ GaussianGammaEulerHead.run w B N :=
  (GaussianGammaEulerHead.program_at z B N).eqTrans ((head_equal z w B N hB h).eqTrans (GaussianGammaEulerHead.program_at w B N).eqSymm)

theorem local_argument_equal (i z w B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    localArgument i z B ≐ localArgument i w B :=
  GaussianInverseBinomialRows.negative_congr (fraction_equal z w _ (positive_product _ _ hB (zero_lt_succ i)) h)

theorem literal_factor_equal (i z w B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    GaussianGammaWeierstrassFactors.factor i z B K ≐ GaussianGammaWeierstrassFactors.factor i w B K :=
  qmul_congr (head_factor_equal i z w B hB h)
    (GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (local_argument_equal i z w B hB h))

def prefixLaw (z w B K N : PTm n) : Fm PTm n := literalPrefix z B K N ≐ literalPrefix w B K N
ipra_subst prefixLaw

theorem prefix_zero (z w B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] prefixLaw z w B K zero :=
  (GaussianGammaWeierstrassFactors.literal_zero z B K hB).eqTrans
    ((fraction_equal z w B hB h).eqTrans (GaussianGammaWeierstrassFactors.literal_zero w B K hB).eqSymm)
theorem prefix_step (z w B K N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w)
    (ih : Γ ⊢[PRAAx] prefixLaw z w B K N) : Γ ⊢[PRAAx] prefixLaw z w B K (succ N) :=
  (GaussianGammaWeierstrassFactors.literal_step z B K N).eqTrans
    ((qmul_congr ih (literal_factor_equal N z w B K hB h)).eqTrans (GaussianGammaWeierstrassFactors.literal_step w B K N).eqSymm)

theorem literal_prefix_equal (z w B K N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx] prefixLaw z w B K N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] equal (Syn.shift z) (Syn.shift w) := by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift z) (Syn.shift w) (Syn.shift B) (Syn.shift K) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero z w B K hB h
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_step (Syn.shift z) (Syn.shift w) (Syn.shift B) (Syn.shift K) (var 0) bs.wk hs.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N


/-- Both actual head and literal-prefix constructors are retained. -/
def output (z w B K N : PTm n) : PTm n := pairT (GaussianGammaEulerHead.head z B N)
  (pairT (GaussianGammaEulerHead.head w B N) (pairT (literalPrefix z B K N) (literalPrefix w B K N)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (z w B K N : PTm n) : PTm n := PTm.app outputF ![z,w,B,K,N]
ipra_subst output
ipra_subst run

theorem program_at (z w B K N : PTm n) : Γ ⊢[PRAAx] run z w B K N ≐ output z w B K N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,w,B,K,N]
theorem returned_head_left (z w B K N : PTm n) : Γ ⊢[PRAAx] fstT (run z w B K N) ≐ GaussianGammaEulerHead.head z B N :=
  (program_at z w B K N).fstE
theorem returned_head_right (z w B K N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run z w B K N)) ≐ GaussianGammaEulerHead.head w B N :=
  ((congrFst (congrSnd (program_at z w B K N))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_prefix_left (z w B K N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run z w B K N))) ≐ literalPrefix z B K N :=
  (((congrFst (congrSnd (congrSnd (program_at z w B K N)))).eqTrans (congrFst (congrSnd (snd_pair _ _)))).eqTrans
    (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_prefix_right (z w B K N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run z w B K N))) ≐ literalPrefix w B K N :=
  (((congrSnd (congrSnd (congrSnd (program_at z w B K N)))).eqTrans (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_equalities (z w B K N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] equal z w) : Γ ⊢[PRAAx]
    (fstT (run z w B K N) ≐ fstT (sndT (run z w B K N))) ⋏
      (fstT (sndT (sndT (run z w B K N))) ≐ sndT (sndT (sndT (run z w B K N)))) :=
  .andI ((returned_head_left z w B K N).eqTrans ((head_equal z w B N hB h).eqTrans (returned_head_right z w B K N).eqSymm))
    ((returned_prefix_left z w B K N).eqTrans ((literal_prefix_equal z w B K N hB h).eqTrans (returned_prefix_right z w B K N).eqSymm))

theorem original_canonical_fraction_native_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ equal (var 0) (var 1) ⟶ ofGaussian (var 0) (var 2) ≐ ofGaussian (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (fraction_equal _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_Gamma_disk_native_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalExponent.source (var 0) (var 2) (var 3) ⟶ equal (var 0) (var 1) ⟶
      GaussianGammaCanonicalExponent.source (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (source_equal _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_Euler_head_native_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ equal (var 0) (var 1) ⟶ headLaw (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (head_equal _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_Weierstrass_factor_native_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ equal (var 1) (var 2) ⟶
      GaussianGammaWeierstrassFactors.factor (var 0) (var 1) (var 3) (var 4) ≐
        GaussianGammaWeierstrassFactors.factor (var 0) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (literal_factor_equal _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_literal_prefix_native_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ equal (var 0) (var 1) ⟶ prefixLaw (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (literal_prefix_equal _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_native_input_equalities_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ equal (var 0) (var 1) ⟶
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ⋏
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))) :=
  closeUniv 5 (.impI (.impI (returned_equalities _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteValueProperness
