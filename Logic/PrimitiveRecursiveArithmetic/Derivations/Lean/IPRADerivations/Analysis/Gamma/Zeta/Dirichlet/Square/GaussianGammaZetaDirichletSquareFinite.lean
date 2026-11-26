import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.Square.GaussianGammaZetaDirichletSquareRow
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinDampedImproper
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetBaselBinding
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameConjugation
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactZeroWidth

/-!
# Common finite Dirichlet and Basel sums

At every internal cutoff the original finite Dirichlet name at two
represents the literal rational sum used by the Basel proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletSquareFinite

open_ipra
open GaussianBinetBaselBinding (literalSum)
open GaussianEulerPositiveScalingConstant (inverseF)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaZetaDirichletSquareRow (nativeTwo squareData original_square_row)
open GaussianGammaZetaMellinDampedImproper (parameters dirichletBody dirichletF dirichlet_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameConjugation (pointwiseEqual equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedFiniteProductFamily (regularRows)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qadd_congr)
open RationalGaussianEmbedding (embed embed_add embed_at embedF)
open RationalReciprocalPowerTail (reciprocalPower reciprocal_congr tail tail_zero tail_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def squareBody : PTm 2 := squareData (succ (var 0))

@[simp] private theorem inst2_squareBody (i x : PTm n) :
    inst2 squareBody i x = squareData (succ i) := by simp [inst2,squareBody]

private theorem embed_congr {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] embed x ≐ embed y :=
  (embed_at x).eqSymm.eqTrans ((congrAp1 embedF e).eqTrans (embed_at y))

private theorem literal_zero : Γ ⊢[PRAAx] literalSum (zero : PTm n) ≐ GaussianRationalHorner.qzero :=
  (embed_congr (tail_zero two zero)).eqTrans
    ((GaussianEulerDecayOrder.fraction_embedding zero one (le_refl one)).eqTrans
      (GaussianCompactZeroWidth.zero_fraction one (le_refl one)))

private theorem literal_succ (m : PTm n) : Γ ⊢[PRAAx]
    literalSum (succ m) ≐ qadd (literalSum m) (squareData (succ m)) := by
  have next := reciprocal_congr (Γ := Γ) (.eqRefl (two : PTm n)) (congrSucc (zero_add m))
  exact (embed_congr ((tail_succ two zero m).eqTrans (RationalAlgebra.add_congr (.eqRefl _) next))).eqTrans
    (embed_add (tail two zero m) (reciprocalPower two (succ m)))

private def readbackLaw (m : PTm n) : Fm PTm n :=
  GaussianRationalFiniteSum.sum squareBody m zero ≐ literalSum m

@[simp] private theorem subst_readbackLaw {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    (readbackLaw m).subst σ = readbackLaw (Syn.subst σ m) := by simp [readbackLaw]

private theorem literal_readback (m : PTm n) : Γ ⊢[PRAAx] readbackLaw m := by
  have hall : Γ ⊢[PRAAx] .all (readbackLaw (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_readbackLaw,Syn.subst_var,Syn.inst_zero]
      exact (GaussianRationalFiniteSum.sum_zero squareBody zero).eqTrans literal_zero.eqSymm
    · simp only [subst_readbackLaw,Syn.subst_var,Syn.repl_zero]
      have previous : readbackLaw (var 0) :: Γ.map Fm.shift ⊢[PRAAx] readbackLaw (var 0) := Prf.hyp0
      exact (GaussianRationalFiniteSum.sum_succ squareBody (var 0) zero).eqTrans (by
        rw [inst2_squareBody]
        exact (qadd_congr previous (.eqRefl _)).eqTrans (literal_succ (var 0)).eqSymm)
  simpa only [subst_readbackLaw,Syn.subst_var,Syn.inst_zero] using hall.allE m

private theorem constant_sample (p N : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianNamedFiniteSumFamily.nameF constantF squareBody) p
      (GaussianNamedFiniteSumFamily.data N zero) ≐ literalSum N := by
  let k := GaussianFastValueCut.exponent N p
  have e : Γ ⊢[PRAAx] GaussianNamedFiniteSumFamily.finite constantF squareBody k N zero ≐
      GaussianRationalFiniteSum.sum squareBody N zero := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
      (GaussianNamedFiniteSumFamily.body constantF squareBody) squareBody N (pairT k zero) zero
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_pairT,PTm.subst_zero] using
      (GaussianNamedFiniteSumFamily.term_at constantF squareBody (var 0) (Syn.shift k) zero).eqTrans
        (constant_at (Syn.shift k) (inst2 squareBody (var 0) zero))
  exact (GaussianNamedFiniteSumFamily.sample_at constantF squareBody p N zero).eqTrans
    (e.eqTrans (literal_readback N))

private theorem constant_sum_cross (N : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedFiniteSumFamily.nameF constantF squareBody) constantF
      (GaussianNamedFiniteSumFamily.data N zero) (literalSum N) := by
  have rows : Γ ⊢[PRAAx] regularRows constantF squareBody N zero :=
    .allI (.impI (constant_regular _))
  apply equal_samples_cross _ _ _ _
    (GaussianNamedFiniteSumFamily.regular _ _ _ _ rows) (constant_regular _)
  refine .allI ?_
  simpa only [pointwiseEqual,Syn.shift,GaussianNamedFiniteSumFamily.subst_data,PTm.subst_zero,
    GaussianBinetBaselBinding.subst_literalSum] using
    (constant_sample (var 0) (Syn.shift N)).eqTrans (constant_at (var 0) (literalSum (Syn.shift N))).eqSymm

private theorem original_square_rows (N R A : PTm n) : Γ ⊢[PRAAx]
    equalRows inverseF constantF dirichletBody squareBody N (parameters nativeTwo R one A) zero := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have row := original_square_row (Γ := Δ) (succ (var 0)) (zero_lt_succ _)
  simpa only [Syn.shift,Δ,GaussianGammaZetaMellinDampedImproper.subst_parameters,
    GaussianGammaZetaDirichletSquareRow.subst_nativeTwo,one,PTm.subst_succ,PTm.subst_zero,
    inst2_squareBody] using
    cross_data_congr inverseF constantF _ _ _ _
      (dirichlet_at (var 0) nativeTwo (Syn.shift R) one (Syn.shift A)).eqSymm (.eqRefl _) row

theorem original_finite_square (N R A : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent dirichletF constantF (GaussianGammaZetaMellinDampedImproper.data N nativeTwo R one A)
      (literalSum N) :=
  cross_trans dirichletF (GaussianNamedFiniteSumFamily.nameF constantF squareBody) constantF _ _ _
    (GaussianNamedFiniteSumFamilyCongruence.family_sum_cross _ _ _ _ _ _ _ (original_square_rows N R A))
    (constant_sum_cross N)

theorem actual_original_finite_Dirichlet_square_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (crossEquivalent dirichletF constantF
        (GaussianGammaZetaMellinDampedImproper.data (var 0) nativeTwo (var 1) one (var 2))
        (literalSum (var 0))) :=
  closeUniv 3 (original_finite_square _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletSquareFinite
