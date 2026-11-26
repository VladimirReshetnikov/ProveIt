import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelGridComparison
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelRefinement
import IPRADerivations.AnalyticNumberTheory.WeightedMangoldt

/-!
# Zero extension of the actual beta row at the degree

The original row is retained on its support. The same evaluator returns
the canonical Gaussian zero outside its support, including the exact
degree endpoint for positive degree. This allows one contiguous tail
interval without adding two copies of its decay bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaZeroExtension

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelGridComparison (row sampleDataBeta)
open GaussianBetaKernelExponential (kernel)
open GaussianRationalHorner (qzero positive_product)
open RationalArithmetic (select select_one select_zero)
open GaussianRationalMonicReconstruction (select_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def evaluatorTerm (p t x : PTm n) : PTm n :=
  select (eqb (monus (fstT t) (sndT t*sndT x)) zero) qzero
    (ap3 GaussianBetaKernelGridComparison.evaluatorF p t x)

def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))

theorem evaluator_at (p t x : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
  change Γ ⊢[PRAAx] PTm.app evaluatorF ![p,t,x] ≐ evaluatorTerm p t x
  simpa only [evaluatorF,evaluatorTerm,RationalArithmetic.subst_select,subst_eqb,PTm.subst_monus,subst_fstT,subst_sndT,
    PTm.subst_mul,PTm.subst_zero,GaussianRationalHorner.subst_qzero,subst_ap3,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem row_at (p z B a b N : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p (pairT a b) (sampleDataBeta z B N) ≐
      select (eqb (monus a (b*N)) zero) qzero (row p z B a b N) := by
  let t := pairT a b
  let x := sampleDataBeta z B N
  have degree : Γ ⊢[PRAAx] sndT x ≐ N := snd_pair _ _
  have guard := AnalyticNumberTheory.Euler.congrEqb
    (congrMonus (fst_pair (Γ := Γ) a b) (congrMul (snd_pair a b) degree)) (.eqRefl zero)
  exact (evaluator_at p t x).eqTrans
    (select_congr guard (.eqRefl _) (GaussianBetaKernelGridComparison.row_at p z B a b N))

theorem row_at_supported (p z B a b N : PTm n) (h : Γ ⊢[PRAAx] le a (b*N)) :
    Γ ⊢[PRAAx] ap3 evaluatorF p (pairT a b) (sampleDataBeta z B N) ≐ row p z B a b N :=
  (row_at p z B a b N).eqTrans (select_one _ _ _ (AnalyticNumberTheory.WeightedMangoldt.eqb_one_le h))

theorem row_at_exterior (p z B a b N : PTm n) (h : Γ ⊢[PRAAx] lt (b*N) a) :
    Γ ⊢[PRAAx] ap3 evaluatorF p (pairT a b) (sampleDataBeta z B N) ≐ qzero :=
  (row_at p z B a b N).eqTrans (select_zero _ _ _ (AnalyticNumberTheory.WeightedMangoldt.eqb_zero_lt h))

theorem original_endpoint_zero (p z B b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] row p z B (b*N) b N ≐ qzero := by
  let D := b*N
  let F := pw D N
  let v := GaussianBetaKernelRefinement.value D b N
  let o : PTm n := RationalGaussianEmbedding.scalarZero
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hb hN
  have hF : Γ ⊢[PRAAx] le one F := RationalNonnegativePowers.denominator_positive _ _ hD
  have ne := GaussianCompactRiemannName.positive_as_successor N hN
  have vanish : Γ ⊢[PRAAx] pw (monus D D) N ≐ zero :=
    (congrAp2 powF ne (monus_self D)).eqTrans ((pw_succ zero _).eqTrans (mul_zero _))
  have numer : Γ ⊢[PRAAx] RationalArithmetic.represents v (ZT.ofNat zero) F :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simpa only [ZT.toZ_ofNat] using natEq vanish) (.eqRefl _)
      (RationalNonnegativePowers.power_represents _ _ _ hD)
  have val : Γ ⊢[PRAAx] v ≐ o :=
    RationalFiniteSum.canonical_equal v o (ZT.ofNat zero) (ZT.ofNat zero) F F
      (RationalNonnegativePowers.power_canonical _ _ _ hD)
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      numer (RationalGaussianEmbedding.scalar_zero_represents F) hF hF
      (by apply ZT.derive; rfl)
  have h : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source D b N := .andI hb (.andI hN (le_refl D))
  have e := (GaussianBetaKernelRefinement.kernel_embedding D b N h).eqTrans
    ((RationalGaussianRealPart.embed_congr val).eqTrans RationalGaussianEmbedding.embed_zero)
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) e).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem row_at_endpoint (p z B b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] ap3 evaluatorF p (pairT (b*N) b) (sampleDataBeta z B N) ≐ qzero :=
  (row_at_supported p z B (b*N) b N (le_refl _)).eqTrans (original_endpoint_zero p z B b N hb hN)

theorem original_beta_zero_extended_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le (var 3) (var 4*var 5) ⟶
      ap3 evaluatorF (var 0) (pairT (var 3) (var 4)) (sampleDataBeta (var 1) (var 2) (var 5)) ≐
        row (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
      (lt (var 4*var 5) (var 3) ⟶
        ap3 evaluatorF (var 0) (pairT (var 3) (var 4)) (sampleDataBeta (var 1) (var 2) (var 5)) ≐ qzero)) :=
  closeUniv 6 (.andI (.impI (row_at_supported _ _ _ _ _ _ Prf.hyp0))
    (.impI (row_at_exterior _ _ _ _ _ _ Prf.hyp0)))

theorem original_beta_zero_extended_degree_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ le one (var 4)) ⟶ ap3 evaluatorF (var 0) (pairT (var 3*var 4) (var 3))
      (sampleDataBeta (var 1) (var 2) (var 4)) ≐ qzero) :=
  closeUniv 5 (.impI (row_at_endpoint _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaZeroExtension
