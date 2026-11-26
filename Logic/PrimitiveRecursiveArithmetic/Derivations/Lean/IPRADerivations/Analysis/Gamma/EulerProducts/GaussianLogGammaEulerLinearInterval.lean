import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerResidualDomain
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaHarmonicPrefix
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderHarmonicIntegral

/-!
# The exact linear terms of an Euler logarithm interval

Row i is the original signed rational Euler input divided by N+i+1.
The same finite table sums to that input multiplied by the original
factorial-cleared scalar harmonic interval on mesh one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum reciprocal_entry)
open GaussianGammaDigammaHarmonicPrefix (reciprocal_succ)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (linearTerm linear_product)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open RationalGaussianEmbedding (embed embed_add embed_zero)
open RationalHarmonicInterval (interval)
open RationalReciprocalPowerTail (tail tail_zero tail_succ reciprocalPower)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def harmonicInterval (N r : PTm n) : PTm n := embed (interval (N+r) N one)

def linearBody : PTm 2 := multiplyBody reciprocalBody
def linearRows (A B D neg N : PTm n) : PTm n := pairT (argument A B D neg) (pairT (succ N) one)
def linearSum (A B D neg N r : PTm n) : PTm n := sum linearBody r (linearRows A B D neg N)

@[simp] theorem subst_harmonicInterval {m : ℕ} (σ : Fin n → PTm m) (N r : PTm n) :
    Syn.subst σ (harmonicInterval N r) = harmonicInterval (Syn.subst σ N) (Syn.subst σ r) := by
  simp [harmonicInterval]

@[simp] theorem subst_linearRows {m : ℕ} (σ : Fin n → PTm m) (A B D neg N : PTm n) :
    Syn.subst σ (linearRows A B D neg N) =
      linearRows (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ N) := by
  change Syn.subst σ (pairT (GaussianRationalHorner.ofGaussian
    (GaussianLogGammaEulerResidualDomain.native A B neg) D) (pairT (succ N) one)) =
    pairT (GaussianRationalHorner.ofGaussian
      (GaussianLogGammaEulerResidualDomain.native (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ neg))
      (Syn.subst σ D)) (pairT (succ (Syn.subst σ N)) one)
  simp [one]

@[simp] theorem subst_linearSum {m : ℕ} (σ : Fin n → PTm m) (A B D neg N r : PTm n) :
    Syn.subst σ (linearSum A B D neg N r) =
      linearSum (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [linearSum]

private theorem embed_eq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] embed a ≐ embed b := by
  simpa only [RationalGaussianEmbedding.subst_embed,Syn.subst_var,Matrix.cons_val_zero] using
    (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (embed (var 0) : PTm 1)
      (σ := ![a]) (σ' := ![b]) (fun i => by fin_cases i; exact h))

private theorem shifted_index (N j : PTm n) : Γ ⊢[PRAAx] index (succ N) one j ≐ succ (N+j) := by
  unfold index
  ipra_ring

private theorem embedded_reciprocal (N j : PTm n) :
    Γ ⊢[PRAAx] embed (reciprocalPower one (succ (N+j))) ≐ fraction one (index (succ N) one j) := by
  let d := succ (N+j)
  have e : Γ ⊢[PRAAx] reciprocalPower one d ≐ GaussianEuclideanDistanceName.fraction one d :=
    RationalNonnegativePowers.fraction_congr (.eqRefl _) (pw_one d)
  exact (embed_eq e).eqTrans
    ((GaussianEulerDecayOrder.fraction_embedding one d (zero_lt_succ _)).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (shifted_index N j).eqSymm))

private def reciprocalLaw (N r : PTm n) : Fm PTm n :=
  reciprocalSum (succ N) one r ≐ embed (tail one N r)

@[simp] private theorem subst_reciprocalLaw {m : ℕ} (σ : Fin n → PTm m) (N r : PTm n) :
    (reciprocalLaw N r).subst σ = reciprocalLaw (Syn.subst σ N) (Syn.subst σ r) := by
  simp [reciprocalLaw]

private theorem reciprocal_step (N j : PTm n) (h : Γ ⊢[PRAAx] reciprocalLaw N j) :
    Γ ⊢[PRAAx] reciprocalLaw N (succ j) := by
  have read := qadd_congr h (embedded_reciprocal N j).eqSymm
  exact (reciprocal_succ (succ N) one j).eqTrans (read.eqTrans
    ((embed_add (tail one N j) (reciprocalPower one (succ (N+j)))).eqSymm.eqTrans
      (embed_eq (tail_succ one N j).eqSymm)))

private theorem reciprocal_harmonic_tail (N r : PTm n) : Γ ⊢[PRAAx] reciprocalLaw N r := by
  have all : Γ ⊢[PRAAx] .all (reciprocalLaw (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_reciprocalLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (GaussianRationalFiniteSum.sum_zero reciprocalBody (pairT (succ N) one)).eqTrans
        (((embed_eq (tail_zero one N)).eqTrans embed_zero).eqSymm)
    · simp only [subst_reciprocalLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact reciprocal_step (Syn.shift N) (var 0) Prf.hyp0
  simpa only [subst_reciprocalLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem reciprocal_harmonic_interval (N r : PTm n) :
    Γ ⊢[PRAAx] reciprocalSum (succ N) one r ≐ harmonicInterval N r := by
  have e : Γ ⊢[PRAAx] tail one N r ≐ tail one (one*N) (one*r) := by
    simpa only [RationalReciprocalPowerTail.subst_tail,Syn.subst_var,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using
      (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (tail one (var 0) (var 1) : PTm 2)
        (σ := ![N,r]) (σ' := ![one*N,one*r]) (fun i => by
          fin_cases i
          exact (one_mul N).eqSymm
          exact (one_mul r).eqSymm))
  exact (reciprocal_harmonic_tail N r).eqTrans
    (embed_eq (e.eqTrans (GaussianStirlingAllOrderHarmonicIntegral.sum_at_original N r one)))

theorem entry (A B D neg N i : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] inst2 linearBody i (linearRows A B D neg N) ≐ linearTerm A B D neg (succ (N+i)) := by
  let z := argument A B D neg
  let x := pairT (succ N) one
  have read := (reciprocal_entry (Γ := Γ) (succ N) one i).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (shifted_index N i))
  exact (multiply_body_at reciprocalBody z i x).eqTrans
    ((qmul_congr (.eqRefl _) read).eqTrans (linear_product A B D neg (succ (N+i)) hD (zero_lt_succ _)))

theorem exact_sum (A B D neg N r : PTm n) :
    Γ ⊢[PRAAx] linearSum A B D neg N r ≐ qmul (argument A B D neg) (harmonicInterval N r) :=
  (sum_multiply reciprocalBody (argument A B D neg) r (pairT (succ N) one)).eqTrans
    (qmul_congr (.eqRefl _) (reciprocal_harmonic_interval N r))

theorem actual_normalized_Euler_linear_interval_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (linearSum (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
        qmul (argument (var 0) (var 1) (var 2) (var 3)) (harmonicInterval (var 4) (var 5))) :=
  closeUniv 6 (exact_sum _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearInterval
