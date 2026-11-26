import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupPresentation
import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupDifference
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteEqualityChain
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary

/-!
# Integer shifts of the difference of two Bohr–Mollerup presentations

The exact unit-step law cancels the same logarithmic increment in both
programs. Finite iteration takes place only at the level of rational
observations, with quantifier-free induction at a common precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 2550000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupPeriod

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupPresentation (Presentation argument observe_value observe_recurrence values recurrence normalization)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNameRingLaws (zeroF zero_fast)
open GaussianNamedFiniteEqualityChain (allSteps finite_cross)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def differenceF (P Q : Presentation) : PR 2 := GaussianNamedDifference.nameF P.nameF Q.nameF
def differenceData (P Q : Presentation) (a b : PTm n) : PTm n :=
  GaussianNamedDifference.data (argument P a b) (argument Q a b)
def shiftBody (P Q : Presentation) : PTm 2 :=
  differenceData P Q (fstT (var 1)+sndT (var 1)*var 0) (sndT (var 1))

@[simp] theorem subst_differenceData {m : ℕ} (σ : Fin n → PTm m) (P Q : Presentation) (a b : PTm n) :
    Syn.subst σ (differenceData P Q a b) = differenceData P Q (Syn.subst σ a) (Syn.subst σ b) := by
  simp [differenceData]

theorem difference_data_congr (P Q : Presentation) (a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] differenceData P Q a b ≐ differenceData P Q c d := by
  simpa only [subst_differenceData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (differenceData P Q (var 0) (var 1) : PTm 2)
      (σ := ![a,b]) (σ' := ![c,d]) (fun i => by fin_cases i; exact ha; exact hb)

theorem shift_at (P Q : Presentation) (a b j : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody P Q) j (pairT a b) ≐ differenceData P Q (a+b*j) b := by
  have ea : Γ ⊢[PRAAx] fstT (pairT a b)+sndT (pairT a b)*j ≐ a+b*j :=
    congrAdd (fst_pair a b) (congrMul (snd_pair a b) (.eqRefl _))
  simpa [shiftBody,inst2] using
    difference_data_congr P Q _ _ _ _ ea (snd_pair a b)

theorem difference_regular (P Q : Presentation) (a b : PTm n) (hp : Γ ⊢[PRAAx] values P)
    (hq : Γ ⊢[PRAAx] values Q) (s : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN (differenceF P Q) (differenceData P Q a b) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (observe_value P a b hp s).andE₁ (observe_value Q a b hq s).andE₁

theorem step_cross (P Q : Presentation) (a b : PTm n) (hp : Γ ⊢[PRAAx] values P)
    (hq : Γ ⊢[PRAAx] values Q) (rp : Γ ⊢[PRAAx] recurrence P) (rq : Γ ⊢[PRAAx] recurrence Q)
    (s : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent (differenceF P Q) (differenceF P Q) (differenceData P Q (a+b) b) (differenceData P Q a b) := by
  let H := GaussianHarmonicLogarithmName.nameF
  let h := GaussianHarmonicLogarithmName.data a b
  have hh := GaussianHarmonicLogarithmName.name_regular a b s
  have sp : Γ ⊢[PRAAx] source (a+b) b := .andI (le_trans s.andE₁ (le_add_right _ _)) s.andE₂
  have hf := (observe_value P a b hp s).andE₁
  have hg := (observe_value Q a b hq s).andE₁
  have first := GaussianGammaRationalWendelBoundary.difference_cross P.nameF (addF H P.nameF)
    Q.nameF (addF H Q.nameF) (argument P (a+b) b) (addData h (argument P a b))
    (argument Q (a+b) b) (addData h (argument Q a b))
    (observe_value P (a+b) b hp sp).andE₁ (add_fast _ _ _ _ hh hf)
    (observe_value Q (a+b) b hq sp).andE₁ (add_fast _ _ _ _ hh hg)
    (observe_recurrence P a b rp s) (observe_recurrence Q a b rq s)
  exact cross_trans _ _ _ _ _ _ first
    (GaussianBohrMollerupDifference.cancel_common H P.nameF Q.nameF h (argument P a b) (argument Q a b) hh hf hg)

theorem periodic (P Q : Presentation) (a b j : PTm n) (hp : Γ ⊢[PRAAx] values P)
    (hq : Γ ⊢[PRAAx] values Q) (rp : Γ ⊢[PRAAx] recurrence P) (rq : Γ ⊢[PRAAx] recurrence Q)
    (s : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent (differenceF P Q) (differenceF P Q) (differenceData P Q (a+b*j) b) (differenceData P Q a b) := by
  let F := differenceF P Q
  let t := shiftBody P Q
  have source_at {k : PTm n} : Γ ⊢[PRAAx] source (a+b*k) b :=
    .andI (le_trans s.andE₁ (le_add_right _ _)) s.andE₂
  have all : Γ ⊢[PRAAx] allSteps F t (pairT a b) := by
    refine .allI ?_
    let Δ := Γ.map Fm.shift
    let A := Syn.shift a
    let B := Syn.shift b
    let i : PTm (n+1) := var 0
    have sp : Δ ⊢[PRAAx] source (A+B*i) B := by
      have ss : Δ ⊢[PRAAx] source A B := by simpa [Δ,A,B,Fm.shift,Syn.shift] using s.shift
      exact .andI (le_trans ss.andE₁ (le_add_right _ _)) ss.andE₂
    have hP : Δ ⊢[PRAAx] values P := by simpa [Δ,Fm.shift] using hp.shift
    have hQ : Δ ⊢[PRAAx] values Q := by simpa [Δ,Fm.shift] using hq.shift
    have rP : Δ ⊢[PRAAx] recurrence P := by simpa [Δ,Fm.shift] using rp.shift
    have rQ : Δ ⊢[PRAAx] recurrence Q := by simpa [Δ,Fm.shift] using rq.shift
    have next : Δ ⊢[PRAAx] (A+B*i)+B ≐ A+B*(succ i) := by ipra_ring
    have ea := (difference_data_congr P Q _ _ _ _ next (.eqRefl _)).eqTrans
      (shift_at P Q A B (succ i)).eqSymm
    have eb := (shift_at (Γ := Δ) P Q A B i).eqSymm
    simpa [GaussianBohrMollerupPresentation.subst_argument,Δ,F,t,A,B,i,Syn.shift] using
      cross_data_congr F F _ _ _ _ ea eb (step_cross P Q (A+B*i) B hP hQ rP rQ sp)
  have start := (shift_at (Γ := Γ) P Q a b zero).eqTrans
    (difference_data_congr P Q _ _ _ _ (by ipra_ring) (.eqRefl _))
  have endpoint := shift_at (Γ := Γ) P Q a b j
  have point_cast (u v : PTm n) (e : Γ ⊢[PRAAx] u ≐ v) (hu : Γ ⊢[PRAAx] pointCN F u) :
      Γ ⊢[PRAAx] pointCN F v := by
    simpa using Prf.eqSubst (pointCN F (var 0) : Fm PTm 1) (fun _ => u) (fun _ => v)
      (fun _ => e) (by simpa using hu)
  exact cross_data_congr F F _ _ _ _ endpoint start
    (finite_cross F t j (pairT a b) all
      (point_cast _ _ endpoint.eqSymm (difference_regular P Q _ _ hp hq source_at))
      (point_cast _ _ start.eqSymm (difference_regular P Q _ _ hp hq s)))

theorem zero_at_one (P Q : Presentation) (hp : Γ ⊢[PRAAx] values P)
    (hq : Γ ⊢[PRAAx] values Q) (np : Γ ⊢[PRAAx] normalization P) (nq : Γ ⊢[PRAAx] normalization Q) :
    Γ ⊢[PRAAx] crossEquivalent (differenceF P Q) zeroF (differenceData P Q one one) zero := by
  have s : Γ ⊢[PRAAx] source one one := .andI (le_refl _) (le_refl _)
  have he := GaussianGammaRationalWendelBoundary.difference_cross P.nameF zeroF Q.nameF zeroF
    (argument P one one) zero (argument Q one one) zero (observe_value P _ _ hp s).andE₁ (zero_fast _)
    (observe_value Q _ _ hq s).andE₁ (zero_fast _) np nq
  exact cross_trans _ _ _ _ _ _ he (GaussianNameRingLaws.add_negative zeroF zero (zero_fast _))

theorem zero_at_integer (P Q : Presentation) (j : PTm n) (hp : Γ ⊢[PRAAx] values P)
    (hq : Γ ⊢[PRAAx] values Q) (rp : Γ ⊢[PRAAx] recurrence P) (rq : Γ ⊢[PRAAx] recurrence Q)
    (np : Γ ⊢[PRAAx] normalization P) (nq : Γ ⊢[PRAAx] normalization Q) : Γ ⊢[PRAAx]
    crossEquivalent (differenceF P Q) zeroF (differenceData P Q (succ j) one) zero := by
  have chain := periodic P Q one one j hp hq rp rq (.andI (le_refl _) (le_refl _))
  exact cross_data_congr _ _ _ _ _ _ (difference_data_congr P Q _ _ _ _ (by ipra_ring) (.eqRefl _))
    (.eqRefl _) (cross_trans _ _ _ _ _ _ chain (zero_at_one P Q hp hq np nq))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupPeriod
