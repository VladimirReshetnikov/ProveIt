import IPRADerivations.Analysis.Gamma.Names.GaussianGammaNativeLogConvexity
import IPRADerivations.Analysis.Stirling.GaussianStirlingNames
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogRescale
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogShift

/-!
# Fixed rational log presentations in the Bohr–Mollerup theorem

A presentation specifies one primitive-recursive observation program
and one argument-data term. Its regularity, real observations, exact
unit-step law, rescaling and convexity are object arithmetic premises.
-/

set_option autoImplicit false
set_option maxHeartbeats 1950000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupPresentation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (zeroF)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

structure Presentation where
  nameF : PR 2
  argumentBody : PTm 2

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (P : Presentation) (a b : PTm n) : PTm n := inst2 P.argumentBody a b
def scaledF (P : Presentation) : PR 2 := productF P.nameF
def scaledData (P : Presentation) (w a b : PTm n) : PTm n := productData P.nameF w (argument P a b)
def normalization (P : Presentation) : Fm PTm n := crossEquivalent P.nameF zeroF (argument P one one) zero
def valueAt (P : Presentation) (a b : PTm n) : Fm PTm n :=
  pointCN P.nameF (argument P a b) ⋏ realSamples P.nameF (argument P a b)
def recurrenceAt (P : Presentation) (a b : PTm n) : Fm PTm n :=
  crossEquivalent P.nameF (addF GaussianHarmonicLogarithmName.nameF P.nameF)
    (argument P (a+b) b) (addData (GaussianHarmonicLogarithmName.data a b) (argument P a b))
def rescaleAt (P : Presentation) (a b k : PTm n) : Fm PTm n :=
  crossEquivalent P.nameF P.nameF (argument P (k*a) (k*b)) (argument P a b)
def convexAt (P : Presentation) (a d b r s : PTm n) : Fm PTm n :=
  realOrder (scaledF P) (addF (scaledF P) (scaledF P))
    (scaledData P (weight r s) (barycenter a d r s) (weight r s*b))
    (addData (scaledData P (succ r) a b) (scaledData P s d b))

def values (P : Presentation) : Fm PTm n :=
  .all (.all (source (var 1) (var 0) ⟶ valueAt P (var 1) (var 0)))
def recurrence (P : Presentation) : Fm PTm n :=
  .all (.all (source (var 1) (var 0) ⟶ recurrenceAt P (var 1) (var 0)))
def rescaleFromData (P : Presentation) (x : PTm n) : Fm PTm n :=
  let a := fstT x
  let b := fstT (sndT x)
  let k := sndT (sndT x)
  source a b ⋏ le one k ⟶ rescaleAt P a b k
def rescaling (P : Presentation) : Fm PTm n := .all (rescaleFromData P (var 0))
def convexFromData (P : Presentation) (x : PTm n) : Fm PTm n :=
  let a := fstT x
  let d := fstT (sndT x)
  let b := fstT (sndT (sndT x))
  let r := fstT (sndT (sndT (sndT x)))
  let s := sndT (sndT (sndT (sndT x)))
  source a b ⋏ le one d ⟶ convexAt P a d b r s
def convexity (P : Presentation) : Fm PTm n := .all (convexFromData P (var 0))
def laws (P : Presentation) : Fm PTm n :=
  normalization P ⋏ (values P ⋏ (recurrence P ⋏ (rescaling P ⋏ convexity P)))

@[simp] theorem subst_argument {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (a b : PTm n) :
    Syn.subst σ (argument P a b) = argument P (Syn.subst σ a) (Syn.subst σ b) := by simp [argument,subst_inst2]
@[simp] theorem subst_scaledData {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (w a b : PTm n) :
    Syn.subst σ (scaledData P w a b) = scaledData P (Syn.subst σ w) (Syn.subst σ a) (Syn.subst σ b) := by simp [scaledData]
@[simp] theorem subst_normalization {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) :
    (normalization (n := n) P).subst σ = normalization (n := m) P := by simp [normalization,one]
@[simp] theorem subst_valueAt {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (a b : PTm n) :
    (valueAt P a b).subst σ = valueAt P (Syn.subst σ a) (Syn.subst σ b) := by simp [valueAt]
@[simp] theorem subst_recurrenceAt {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (a b : PTm n) :
    (recurrenceAt P a b).subst σ = recurrenceAt P (Syn.subst σ a) (Syn.subst σ b) := by simp [recurrenceAt]
@[simp] theorem subst_rescaleAt {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (a b k : PTm n) :
    (rescaleAt P a b k).subst σ = rescaleAt P (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) := by simp [rescaleAt]
@[simp] theorem subst_convexAt {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (a d b r s : PTm n) :
    (convexAt P a d b r s).subst σ =
      convexAt P (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ b) (Syn.subst σ r) (Syn.subst σ s) := by
  simp [convexAt,weight,barycenter]

@[simp] theorem subst_values {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) :
    (values (n := n) P).subst σ = values (n := m) P := by simp [values]
@[simp] theorem subst_recurrence {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) :
    (recurrence (n := n) P).subst σ = recurrence (n := m) P := by simp [recurrence]
@[simp] theorem subst_rescaleFromData {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (x : PTm n) :
    (rescaleFromData P x).subst σ = rescaleFromData P (Syn.subst σ x) := by simp [rescaleFromData,one]
@[simp] theorem subst_rescaling {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) :
    (rescaling (n := n) P).subst σ = rescaling (n := m) P := by simp [rescaling]
@[simp] theorem subst_convexFromData {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (x : PTm n) :
    (convexFromData P x).subst σ = convexFromData P (Syn.subst σ x) := by simp [convexFromData,one]
@[simp] theorem subst_convexity {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) :
    (convexity (n := n) P).subst σ = convexity (n := m) P := by simp [convexity]
@[simp] theorem subst_laws {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) :
    (laws (n := n) P).subst σ = laws (n := m) P := by simp [laws]

theorem observe_value (P : Presentation) (a b : PTm n) (h : Γ ⊢[PRAAx] values P)
    (s : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] valueAt P a b := by
  have e : Γ ⊢[PRAAx] .all (source (Syn.shift a) (var 0) ⟶ valueAt P (Syn.shift a) (var 0)) := by
    simpa [values] using h.allE a
  exact (by simpa using e.allE b : Γ ⊢[PRAAx] source a b ⟶ valueAt P a b).impE s

theorem observe_recurrence (P : Presentation) (a b : PTm n) (h : Γ ⊢[PRAAx] recurrence P)
    (s : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] recurrenceAt P a b := by
  have e : Γ ⊢[PRAAx] .all (source (Syn.shift a) (var 0) ⟶ recurrenceAt P (Syn.shift a) (var 0)) := by
    simpa [recurrence] using h.allE a
  exact (by simpa using e.allE b : Γ ⊢[PRAAx] source a b ⟶ recurrenceAt P a b).impE s

theorem observe_rescale (P : Presentation) (a b k : PTm n) (h : Γ ⊢[PRAAx] rescaling P)
    (s : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] rescaleAt P a b k := by
  let x := pairT a (pairT b k)
  have et : Γ ⊢[PRAAx] sndT x ≐ pairT b k := snd_pair _ _
  have ea : Γ ⊢[PRAAx] fstT x ≐ a := fst_pair _ _
  have eb : Γ ⊢[PRAAx] fstT (sndT x) ≐ b := (congrFst et).eqTrans (fst_pair _ _)
  have ek : Γ ⊢[PRAAx] sndT (sndT x) ≐ k := (congrSnd et).eqTrans (snd_pair _ _)
  let formula : Fm PTm 3 := source (var 0) (var 1) ⋏ le one (var 2) ⟶
    rescaleAt P (var 0) (var 1) (var 2)
  have packed : Γ ⊢[PRAAx] rescaleFromData P x := by simpa [rescaling] using h.allE x
  have E := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) formula
    ![fstT x,fstT (sndT x),sndT (sndT x)] ![a,b,k]
    (fun i => by fin_cases i; exact ea; exact eb; exact ek)
    (by simpa [formula,rescaleFromData] using packed)
  exact (by simpa [formula] using E :
    Γ ⊢[PRAAx] source a b ⋏ le one k ⟶ rescaleAt P a b k).impE (.andI s hk)

theorem observe_convex (P : Presentation) (a d b r s : PTm n) (h : Γ ⊢[PRAAx] convexity P)
    (ha : Γ ⊢[PRAAx] source a b) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] convexAt P a d b r s := by
  let x := pairT a (pairT d (pairT b (pairT r s)))
  let read (u : PTm n) := sndT u
  have e₁ : Γ ⊢[PRAAx] read x ≐ pairT d (pairT b (pairT r s)) := snd_pair _ _
  have e₂ : Γ ⊢[PRAAx] read (read x) ≐ pairT b (pairT r s) :=
    (congrSnd e₁).eqTrans (snd_pair _ _)
  have e₃ : Γ ⊢[PRAAx] read (read (read x)) ≐ pairT r s :=
    (congrSnd e₂).eqTrans (snd_pair _ _)
  have ea : Γ ⊢[PRAAx] fstT x ≐ a := fst_pair _ _
  have ed : Γ ⊢[PRAAx] fstT (read x) ≐ d := (congrFst e₁).eqTrans (fst_pair _ _)
  have eb : Γ ⊢[PRAAx] fstT (read (read x)) ≐ b := (congrFst e₂).eqTrans (fst_pair _ _)
  have er : Γ ⊢[PRAAx] fstT (read (read (read x))) ≐ r := (congrFst e₃).eqTrans (fst_pair _ _)
  have es : Γ ⊢[PRAAx] read (read (read (read x))) ≐ s := (congrSnd e₃).eqTrans (snd_pair _ _)
  let formula : Fm PTm 5 := source (var 0) (var 2) ⋏ le one (var 1) ⟶
    convexAt P (var 0) (var 1) (var 2) (var 3) (var 4)
  have packed : Γ ⊢[PRAAx] convexFromData P x := by simpa [convexity] using h.allE x
  have E := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) formula
    ![fstT x,fstT (read x),fstT (read (read x)),fstT (read (read (read x))),read (read (read (read x)))]
    ![a,d,b,r,s] (fun i => by fin_cases i; exact ea; exact ed; exact eb; exact er; exact es)
    (by simpa [formula,convexFromData,read] using packed)
  exact (by simpa [formula] using E :
    Γ ⊢[PRAAx] source a b ⋏ le one d ⟶ convexAt P a d b r s).impE (.andI ha hd)

def native : Presentation :=
  ⟨GaussianStirlingGammaLogarithm.logGammaF,GaussianStirlingGammaLogarithm.logGammaData (var 0) (var 1)⟩

@[simp] theorem native_program : native.nameF = GaussianStirlingGammaLogarithm.logGammaF := rfl

@[simp] theorem native_argument (a b : PTm n) :
    argument native a b = GaussianStirlingGammaLogarithm.logGammaData a b := by
  simp [native,argument,inst2]

theorem native_values : Γ ⊢[PRAAx] values native := by
  refine .allI (.allI (.impI ?_))
  simpa only [valueAt,native_program,native_argument] using
    Prf.andI (GaussianStirlingGammaLogarithm.log_gamma_regular (var 1) (var 0) Prf.hyp0)
      (GaussianStirlingNames.log_gamma_real (var 1) (var 0))

theorem native_recurrence : Γ ⊢[PRAAx] recurrence native := by
  refine .allI (.allI (.impI ?_))
  simpa only [recurrenceAt,native_program,native_argument] using GaussianStirlingGammaLogShift.log_gamma_increment _ _ Prf.hyp0

theorem native_rescaling : Γ ⊢[PRAAx] rescaling native := by
  refine .allI (.impI ?_)
  simpa only [rescaleAt,native_program,native_argument] using GaussianStirlingGammaLogRescale.log_gamma_rescale _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂

theorem native_convexity : Γ ⊢[PRAAx] convexity native := by
  refine .allI (.impI ?_)
  simpa only [convexAt,scaledF,scaledData,native_program,native_argument,source,
    GaussianGammaNativeLogConvexityCore.nativeCenterData,
    GaussianGammaNativeLogConvexityCore.nativeWeightedData] using
    GaussianGammaNativeLogConvexity.weighted_convexity _ _ _ _ _
      Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₂ Prf.hyp0.andE₁.andE₂

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupPresentation
