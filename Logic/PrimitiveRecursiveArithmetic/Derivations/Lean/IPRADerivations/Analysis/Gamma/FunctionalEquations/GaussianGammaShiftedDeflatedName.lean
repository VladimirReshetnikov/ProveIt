import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShiftedDeflatedPolynomial

/-!
# A genuine regular name from the deflated original Gamma polynomials

The numerical Fast(B,p) clock pays the native reciprocal bound in the
actual full-polynomial comparison. No regularity of the deflated sampler
is supplied: exact compatibility with the original shifted C7 name
derives its own pointCN.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaShiftedDeflatedPolynomial (input rawValue shiftedSample)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def data (z R B d : PTm n) : PTm n := pairT z (pairT R (pairT B d))
def rawTerm (p x : PTm n) : PTm n := rawValue p (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x)))
def rawF : PR 2 := PTm.toPR (rawTerm (var 0) (var 1))
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def nameData (z R B d : PTm n) : PTm n := GaussianFastValueCut.nameData B (data z R B d)
def clock (p B : PTm n) : PTm n := GaussianFastValueCut.exponent B p

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B d : PTm n) :
    Syn.subst σ (data z R B d) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_rawTerm {m : ℕ} (σ : Fin n → PTm m) (p x : PTm n) :
    Syn.subst σ (rawTerm p x) = rawTerm (Syn.subst σ p) (Syn.subst σ x) := by simp [rawTerm]
@[simp] theorem subst_nameData {m : ℕ} (σ : Fin n → PTm m) (z R B d : PTm n) :
    Syn.subst σ (nameData z R B d) = nameData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by simp [nameData]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p B : PTm n) :
    Syn.subst σ (clock p B) = clock (Syn.subst σ p) (Syn.subst σ B) := by simp [clock]

private theorem value_congr (p z R B d z' R' B' d' : PTm n)
    (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R')
    (hB : Γ ⊢[PRAAx] B ≐ B') (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx]
    rawValue p z R B d ≐ rawValue p z' R' B' d' := by
  have e1 : Γ ⊢[PRAAx] rawValue p z R B d ≐ rawValue p z' R B d := by
    simpa only [GaussianGammaShiftedDeflatedPolynomial.subst_rawValue,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rawValue (Syn.shift p) (var 0) (Syn.shift R) (Syn.shift B) (Syn.shift d)) hz
  have e2 : Γ ⊢[PRAAx] rawValue p z' R B d ≐ rawValue p z' R' B d := by
    simpa only [GaussianGammaShiftedDeflatedPolynomial.subst_rawValue,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rawValue (Syn.shift p) (Syn.shift z') (var 0) (Syn.shift B) (Syn.shift d)) hR
  have e3 : Γ ⊢[PRAAx] rawValue p z' R' B d ≐ rawValue p z' R' B' d := by
    simpa only [GaussianGammaShiftedDeflatedPolynomial.subst_rawValue,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rawValue (Syn.shift p) (Syn.shift z') (Syn.shift R') (var 0) (Syn.shift d)) hB
  have e4 : Γ ⊢[PRAAx] rawValue p z' R' B' d ≐ rawValue p z' R' B' d' := by
    simpa only [GaussianGammaShiftedDeflatedPolynomial.subst_rawValue,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (rawValue (Syn.shift p) (Syn.shift z') (Syn.shift R') (Syn.shift B') (var 0)) hd
  exact e1.eqTrans (e2.eqTrans (e3.eqTrans e4))

theorem raw_at (p z R B d : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (data z R B d) ≐ rawValue p z R B d := by
  have actual : Γ ⊢[PRAAx] ap2 rawF p (data z R B d) ≐ rawTerm p (data z R B d) := by
    simpa only [rawF,ap2,subst_rawTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (rawTerm (var 0) (var 1) : PTm 2) ![p,data z R B d]
  have first := snd_pair (Γ := Γ) z (pairT R (pairT B d))
  have second := (congrSnd first).eqTrans (snd_pair R (pairT B d))
  exact actual.eqTrans (value_congr _ _ _ _ _ _ _ _ _ (fst_pair _ _)
    ((congrFst first).eqTrans (fst_pair _ _))
    ((congrFst second).eqTrans (fst_pair _ _))
    ((congrSnd second).eqTrans (snd_pair _ _)))

theorem name_at (p z R B d : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (nameData z R B d) ≐ rawValue (clock p B) z R B d :=
  (GaussianFastValueCut.name_at rawF B (data z R B d) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p B) z R B d)).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.horner_canonical _ _ _)))

/-- The original shifted P and the actual new deflated program keep both requested errors. -/
theorem original_observations (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] input z R B) : Γ ⊢[PRAAx]
    distanceBounded (shiftedSample p z R B) (ap2 nameF q (nameData z R B d))
      (unit p+unit q) (unit p*unit q) := by
  have paid := GaussianFastValueCut.query_budget (Γ := Γ) B q
  have old := GaussianGammaShiftedDeflatedPolynomial.original_observations p (clock q B) z R B d h
  have fine := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive p) (unit_positive (clock q B))) (positive_product _ _ (unit_positive p) (unit_positive q))
    (by dsimp only [GaussianGammaShiftedDeflatedPolynomial.numerator,GaussianGammaShiftedDeflatedPolynomial.denominator,clock]
        ipra_le (𝔞 (unit p)^2)*sl paid) old
  exact distance_congr (.eqRefl _) (name_at q z R B d).eqSymm (.eqRefl _) (.eqRefl _) fine

theorem original_cross (z R B d : PTm n) (h : Γ ⊢[PRAAx] input z R B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF nameF (GaussianGammaRepeatedShift.stageData z R B one) (nameData z R B d) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEuclideanPointDistance.unit,unit,shiftedSample,GaussianGammaRepeatedShift.stage,
    GaussianGammaRepeatedShift.subst_stageData,subst_nameData,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      original_observations (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift d)) hs

theorem name_regular (z R B d : PTm n) (h : Γ ⊢[PRAAx] input z R B) : Γ ⊢[PRAAx] pointCN nameF (nameData z R B d) := by
  have eqn := original_cross z R B d h
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ eqn) eqn

theorem actual_original_shifted_P_deflated_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶ crossEquivalent GaussianGammaC7Name.nameF nameF
      (GaussianGammaRepeatedShift.stageData (var 0) (var 1) (var 2) one) (nameData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_cross _ _ _ _ Prf.hyp0))
theorem actual_original_shifted_P_deflated_regularity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶ pointCN nameF (nameData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedName
