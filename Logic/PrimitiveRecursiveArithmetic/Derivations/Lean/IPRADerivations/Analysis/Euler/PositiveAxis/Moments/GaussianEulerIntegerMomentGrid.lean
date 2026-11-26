import IPRADerivations.Analysis.Euler.PositiveAxis.Moments.GaussianEulerIntegerMomentUniform
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactClientIndependence
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# Literal integer-moment rows on the unchanged affine Euler grid

A fixed PR3 client evaluates the actual uniform-clock product t^N times
its original base Euler observation. Source-only compact time guards
identify it with the unchanged original shifted evaluator. The finite
quadrature error is exactly the physical width times the two requested
observation allowances, for arbitrary internal moment and mesh indices.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegerMomentGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (evaluatorName nameData inside grid sampleBody sampleData quadrature)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaShiftTrajectory (point)
open GaussianEulerIntegerMomentIntegrand (monomial)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "U" => GaussianEulerIntegerMomentUniform.nameF
local notation "F" => GaussianEulerIntegrandName.evaluatorF

def source (B a C E T : PTm n) : Fm PTm n :=
  (le one B ⋏ le one E) ⋏ (le one a ⋏ le (a+C) (E*T))
def fixedData (z B N T : PTm n) : PTm n := pairT (pairT z B) (pairT N T)
def evaluatorTerm (p t x : PTm n) : PTm n := ap2 U p
  (GaussianEulerIntegerMomentUniform.nameData (fstT (fstT x)) (sndT (fstT x)) (fstT (sndT x))
    (fstT t) (sndT t) (sndT (sndT x)))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (B a C E T : PTm n) :
    (source B a C E T).subst σ = source (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [source]
@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (z B N T : PTm n) :
    Syn.subst σ (fixedData z B N T) = fixedData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ T) := by simp [fixedData]
@[simp] theorem subst_evaluatorTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluatorTerm p t x) = evaluatorTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [evaluatorTerm]

private theorem row_data_congr (z B N a b T z' B' N' T' : PTm n)
    (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hT : Γ ⊢[PRAAx] T ≐ T') : Γ ⊢[PRAAx]
    GaussianEulerIntegerMomentUniform.nameData z B N a b T ≐ GaussianEulerIntegerMomentUniform.nameData z' B' N' a b T' := by
  have e1 : Γ ⊢[PRAAx] GaussianEulerIntegerMomentUniform.nameData z B N a b T ≐ GaussianEulerIntegerMomentUniform.nameData z' B N a b T := by
    simpa only [GaussianEulerIntegerMomentUniform.subst_nameData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerIntegerMomentUniform.nameData (var 0) (Syn.shift B) (Syn.shift N) (Syn.shift a) (Syn.shift b) (Syn.shift T)) hz
  have e2 : Γ ⊢[PRAAx] GaussianEulerIntegerMomentUniform.nameData z' B N a b T ≐ GaussianEulerIntegerMomentUniform.nameData z' B' N a b T := by
    simpa only [GaussianEulerIntegerMomentUniform.subst_nameData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerIntegerMomentUniform.nameData (Syn.shift z') (var 0) (Syn.shift N) (Syn.shift a) (Syn.shift b) (Syn.shift T)) hB
  have e3 : Γ ⊢[PRAAx] GaussianEulerIntegerMomentUniform.nameData z' B' N a b T ≐ GaussianEulerIntegerMomentUniform.nameData z' B' N' a b T := by
    simpa only [GaussianEulerIntegerMomentUniform.subst_nameData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerIntegerMomentUniform.nameData (Syn.shift z') (Syn.shift B') (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift T)) hN
  have e4 : Γ ⊢[PRAAx] GaussianEulerIntegerMomentUniform.nameData z' B' N' a b T ≐ GaussianEulerIntegerMomentUniform.nameData z' B' N' a b T' := by
    simpa only [GaussianEulerIntegerMomentUniform.subst_nameData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerIntegerMomentUniform.nameData (Syn.shift z') (Syn.shift B') (Syn.shift N') (Syn.shift a) (Syn.shift b) (var 0)) hT
  exact e1.eqTrans (e2.eqTrans (e3.eqTrans e4))

theorem evaluator_at (p t z B N T : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B N T) ≐ ap2 U p
      (GaussianEulerIntegerMomentUniform.nameData z B N (fstT t) (sndT t) T) := by
  have raw : Γ ⊢[PRAAx] ap3 evaluatorF p t (fixedData z B N T) ≐ evaluatorTerm p t (fixedData z B N T) := by
    simpa only [evaluatorF,ap3,subst_evaluatorTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,fixedData z B N T]
  have l := fst_pair (Γ := Γ) (pairT z B) (pairT N T)
  have r := snd_pair (Γ := Γ) (pairT z B) (pairT N T)
  exact raw.eqTrans (congrAp2 U (.eqRefl _) (row_data_congr _ _ _ _ _ _ _ _ _ _
    ((congrFst l).eqTrans (fst_pair _ _)) ((congrSnd l).eqTrans (snd_pair _ _))
    ((congrFst r).eqTrans (fst_pair _ _)) ((congrSnd r).eqTrans (snd_pair _ _))))

theorem wrapped_at (p t z B N T : PTm n) : Γ ⊢[PRAAx]
    ap2 (evaluatorName evaluatorF) p (nameData t (fixedData z B N T)) ≐ ap2 U p
      (GaussianEulerIntegerMomentUniform.nameData z B N (fstT t) (sndT t) T) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_at p t z B N T)

theorem wrapped_cross (t z B N E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerIntegerMomentIntegrand.source B (fstT t) (sndT t) E T) : Γ ⊢[PRAAx]
    crossEquivalent (evaluatorName F) (evaluatorName evaluatorF)
      (nameData t (GaussianEulerIntegrandName.fixedData (point z B N) B)) (nameData t (fixedData z B N T)) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianEulerIntegerMomentIntegrand.source
      (Syn.shift (Syn.shift B)) (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t)))
      (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianCompactRiemannName.subst_nameData,GaussianEulerIntegrandName.subst_fixedData,
    subst_fixedData,GaussianGammaShiftTrajectory.subst_point,Syn.shift] using
    distance_congr (GaussianEulerCompactModulus.wrapped_at (var 1) (Syn.shift (Syn.shift t))
      (point (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N))) (Syn.shift (Syn.shift B))).eqSymm
      (wrapped_at (var 0) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))
        (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift T))).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerIntegerMomentUniform.original_observations (var 1) (var 0) (Syn.shift (Syn.shift z))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) (fstT (Syn.shift (Syn.shift t)))
        (sndT (Syn.shift (Syn.shift t))) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) hs)

theorem local_agreement (z B N a C E T : PTm n) (h : Γ ⊢[PRAAx] source B a C E T) : Γ ⊢[PRAAx]
    GaussianCompactClientIndependence.localAgreement F evaluatorF a C E
      (GaussianEulerIntegrandName.fixedData (point z B N) B) (fixedData z B N T) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  have ht := GaussianEulerCompactAdditivity.domain_of_inside (var 0) (Syn.shift a) (Syn.shift C)
    (Syn.shift E) (Syn.shift T) hs.andE₂.andE₁.wk hs.andE₁.andE₂.wk hs.andE₂.andE₂.wk Prf.hyp0
  simpa only [GaussianCompactClientIndependence.localAgreement,GaussianCompactClientIndependence.agreementBody,
    GaussianEulerIntegrandName.subst_fixedData,subst_fixedData,GaussianGammaShiftTrajectory.subst_point,Syn.shift] using
    wrapped_cross (var 0) (Syn.shift z) (Syn.shift B) (Syn.shift N) (Syn.shift E) (Syn.shift T)
      (.andI hs.andE₁.andE₁.wk (.andI hs.andE₁.andE₂.wk ht))

theorem original_grid_distance (p q M z B N a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source B a C E T) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p M a C E (GaussianEulerIntegrandName.fixedData (point z B N) B))
      (quadrature evaluatorF q M a C E (fixedData z B N T)) (C*(unit p+unit q)) (E*(unit p*unit q)) :=
  GaussianCompactClientIndependence.quadrature_distance F evaluatorF p q M a C E _ _
    (local_agreement z B N a C E T h) h.andE₂.andE₁ h.andE₁.andE₂ hM

theorem literal_row_at (i p M z B N a C E T : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody evaluatorF) i (sampleData p M a C E (fixedData z B N T)) ≐
      qmul (monomial N (fstT (grid i M a C E)) (sndT (grid i M a C E)))
        (ap2 GaussianEulerIntegrandName.nameF (GaussianEulerIntegerMomentUniform.clock p N T)
          (GaussianEulerIntegrandName.data z B (fstT (grid i M a C E)) (sndT (grid i M a C E)))) :=
  (GaussianCompactRiemannName.sample_body_at evaluatorF i p M a C E _).eqTrans
    ((evaluator_at p (grid i M a C E) z B N T).eqTrans (GaussianEulerIntegerMomentUniform.sample_at p z B N _ _ T))

theorem actual_original_integer_moment_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 4) (var 6) (var 7) (var 8) (var 9) ⟶ le one (var 2) ⟶
      distanceBounded (quadrature F (var 0) (var 2) (var 6) (var 7) (var 8)
        (GaussianEulerIntegrandName.fixedData (point (var 3) (var 4) (var 5)) (var 4)))
        (quadrature evaluatorF (var 1) (var 2) (var 6) (var 7) (var 8) (fixedData (var 3) (var 4) (var 5) (var 9)))
        ((var 7)*(unit (var 0)+unit (var 1))) ((var 8)*(unit (var 0)*unit (var 1)))) :=
  closeUniv 10 (.impI (.impI (original_grid_distance _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegerMomentGrid
