import IPRADerivations.Analysis.Euler.PositiveAxis.Moments.GaussianEulerIntegerMomentUniform
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactClientIndependence
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAdditivity

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

open_ipra
open GaussianCompactRiemannName (evaluatorName nameData inside grid sampleBody sampleData quadrature)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaShiftTrajectory (point)
open GaussianEulerIntegerMomentIntegrand (monomial)

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
ipra_subst source
ipra_subst fixedData
ipra_subst evaluatorTerm

theorem evaluator_at (p t z B N T : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B N T) ≐ ap2 U p
      (GaussianEulerIntegerMomentUniform.nameData z B N (fstT t) (sndT t) T) := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 1)
    (ap2 U (var 0) (GaussianEulerIntegerMomentUniform.nameData (fstT (var 2)) (sndT (var 2))
        (fstT (var 3)) (fstT (var 1)) (sndT (var 1)) (sndT (var 3)))) p t ![pairT z B, pairT N T]
  simp only [subst_ap2, GaussianEulerIntegerMomentUniform.subst_nameData,
    subst_fstT, subst_sndT, Syn.subst_var] at read
  refine read.eqTrans (congrAp2 U (.eqRefl p) ?_)
  ipra_congr (GaussianEulerIntegerMomentUniform.nameData (var 0) (var 1) (var 2)
    (fstT (var 3)) (sndT (var 3)) (var 4) : PTm 5) with
    [fst_pair z B, snd_pair z B, fst_pair N T, .eqRefl t, snd_pair N T]

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
