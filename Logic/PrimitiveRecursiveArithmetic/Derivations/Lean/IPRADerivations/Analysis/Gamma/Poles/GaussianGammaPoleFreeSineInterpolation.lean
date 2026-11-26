import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianNamedGammaFactorialInterpolation
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaShift
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleSearch

/-!
# The modulated Gamma recurrence at all pole-free Gaussian rational inputs

A rational argument away from the poles supplies both original
separation guards with separation 1/B, where B is its positive
denominator. The original Gamma shift and the sine period then give
the recurrence for the same modulated Gamma program at both arguments.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleFreeSineInterpolation

open_ipra
open ComplexLogarithmRemainder (normSq zeroCode)
open GaussianArctangentExponentialPeriod (fullTurnF fullTurnData original_full_turn_input)
open GaussianArctangentNamedPhase (angleF angleData)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard)
open GaussianGammaEulerHeadShift (shifted shifted_translation)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedGammaFactorialInterpolation (angle_input sinePoint sine_point_regular successor_sine_cross)
open GaussianNamedGammaSineModulation (factorF factorData factor_regular factor_proper valueF valueData)
open GaussianNamedSineFromExponential (sineF sine_proper)
open GaussianRationalHorner (ofGaussian qadd qadd_represents qadd_canonical ofGaussian_canonical ofGaussian_represents canonical_unique)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRootAlgebra (equal equal_symm equal_trans)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def poleFree (z B : PTm n) : Fm PTm n :=
  .all (equal (translated (Syn.shift z) (Syn.shift B) (var 0)) zeroCode ⟶ .bot)

ipra_subst poleFree [zeroCode, Syn.subst_shift, Syn.shift_subst]

private theorem no_pole_at (z B k : PTm n) (h : Γ ⊢[PRAAx] poleFree z B) :
    Γ ⊢[PRAAx] equal (translated z B k) zeroCode ⟶ .bot := by
  simpa [poleFree,zeroCode] using h.allE k

theorem shifted_pole_free (z B : PTm n) (h : Γ ⊢[PRAAx] poleFree z B) :
    Γ ⊢[PRAAx] poleFree (shifted z B) B := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] poleFree (Syn.shift z) (Syn.shift B) := by
    simpa only [Fm.shift,subst_poleFree,Syn.shift] using h.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx]
      equal (translated (shifted (Syn.shift z) (Syn.shift B)) (Syn.shift B) (var 0)) zeroCode ⟶ .bot := by
    refine .impI (.impE (no_pole_at (Syn.shift z) (Syn.shift B) (succ (var 0)) hs).wk ?_)
    exact equal_trans (equal_symm (shifted_translation _ _ _)) Prf.hyp0
  simpa [poleFree,Syn.shift] using h'

private theorem separated_at (z B k : PTm n) (h : Γ ⊢[PRAAx] poleFree z B) :
    Γ ⊢[PRAAx] poleAt z B one B k := by
  have nz : Γ ⊢[PRAAx] (normSq (translated z B k) ≐ zero) ⟶ .bot :=
    .impI (.impE (no_pole_at z B k h).wk (GaussianGammaPoleSearch.norm_zero_at_pole _ _ _ Prf.hyp0))
  have pos := Foundations.BoundedReflection.compl_of_ne nz
  exact le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (B*B)) pos)

theorem pole_guard (z B N : PTm n) (h : Γ ⊢[PRAAx] poleFree z B) :
    Γ ⊢[PRAAx] poleGuard z B one B N := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] poleFree (Syn.shift z) (Syn.shift B) := by
    simpa only [Fm.shift,subst_poleFree,Syn.shift] using h.shift
  simpa only [poleGuard,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    separated_at (Syn.shift z) (Syn.shift B) (var 0) hs.wk

def radius (z : PTm n) : PTm n := succ (normSq z)

theorem canonical_source (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z (radius z) B := by
  have hr : Γ ⊢[PRAAx] le one (radius z) := zero_lt_succ _
  have hp : Γ ⊢[PRAAx] le (radius z) (radius z*B) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (radius z)) hB)
  have hq : Γ ⊢[PRAAx] le one (radius z*B) := le_trans hr hp
  have hsquare : Γ ⊢[PRAAx] le (radius z) ((radius z*B)*(radius z*B)) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono hp hq)
  exact .andI hr (.andI hB (le_trans (le_succ_self _) hsquare))

theorem original_guarded_input (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] poleFree z B) :
    Γ ⊢[PRAAx] GaussianGammaShift.input z (radius z) B one B one B :=
  .andI (.andI (canonical_source z B hB) (.andI (le_refl _) (.andI hB (pole_guard z B _ hz))))
    (.andI (le_refl _) (.andI hB (pole_guard (shifted z B) B _ (shifted_pole_free z B hz))))

private theorem rational_successor (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (ofGaussian z B) qone ≐ ofGaussian (shifted z B) B := by
  let a := ComplexLogarithmRemainder.scale B ComplexLogarithmRemainder.oneCode
  have h := qadd_represents (ofGaussian z B) qone z a B hB
    (ofGaussian_represents _ _ hB) (qone_represents_scaled B)
  have eq : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.add z a) (shifted z B) := by
    open GaussianRootAlgebra in
    apply equal_of_values <;> simp only [a,shifted,translated,re_add,im_add,re_scale,im_scale] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ B (qadd_canonical _ _) (ofGaussian_canonical _ _ hB) hB
    (GaussianRationalHorner.represents_congr (.eqRefl _) eq (.eqRefl _) h) (ofGaussian_represents _ _ hB)

private theorem shifted_constant (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent constantF (shiftF constantF)
      (ofGaussian (shifted z B) B) (shiftData (ofGaussian z B)) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _)
    (GaussianEulerNamedShiftInput.regular constantF _ (constant_regular _))
  refine .allI ?_
  let p : PTm (n+1) := var 0
  let u := Syn.shift z
  let D := Syn.shift B
  have hD : Γ.map Fm.shift ⊢[PRAAx] le one D := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,D] using hB.shift
  have right := (GaussianEulerNamedShiftInput.sample_at (Γ := Γ.map Fm.shift) constantF p (ofGaussian u D)).eqTrans
    ((qadd_congr (constant_at _ _) (.eqRefl _)).eqTrans (rational_successor u D hD))
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalHorner.subst_ofGaussian,
    GaussianGammaEulerHeadShift.subst_shifted,GaussianEulerNamedShiftInput.subst_shiftData,p,u,D] using
    (constant_at p (ofGaussian (shifted u D) D)).eqTrans right.eqSymm

theorem rational_sine_successor (z B t : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (angleF constantF)) (sineF (angleF constantF))
      (sinePoint constantF t (ofGaussian (shifted z B) B)) (sinePoint constantF t (ofGaussian z B)) := by
  let x := ofGaussian z B
  let y := ofGaussian (shifted z B) B
  let P := shiftF constantF
  let v := fullTurnData t
  have hv := (original_full_turn_input (Γ := Γ) t).andE₁
  have hX := constant_regular (Γ := Γ) x
  have hY := constant_regular (Γ := Γ) y
  have hShift := GaussianEulerNamedShiftInput.regular constantF x hX
  have angle := multiply_cross fullTurnF fullTurnF constantF P v v y (shiftData x)
    hv hv hY hShift (cross_refl _ _ hv) (shifted_constant z B hB)
  have sine := sine_proper _ _ _ _ _ _ (angle_input constantF t y hY) (angle_input P t (shiftData x) hShift) angle
  exact cross_trans _ _ _ _ _ _ sine (successor_sine_cross constantF t x hX)

def interpolationF (c : PR 2) : PR 2 := valueF gammaF c (sineF (angleF constantF))
def interpolationData (c : PR 2) (z R B d b t : PTm n) : PTm n :=
  valueData gammaF c (sineF (angleF constantF)) (gammaData z R B d) b (sinePoint constantF t (ofGaussian z B))

def recurrence (c : PR 2) (z R B d f b t : PTm n) : Fm PTm n :=
  crossEquivalent (interpolationF c) (multiplyF constantF (interpolationF c))
    (interpolationData c (shifted z B) (R+one) B f b t)
    (multiplyData constantF (interpolationF c) (ofGaussian z B) (interpolationData c z R B d b t))

theorem original_guarded_recurrence (c : PR 2) (z R B a d e f b t : PTm n)
    (hg : Γ ⊢[PRAAx] GaussianGammaShift.input z R B a d e f) (hc : Γ ⊢[PRAAx] pointCN c b) :
    Γ ⊢[PRAAx] recurrence c z R B d f b t := by
  let S := sineF (angleF constantF)
  let x := ofGaussian z B
  let y := ofGaussian (shifted z B) B
  let u := sinePoint constantF t x
  let v := sinePoint constantF t y
  let g := gammaData z R B d
  let g' := gammaData (shifted z B) (R+one) B f
  have hX := constant_regular (Γ := Γ) x
  have hu := sine_point_regular constantF t x hX
  have hv := sine_point_regular (Γ := Γ) constantF t y (constant_regular _)
  have hG := gamma_regular z R B a d hg.andE₁
  have hG' := gamma_regular _ _ _ e f (GaussianGammaShift.shifted_source z R B a d e f hg)
  have he := factor_proper c S S b v u hc hv hu (rational_sine_successor z B t hg.andE₁.andE₁.andE₂.andE₁)
  have hf := factor_regular c S b u hc hu
  have combined := multiply_cross gammaF GaussianGammaShift.shiftF (factorF c S) (factorF c S)
    g' (GaussianGammaShift.shiftData z R B d) (factorData c S b v) (factorData c S b u)
    hG' (multiply_fast _ _ _ _ hX hG) (factor_regular c S b v hc hv) hf
    (GaussianGammaShift.C21_Gamma_shift z R B a d e f hg) he
  exact cross_trans _ _ _ _ _ _ combined
    (GaussianNameRingLaws.multiply_associative constantF gammaF (factorF c S) x g (factorData c S b u) hX hG hf)

theorem original_pole_free_recurrence (c : PR 2) (z B b t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] poleFree z B) (hc : Γ ⊢[PRAAx] pointCN c b) :
    Γ ⊢[PRAAx] recurrence c z (radius z) B B B b t :=
  original_guarded_recurrence c z (radius z) B one B one B b t (original_guarded_input z B hB hz) hc

def canonicalData (c : PR 2) (z B b t : PTm n) : PTm n :=
  interpolationData c z (radius z) B B b t

/-- Each side uses the radius computed from its own rational argument. -/
theorem original_canonical_recurrence (c : PR 2) (z B b t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] poleFree z B) (hc : Γ ⊢[PRAAx] pointCN c b) :
    Γ ⊢[PRAAx] crossEquivalent (interpolationF c) (multiplyF constantF (interpolationF c))
      (canonicalData c (shifted z B) B b t)
      (multiplyData constantF (interpolationF c) (ofGaussian z B) (canonicalData c z B b t)) := by
  let w := shifted z B
  let S := sineF (angleF constantF)
  let u := sinePoint constantF t (ofGaussian w B)
  have h := original_guarded_input z B hB hz
  have hw := (original_guarded_input w B hB (shifted_pole_free z B hz)).andE₁
  have hs := GaussianGammaShift.shifted_source z (radius z) B one B one B h
  have between := GaussianGammaRadiusOverlap.original_Gamma_overlap w (radius w) (radius z+one)
    B one B one B hw hs
  have hf := factor_regular c S b u hc (sine_point_regular constantF t (ofGaussian w B) (constant_regular _))
  have left := multiply_cross gammaF gammaF (factorF c S) (factorF c S)
    (gammaData w (radius w) B B) (gammaData w (radius z+one) B B) (factorData c S b u) (factorData c S b u)
    (gamma_regular _ _ _ _ _ hw) (gamma_regular _ _ _ _ _ hs) hf hf between (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ left (original_pole_free_recurrence c z B b t hB hz hc)

theorem actual_original_Gamma_sine_interpolation_pole_free_recurrence_closed (c : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 1) ⟶ poleFree (var 0) (var 1) ⟶ pointCN c (var 2) ⟶
        recurrence c (var 0) (radius (var 0)) (var 1) (var 1) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (original_pole_free_recurrence c _ _ _ _
    Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_original_Gamma_sine_interpolation_canonical_recurrence_closed (c : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 1) ⟶ poleFree (var 0) (var 1) ⟶ pointCN c (var 2) ⟶
        crossEquivalent (interpolationF c) (multiplyF constantF (interpolationF c))
          (canonicalData c (shifted (var 0) (var 1)) (var 1) (var 2) (var 3))
          (multiplyData constantF (interpolationF c) (ofGaussian (var 0) (var 1))
            (canonicalData c (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (original_canonical_recurrence c _ _ _ _
    Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleFreeSineInterpolation
