import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveGridTelescope
import IPRADerivations.Analysis.Beta.Primitives.GaussianBetaPrimitiveCompactStep

/-!
# Source-only beta primitive comparison on the unchanged compact grid

The original lower real-part source and finite compact/support guards
supply every local cell estimate. All grid arguments, clock-changing
endpoint samples and beta replacement rows are the original programs.
The resulting finite error compares the endpoint difference with the
literal original quadrature divided by the numerical beta degree.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveCompactGrid

open_ipra
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCompactLogarithmBounds (domain)
open GaussianBetaPrimitiveGridTelescope (gridEndpoint gridRow endpoint step quadratureScaled cellNumerator globalDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A a C E T M N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    ((le one E ⋏ le one M ⋏ le one N) ⋏
      (le one a ⋏ le (a+C) (E*T) ⋏ le (a+C) (E*N) ⋏ le ((R+one)*C) (a*M)))
def K (z R B E T N : PTm n) : PTm n := GaussianBetaPrimitiveCompactStep.curvature z R B E T N
def Z (z B N : PTm n) : PTm n := GaussianBetaPrimitiveCompactStep.polynomialBound z B N

ipra_subst source
ipra_subst K [GaussianBetaPrimitiveCompactStep.curvature, GaussianBetaPrimitiveCompactStep.powerRemainder, GaussianBetaPrimitiveCompactStep.powerLinear, GaussianBetaPrimitiveCompactStep.polynomialBound, GaussianBetaPrimitiveCompactStep.polynomialRemainder, GaussianBetaPrimitiveCompactStep.polynomialVariation, GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius, GaussianTimeWeightedPolynomialIncrement.quadraticBound]
ipra_subst Z [GaussianBetaPrimitiveCompactStep.polynomialBound]

private theorem endpoint_congr {p p' z z' B B' a a' b b' N N' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B')
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx]
    endpoint p z B a b N ≐ endpoint p' z' B' a' b' N' := by
  have lastInput : ![p,z,B,a,b,N] (5 : Fin 6) = N := rfl
  have lastOutput : ![p',z',B',a',b',N'] (5 : Fin 6) = N' := rfl
  ipra_congr (endpoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [hp, hz, hB, ha, hb, hN] using [lastInput, lastOutput]

private theorem domain_num_congr {u v b E T : PTm n} (he : Γ ⊢[PRAAx] u ≐ v)
    (h : Γ ⊢[PRAAx] domain u b E T) : Γ ⊢[PRAAx] domain v b E T :=
  .andI (.andI (le_congr (.eqRefl _) he h.andE₁.andE₁) h.andE₁.andE₂)
    (.andI (le_congr (.eqRefl _) (congrMul (.eqRefl _) he) h.andE₂.andE₁) (le_congr he (.eqRefl _) h.andE₂.andE₂))

/-- Both endpoint domains are obtained from the original numerical grid
and its literal compact endpoint, rather than supplied as row premises. -/
theorem grid_domain (i a C E T M : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] le i M) (hTop : Γ ⊢[PRAAx] le (a+C) (E*T)) : Γ ⊢[PRAAx]
    domain (a*M+C*i) (E*M) E T := by
  have base := positive_product a M ha hM
  have positive := le_trans base (le_add_right (a*M) (C*i))
  have denominator := positive_product E M hE hM
  have low : Γ ⊢[PRAAx] le M (a*M+C*i) :=
    le_trans (le_congr (one_mul M) (.eqRefl _) (mul_le_mul_right M ha)) (le_add_right (a*M) (C*i))
  have lower : Γ ⊢[PRAAx] le (E*M) (E*(a*M+C*i)) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E low)
  have row : Γ ⊢[PRAAx] le (a*M+C*i) ((a+C)*M) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ (le_refl (a*M)) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl C) hi))
  have upper : Γ ⊢[PRAAx] le ((a+C)*M) (T*(E*M)) :=
    le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right M hTop)
  exact .andI (.andI positive denominator) (.andI lower (le_trans row upper))

theorem grid_cell_source (i z R B A a C E T M N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a C E T M N) (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    GaussianBetaPrimitiveCompactStep.source z R B A E T (a*M+C*i) (E*M) C N := by
  have hE := h.andE₂.andE₁.andE₁
  have hM := h.andE₂.andE₁.andE₂.andE₁
  have hN := h.andE₂.andE₁.andE₂.andE₂
  have ha := h.andE₂.andE₂.andE₁
  have hTop := h.andE₂.andE₂.andE₂.andE₁
  have hSupport := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hSmall := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have here := grid_domain i a C E T M ha hE hM (le_of_lt hi) hTop
  have next := domain_num_congr (by ipra_ring : Γ ⊢[PRAAx] a*M+C*succ i ≐ (a*M+C*i)+C)
    (grid_domain (succ i) a C E T M ha hE hM hi hTop)
  have small := le_trans hSmall (le_add_right (a*M) (C*i))
  have shift : Γ ⊢[PRAAx] GaussianEulerPowerShiftRate.source z R B E T (a*M+C*i) (E*M) C :=
    .andI (.andI h.andE₁.andE₂.andE₁.andE₁ (.andI hE h.andE₁.andE₂.andE₁.andE₂)) (.andI here (.andI next small))
  have row := add_le_add₂ (le_refl (a*M)) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl C) hi)
  have support : Γ ⊢[PRAAx] le ((a*M+C*i)+C) ((E*M)*N) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) row)
      (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right M hSupport))
  exact .andI h.andE₁ (.andI shift (.andI hN support))

/-- The exact checked local source discharges the SAME original cell
shape, including the successor's independently changing clock. -/
theorem original_grid_cell (i p z R B A a C E T M N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a C E T M N) (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    distanceBounded (qsub (gridEndpoint (succ i) p z B a C E M N) (gridEndpoint i p z B a C E M N))
      (qmul (gridRow i p z B a C E M N) (step C E M N))
      (cellNumerator p C E M (K z R B E T N) (Z z B N)) (GaussianBetaPrimitiveGridTelescope.cellDenominator p E M) := by
  have localError : Γ ⊢[PRAAx] distanceBounded
      (qsub (GaussianBetaPrimitiveCompactStep.endpoint p z B ((a*M+C*i)+C) (E*M) N) (GaussianBetaPrimitiveCompactStep.endpoint p z B (a*M+C*i) (E*M) N))
      (GaussianBetaPrimitiveCompactStep.cell p z B (a*M+C*i) (E*M) C N)
      (GaussianBetaPrimitiveCompactStep.numerator p z R B E T (E*M) C N) (GaussianBetaPrimitiveCompactStep.denominator p (E*M)) := GaussianBetaPrimitiveCompactStep.original_cell_error p z R B A E T (a*M+C*i) (E*M) C N
    (grid_cell_source i z R B A a C E T M N h hi)
  have successor : Γ ⊢[PRAAx] endpoint p z B ((a*M+C*i)+C) (E*M) N ≐ gridEndpoint (succ i) p z B a C E M N :=
    endpoint_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (.eqRefl _)
  exact distance_congr (qsub_congr successor (.eqRefl _)) (.eqRefl _)
    (by dsimp only [GaussianBetaPrimitiveCompactStep.numerator,cellNumerator,K,Z]; ipra_ring) (.eqRefl _) localError

theorem all_cells (p z R B A a C E T M N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a C E T M N) : Γ ⊢[PRAAx]
    GaussianBetaPrimitiveGridTelescope.cellBound p z B a C E M N (K z R B E T N) (Z z B N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift M) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [GaussianBetaPrimitiveGridTelescope.cellBound,Syn.shift,subst_K,subst_Z] using
    original_grid_cell (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift M) (Syn.shift N) hs.wk Prf.hyp0

/-- Source-only exact finite beta quadrature comparison. -/
theorem original_compact_grid (p z R B A a C E T M N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a C E T M N) : Γ ⊢[PRAAx]
    distanceBounded (qsub (gridEndpoint M p z B a C E M N) (gridEndpoint zero p z B a C E M N))
      (quadratureScaled p z B a C E M N) (cellNumerator p C E M (K z R B E T N) (Z z B N)) (globalDenominator p E M) :=
  GaussianBetaPrimitiveGridTelescope.aggregate _ _ _ _ _ _ _ _ _ _
    h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂.andE₁ h.andE₂.andE₁.andE₂.andE₂ (all_cells p z R B A a C E T M N h)

/-- Source-only bound for the SAME actual returned grid program. -/
theorem returned_error (p z R B A a C E T M N : PTm n) (h : Γ ⊢[PRAAx] source z R B A a C E T M N) : Γ ⊢[PRAAx]
    distanceBounded (fstT (GaussianBetaPrimitiveGridTelescope.run p z B a C E M N))
      (fstT (sndT (GaussianBetaPrimitiveGridTelescope.run p z B a C E M N)))
      (cellNumerator p C E M (K z R B E T N) (Z z B N)) (globalDenominator p E M) := by
  have program := GaussianBetaPrimitiveGridTelescope.program_at (Γ := Γ) p z B a C E M N
  have first : Γ ⊢[PRAAx] fstT (GaussianBetaPrimitiveGridTelescope.run p z B a C E M N) ≐
      qsub (gridEndpoint M p z B a C E M N) (gridEndpoint zero p z B a C E M N) :=
    program.fstE
  have tail : Γ ⊢[PRAAx] sndT (GaussianBetaPrimitiveGridTelescope.run p z B a C E M N) ≐
      pairT (quadratureScaled p z B a C E M N)
        (GaussianCompactRiemannName.quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N)) :=
    program.sndE
  have second := tail.fstE
  exact distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _) (original_compact_grid p z R B A a C E T M N h)

theorem original_Beta_compact_grid_cells_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      GaussianBetaPrimitiveGridTelescope.cellBound (var 0) (var 1) (var 3) (var 5) (var 6) (var 7) (var 9) (var 10)
        (K (var 1) (var 2) (var 3) (var 7) (var 8) (var 10)) (Z (var 1) (var 3) (var 10))) :=
  closeUniv 11 (.impI (all_cells _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_Beta_primitive_compact_grid_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded
        (qsub (gridEndpoint (var 9) (var 0) (var 1) (var 3) (var 5) (var 6) (var 7) (var 9) (var 10))
          (gridEndpoint zero (var 0) (var 1) (var 3) (var 5) (var 6) (var 7) (var 9) (var 10)))
        (quadratureScaled (var 0) (var 1) (var 3) (var 5) (var 6) (var 7) (var 9) (var 10))
        (cellNumerator (var 0) (var 6) (var 7) (var 9) (K (var 1) (var 2) (var 3) (var 7) (var 8) (var 10)) (Z (var 1) (var 3) (var 10)))
        (globalDenominator (var 0) (var 7) (var 9))) :=
  closeUniv 11 (.impI (original_compact_grid _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))
theorem original_returned_Beta_primitive_grid_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      distanceBounded
        (fstT (GaussianBetaPrimitiveGridTelescope.run (var 0) (var 1) (var 3) (var 5) (var 6) (var 7) (var 9) (var 10)))
        (fstT (sndT (GaussianBetaPrimitiveGridTelescope.run (var 0) (var 1) (var 3) (var 5) (var 6) (var 7) (var 9) (var 10))))
        (cellNumerator (var 0) (var 6) (var 7) (var 9) (K (var 1) (var 2) (var 3) (var 7) (var 8) (var 10)) (Z (var 1) (var 3) (var 10)))
        (globalDenominator (var 0) (var 7) (var 9))) :=
  closeUniv 11 (.impI (returned_error _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveCompactGrid
