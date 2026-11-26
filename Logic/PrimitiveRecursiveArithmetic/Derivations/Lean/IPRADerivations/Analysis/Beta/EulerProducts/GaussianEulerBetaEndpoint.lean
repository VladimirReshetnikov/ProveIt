import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPrimitiveEvaluationPascal
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaProductPascal
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Exact endpoint of the actual finite Beta polynomial primitive

The actual polynomial primitive at one and the ORIGINAL reciprocal Euler
head have the same proved base and shifted Pascal recurrence. At a fixed
requested numerical horizon H, a genuine bounded atomic-QF induction
carries their equalities at all actual ShiftTrajectory offsets j with
n+j<=H. No quantified/name/analytic induction or output law is supplied.
The final value is exactly N! divided by the SAME actual rising product.
This is finite primitive algebra; analytic integration remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerBetaEndpoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul canonical)
open GaussianRationalReciprocal (qone reciprocal)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianEulerBetaPolynomialPrimitive (primitive kernel)
open GaussianEulerBetaPrimitiveEvaluationPascal (value)
open GaussianGammaShiftTrajectory (point point_zero point_succ point_native)
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerBetaPoleGuard (source)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def law (z B N : PTm n) : Fm PTm n := value z B N ≐ GaussianEulerBetaProductValue.value z B N
@[simp] theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    (law z B N).subst σ = law (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [law]

theorem law_transport {z w : PTm n} (B N : PTm n) (hz : Γ ⊢[PRAAx] z ≐ w) (h : Γ ⊢[PRAAx] law w B N) : Γ ⊢[PRAAx] law z B N := by
  have result := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (law (var 0) (var 1) (var 2) : Fm PTm 3)
    ![w,B,N] ![z,B,N] (fun i => by fin_cases i; exact hz.eqSymm; exact .eqRefl _; exact .eqRefl _) (by simpa using h)
  simpa using result

theorem base_value (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] law z B zero := by
  have k0 : Γ ⊢[PRAAx] kernel zero ≐ GaussianRationalMonicReduction.singleton qone :=
    GaussianRationalPolynomialPowers.prefix_zero GaussianEulerBetaPolynomialPrimitive.base one zero
  have reader : Γ ⊢[PRAAx] GaussianEulerBetaPrimitivePascal.reader zero zero ≐ qone :=
    (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ (le_refl zero)).eqTrans
      ((entry_congr k0 (monus_self zero)).eqTrans (GaussianRationalMonicReduction.singleton_lookup qone))
  have actual : Γ ⊢[PRAAx] GaussianEulerBetaPrimitivePascal.primitiveReader z B zero zero ≐ entry (primitive z B zero) zero :=
    (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ (le_refl zero)).eqTrans (entry_congr (.eqRefl _) (monus_self zero))
  have linearZero : Γ ⊢[PRAAx] GaussianGammaEulerHeadShift.linear z B zero ≐ GaussianRationalHorner.ofGaussian z B :=
    GaussianGammaFiniteValueProperness.fraction_equal _ _ B hB (GaussianGammaEulerHeadLower.translated_zero z B)
  have left : Γ ⊢[PRAAx] value z B zero ≐ reciprocal (GaussianRationalHorner.ofGaussian z B) :=
    (congrAp3 GaussianRationalHorner.hornerF (GaussianEulerBetaPolynomialPrimitive.primitive_length z B zero) (.eqRefl _) (.eqRefl _)).eqTrans
      ((GaussianEulerBetaPrimitiveEvaluationPascal.horner_first _ _ (GaussianEulerBetaPolynomialPrimitive.primitive_entry_canonical z B zero zero (le_refl zero))).eqTrans
        (actual.eqSymm.eqTrans ((GaussianEulerBetaPrimitivePascal.primitive_reader_value z B zero zero).eqTrans
          ((qmul_congr reader (.eqRefl _)).eqTrans
            ((GaussianEulerBetaProductPascal.one_left _ (GaussianRationalReciprocal.reciprocal_canonical _)).eqTrans
              (GaussianNameReciprocal.reciprocal_congr linearZero))))))
  exact left.eqTrans (GaussianEulerBetaProductPascal.value_zero z B hB).eqSymm

theorem positive_step (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A)
    (ih : Γ ⊢[PRAAx] law z B N) (ihShift : Γ ⊢[PRAAx] law (shifted z B) B N) : Γ ⊢[PRAAx] law z B (succ N) :=
  (GaussianEulerBetaPrimitiveEvaluationPascal.endpoint_Pascal z B N h.andE₁).eqTrans
    ((GaussianRationalSyntheticDivision.qsub_congr ih ihShift).eqTrans
      (GaussianEulerBetaProductPascal.product_value_Pascal z B A N h).eqSymm)

/-- The original positive native margin holds at every ACTUAL recursive
shift code. No source condition for a computed shifted input is assumed. -/
theorem trajectory_source (z B A j : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx] source (point z B j) B A := by
  have original := GaussianEulerBetaPoleGuard.translated_real_margin z B A j h.andE₂.andE₂
  have native := GaussianRootAlgebra.equal_re (point_native (Γ := Γ) z B j)
  have margin : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (point z B j) A B :=
    PolynomialBisection.zle_congr rfl (by
      simp only [GaussianRootAlgebra.re_scale,ZT.toZ_mul,ZT.toZ_ofNat]
      rw [native]) original
  exact .andI h.andE₁ (.andI h.andE₂.andE₁ margin)

def prefixLaw (z B H N : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift H)) ⟶ le (Syn.shift N+var 0) (Syn.shift H) ⟶
    law (point (Syn.shift z) (Syn.shift B) (var 0)) (Syn.shift B) (Syn.shift N))
def prefixSyntax (z B H N : PTm n) : BFm n := .all (succ H)
  (.imp (.le (Syn.shift N+var 0) (Syn.shift H))
    (.eq (value (point (Syn.shift z) (Syn.shift B) (var 0)) (Syn.shift B) (Syn.shift N))
      (GaussianEulerBetaProductValue.value (point (Syn.shift z) (Syn.shift B) (var 0)) (Syn.shift B) (Syn.shift N))))
@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (z B H N : PTm n) :
    (prefixLaw z B H N).subst σ = prefixLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ N) := by simp [prefixLaw,Syn.subst_shift,Syn.shift_subst]
theorem prefix_formula (z B H N : PTm n) : formula (prefixSyntax z B H N) = prefixLaw z B H N := by
  simp [prefixSyntax,prefixLaw,law,formula,BFm.le,le]

theorem prefix_at (z B H N j : PTm n) (h : Γ ⊢[PRAAx] prefixLaw z B H N)
    (hj : Γ ⊢[PRAAx] le j H) (hSum : Γ ⊢[PRAAx] le (N+j) H) : Γ ⊢[PRAAx] law (point z B j) B N := by
  have rule : Γ ⊢[PRAAx] lt j (succ H) ⟶ le (N+j) H ⟶ law (point z B j) B N := by simpa [prefixLaw] using h.allE j
  exact .impE (.impE rule ((succ_monus_succ _ _).eqTrans hj)) hSum

theorem prefix_base (z B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] prefixLaw z B H zero := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  refine .allI (.impI (.impI ?_))
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_zero] using
    base_value (point (Syn.shift z) (Syn.shift B) (var 0)) (Syn.shift B) bs.wk.wk

theorem prefix_step (z B A H N : PTm n) (hSource : Γ ⊢[PRAAx] source z B A) (h : Γ ⊢[PRAAx] prefixLaw z B H N) : Γ ⊢[PRAAx] prefixLaw z B H (succ N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift B) (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hSource.shift
  have hp : Γ.map Fm.shift ⊢[PRAAx] prefixLaw (Syn.shift z) (Syn.shift B) (Syn.shift H) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI (.impI ?_))
  let Δ := le (succ (Syn.shift N)+var 0) (Syn.shift H) :: lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift
  have next : Δ ⊢[PRAAx] le (succ (Syn.shift N+var 0)) (Syn.shift H) := le_congr (by ipra_ring) (.eqRefl _) Prf.hyp0
  have cur : Δ ⊢[PRAAx] le (Syn.shift N+var 0) (Syn.shift H) := le_trans (le_succ_self _) next
  have idx : Δ ⊢[PRAAx] le (succ (var 0)) (Syn.shift H) :=
    le_trans (le_add_left (succ (var 0)) (Syn.shift N)) (le_congr (by ipra_ring) (.eqRefl _) Prf.hyp0)
  have jBound : Δ ⊢[PRAAx] le (var 0) (Syn.shift H) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1
  have nextSum : Δ ⊢[PRAAx] le (Syn.shift N+succ (var 0)) (Syn.shift H) := le_congr (by ipra_ring) (.eqRefl _) Prf.hyp0
  have first := prefix_at (Syn.shift z) (Syn.shift B) (Syn.shift H) (Syn.shift N) (var 0) hp.wk.wk jBound cur
  have second := prefix_at (Syn.shift z) (Syn.shift B) (Syn.shift H) (Syn.shift N) (succ (var 0)) hp.wk.wk idx nextSum
  have shiftedOld : Δ ⊢[PRAAx] law (shifted (point (Syn.shift z) (Syn.shift B) (var 0)) (Syn.shift B)) (Syn.shift B) (Syn.shift N) :=
    law_transport _ _ (point_succ (Syn.shift z) (Syn.shift B) (var 0)).eqSymm second
  have result := positive_step _ _ (Syn.shift A) _
    (trajectory_source (Syn.shift z) (Syn.shift B) (Syn.shift A) (var 0) hs.wk.wk) first shiftedOld
  simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ] using result

/-- Genuine fixed-horizon two-variable uniqueness, in the object theory. -/
theorem primitive_endpoint (z B A N : PTm n) (hSource : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx] law z B N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift B) (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hSource.shift
  have all : Γ ⊢[PRAAx] .all (formula (prefixSyntax (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [prefix_formula,subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_base (Γ := Γ) z B N hSource.andE₁
    · simpa only [prefix_formula,subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_step (Γ := formula (prefixSyntax (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0)) :: Γ.map Fm.shift)
          (Syn.shift z) (Syn.shift B) (Syn.shift A) (Syn.shift N) (var 0) hs.wk (by simpa only [prefix_formula] using (Prf.hyp0 (Ax := PRAAx)))
  have result : Γ ⊢[PRAAx] prefixLaw z B N N := by
    simpa only [prefix_formula,subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  have final := prefix_at z B N N zero result (zero_le N) (le_congr (add_zero N).eqSymm (.eqRefl _) (le_refl N))
  exact law_transport B N (point_zero z B).eqSymm final

theorem primitive_endpoint_product (z B A N : PTm n) (hSource : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    value z B N ≐ qmul (GaussianRationalNaturalScale.naturalPoint (Products.fact N))
      (reciprocal (GaussianGammaRepeatedShift.risingProduct z B (succ N))) :=
  (primitive_endpoint z B A N hSource).eqTrans (GaussianEulerBetaProductValue.quotient_formula z B A N hSource)

theorem original_primitive_endpoint (z R B A N : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    value z B N ≐ qmul (GaussianRationalNaturalScale.naturalPoint (Products.fact N))
      (reciprocal (GaussianGammaRepeatedShift.risingProduct z B (succ N))) :=
  primitive_endpoint_product z B A N (GaussianEulerBetaPoleGuard.original_integral_source z R B A N h).andE₁

/-- The actual primitive endpoint, original reciprocal head, and literal
finite quotient are all returned by one primitive-recursive program. -/
def output (z B N : PTm n) : PTm n := pairT (value z B N)
  (pairT (GaussianEulerBetaProductValue.value z B N)
    (qmul (GaussianRationalNaturalScale.naturalPoint (Products.fact N))
      (reciprocal (GaussianGammaRepeatedShift.risingProduct z B (succ N)))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (z B N : PTm n) : PTm n := ap3 outputF z B N
theorem program_at (z B N : PTm n) : Γ ⊢[PRAAx] run z B N ≐ output z B N := by
  simpa [run,outputF,output,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![z,B,N]

theorem actual_Beta_primitive_endpoint_original_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ value (var 0) (var 1) (var 3) ≐ GaussianEulerBetaProductValue.value (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (primitive_endpoint _ _ _ _ Prf.hyp0))
theorem actual_Beta_polynomial_primitive_endpoint_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ value (var 0) (var 1) (var 3) ≐
      qmul (GaussianRationalNaturalScale.naturalPoint (Products.fact (var 3)))
        (reciprocal (GaussianGammaRepeatedShift.risingProduct (var 0) (var 1) (succ (var 3))))) :=
  closeUniv 4 (.impI (primitive_endpoint_product _ _ _ _ Prf.hyp0))
theorem original_Euler_Beta_polynomial_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianEulerLowerPowerCoefficients.source (var 0) (var 1) (var 2) (var 3) ⟶ value (var 0) (var 2) (var 4) ≐
      qmul (GaussianRationalNaturalScale.naturalPoint (Products.fact (var 4)))
        (reciprocal (GaussianGammaRepeatedShift.risingProduct (var 0) (var 2) (succ (var 4))))) :=
  closeUniv 5 (.impI (original_primitive_endpoint _ _ _ _ _ Prf.hyp0))
theorem actual_Beta_primitive_endpoint_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerBetaEndpoint
