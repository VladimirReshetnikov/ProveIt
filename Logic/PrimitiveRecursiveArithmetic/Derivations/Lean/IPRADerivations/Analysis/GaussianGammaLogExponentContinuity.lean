import IPRADerivations.Analysis.GaussianGammaFiniteApproximantName
import IPRADerivations.Analysis.GaussianExponentialReference

/-!
# Quantitative continuity of the original Euler mesh exponent

Both actual normalized multiplication clocks are retained. Their log
queries are compared through the SAME original mesh-log name, while
input variation is measured on the original encoded Gaussian fractions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaLogExponentContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (logF logExponentF logExponentData log_regular log_exponent_regular)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalReciprocal (bound_congr bounded_negative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def logRadius (N : PTm n) : PTm n := GaussianNameBounds.U logF N
def exponentRadius (R N : PTm n) : PTm n := logRadius N*R
def query (p z B N : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus logF constantF N (qnegative (ofGaussian z B))) p
@[simp] theorem subst_logRadius {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (logRadius N) = logRadius (Syn.subst σ N) := by simp [logRadius]
@[simp] theorem subst_exponentRadius {l : ℕ} (σ : Fin n → PTm l) (R N : PTm n) :
    Syn.subst σ (exponentRadius R N) = exponentRadius (Syn.subst σ R) (Syn.subst σ N) := by simp [exponentRadius]
@[simp] theorem subst_query {l : ℕ} (σ : Fin n → PTm l) (p z B N : PTm n) :
    Syn.subst σ (query p z B N) = query (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [query]

theorem query_later (p z B N : PTm n) : Γ ⊢[PRAAx] le p (query p z B N) :=
  le_add_right _ _

theorem exponent_at (p z B N : PTm n) : Γ ⊢[PRAAx]
    ap2 logExponentF p (logExponentData z B N) ≐ qmul (ap2 logF (query p z B N) N) (qnegative (ofGaussian z B)) :=
  (GaussianNameArithmetic.multiply_at logF constantF N (qnegative (ofGaussian z B)) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (constant_at _ _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem log_sample_bound (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    bounded (ap2 logF p N) (logRadius N) one :=
  GaussianNameBounds.sample_bound logF N p (log_regular N hN)

theorem exponent_bound (p z R B N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    bounded (ap2 logExponentF p (logExponentData z B N)) (exponentRadius R N) one :=
  bound_congr (exponent_at p z B N).eqSymm (.eqRefl _) (one_mul _)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _)
      (log_sample_bound (query p z B N) N hN) (bounded_negative _ _ _ (le_refl _)
        (GaussianGammaEulerHead.fraction_disk z R B hB hz)))

theorem exponent_input (z R B N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input logExponentF (exponentRadius R N) (logExponentData z B N) := by
  refine .andI (log_exponent_regular z B N hN) (.allI ?_)
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift,ComplexLogarithmRemainder.bounded] using hz.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,subst_exponentRadius,
    GaussianNameArithmetic.subst_multiplyData,GaussianRationalMetric.subst_qnegative,
    GaussianRationalHorner.subst_ofGaussian,Syn.shift,logExponentData,PTm.subst_succ,PTm.subst_zero] using
    exponent_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) ns bs zs

theorem log_query_distance (p z w B N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 logF (query p z B N) N) (ap2 logF (query p w B N) N) two (unit p) := by
  let s := query p z B N
  let t := query p w B N
  have raw := GaussianNameEquivalence.point_at logF N s t (log_regular N hN)
  have gs := GaussianExponentialReference.unit_monotone (query_later (Γ := Γ) p z B N)
  have gt := GaussianExponentialReference.unit_monotone (query_later (Γ := Γ) p w B N)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t)) (unit_positive p) _ raw
  have a : Γ ⊢[PRAAx] le (unit p*unit t) (unit s*unit t) := mul_le_mul_right (unit t) gs
  have b : Γ ⊢[PRAAx] le (unit p*unit s) (unit t*unit s) := mul_le_mul_right (unit s) gt
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ a b)

/-- Negation is measured through the actual original representations. -/
theorem negative_fraction_distance (z w B A D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w B) A D) : Γ ⊢[PRAAx]
    distanceBounded (qnegative (ofGaussian z B)) (qnegative (ofGaussian w B)) A D := by
  have hz := GaussianRationalHorner.ofGaussian_represents z B hB
  have hw := GaussianRationalHorner.ofGaussian_represents w B hB
  have old := (GaussianRationalMetric.bounded_difference_iff _ _ z w B A D hB hD hz hw).iffMp h
  apply (GaussianRationalMetric.bounded_difference_iff _ _ _ _ B A D hB hD
    (GaussianRationalMetric.qnegative_represents _ _ _ hz) (GaussianRationalMetric.qnegative_represents _ _ _ hw)).iffMpr
  have eq : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq
      (GaussianRootAlgebra.sub (ComplexLogarithmRemainder.neg z) (ComplexLogarithmRemainder.neg w)) ≐
      ComplexLogarithmRemainder.normSq (GaussianRootAlgebra.sub z w) := by
    have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
        (GaussianRootAlgebra.sub (ComplexLogarithmRemainder.neg z) (ComplexLogarithmRemainder.neg w))
        (ComplexLogarithmRemainder.neg (GaussianRootAlgebra.sub z w)) := by
      apply GaussianRootAlgebra.equal_of_values <;>
        simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg] <;> ring
    exact (GaussianRootAlgebra.normSq_equal native).eqTrans (ComplexLogarithmRemainder.normSq_neg _)
  exact le_congr (congrMul (.eqRefl _) eq).eqSymm (.eqRefl _) old

def distanceBudget (p R A D N : PTm n) : PTm n := two*D*R+logRadius N*A*unit p
@[simp] theorem subst_distanceBudget {l : ℕ} (σ : Fin n → PTm l) (p R A D N : PTm n) :
    Syn.subst σ (distanceBudget p R A D N) = distanceBudget (Syn.subst σ p) (Syn.subst σ R)
      (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ N) := by simp [distanceBudget]

theorem exponent_distance (p z w R B A D N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w B) A D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 logExponentF p (logExponentData z B N)) (ap2 logExponentF p (logExponentData w B N))
      (distanceBudget p R A D N) (D*unit p) := by
  have den := positive_product _ _ hD (unit_positive p)
  have logs := distance_radius_mono _ _ two (unit p) (two*D) (D*unit p) (unit_positive p) den
    (le_of_eq_add (d := zero) (by ipra_ring)) (log_query_distance p z w B N hN)
  have inputs := distance_radius_mono _ _ A D (A*unit p) (D*unit p) hD den
    (le_of_eq_add (d := zero) (by ipra_ring)) (negative_fraction_distance z w B A D hB hD hd)
  have raw := GaussianNameArithmetic.product_distance _ _ _ _ (two*D) (A*unit p) (D*unit p) R (logRadius N)
    den logs inputs (bounded_negative _ _ _ (le_refl _) (GaussianGammaEulerHead.fraction_disk z R B hB hz))
    (log_sample_bound (query p w B N) N hN)
  exact distance_congr (exponent_at p z B N).eqSymm (exponent_at p w B N).eqSymm (by unfold distanceBudget; ipra_ring) (.eqRefl _) raw

/-- The actual original exponent observations and their computed budget. -/
def output (p z w R B A D N : PTm n) : PTm n := pairT (ap2 logExponentF p (logExponentData z B N))
  (pairT (ap2 logExponentF p (logExponentData w B N)) (pairT (distanceBudget p R A D N) (D*unit p)))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (p z w R B A D N : PTm n) : PTm n := PTm.app outputF ![p,z,w,R,B,A,D,N]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p z w R B A D N : PTm n) :
    Syn.subst σ (output p z w R B A D N) = output (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ w)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ N) := by simp [output,logExponentData]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p z w R B A D N : PTm n) :
    Syn.subst σ (run p z w R B A D N) = run (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ w)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem program_at (p z w R B A D N : PTm n) : Γ ⊢[PRAAx] run p z w R B A D N ≐ output p z w R B A D N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![p,z,w,R,B,A,D,N]
theorem returned_left (p z w R B A D N : PTm n) : Γ ⊢[PRAAx]
    fstT (run p z w R B A D N) ≐ ap2 logExponentF p (logExponentData z B N) :=
  (congrFst (program_at p z w R B A D N)).eqTrans (fst_pair _ _)
theorem returned_right (p z w R B A D N : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p z w R B A D N)) ≐ ap2 logExponentF p (logExponentData w B N) :=
  ((congrFst (congrSnd (program_at p z w R B A D N))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_budget (p z w R B A D N : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run p z w R B A D N))) ≐ distanceBudget p R A D N :=
  (((congrFst (congrSnd (congrSnd (program_at p z w R B A D N)))).eqTrans (congrFst (congrSnd (snd_pair _ _)))).eqTrans
    (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (p z w R B A D N : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run p z w R B A D N))) ≐ D*unit p :=
  (((congrSnd (congrSnd (congrSnd (program_at p z w R B A D N)))).eqTrans (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_original_mesh_exponent_uniform_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      GaussianRadiusExponentialName.input logExponentF (exponentRadius (var 1) (var 3)) (logExponentData (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (exponent_input _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_original_mesh_log_query_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ distanceBounded (ap2 logF (query (var 0) (var 1) (var 3) (var 4)) (var 4))
      (ap2 logF (query (var 0) (var 2) (var 3) (var 4)) (var 4)) two (unit (var 0))) :=
  closeUniv 5 (.impI (log_query_distance _ _ _ _ _ Prf.hyp0))
theorem actual_original_mesh_exponent_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 7) ⟶ le one (var 4) ⟶ le one (var 6) ⟶
      ComplexLogarithmRemainder.bounded (var 1) (var 3*var 4) ⟶
      distanceBounded (ofGaussian (var 1) (var 4)) (ofGaussian (var 2) (var 4)) (var 5) (var 6) ⟶
      distanceBounded (ap2 logExponentF (var 0) (logExponentData (var 1) (var 4) (var 7)))
        (ap2 logExponentF (var 0) (logExponentData (var 2) (var 4) (var 7)))
        (distanceBudget (var 0) (var 3) (var 5) (var 6) (var 7)) (var 6*unit (var 0))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (exponent_distance _ _ _ _ _ _ _ _
    hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))
theorem actual_mesh_exponent_continuity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) := closeUniv 8 (program_at _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaLogExponentContinuity
