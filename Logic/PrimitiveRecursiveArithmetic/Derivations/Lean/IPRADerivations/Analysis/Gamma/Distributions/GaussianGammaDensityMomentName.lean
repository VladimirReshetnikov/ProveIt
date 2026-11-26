import IPRADerivations.Analysis.Gamma.Distributions.GaussianGammaDensityMomentGrid

/-!
# Actual normalized Gamma-density integer moment names

The computed observations are literal finite t^N times base-density
Euler sums, normalized by one original C7 observation. Their original
cofinal shifted cutoffs and computed queries are those of the checked
grid module. Finite comparison proves actual regularity and the exact
rising-factorial value for every internal N, including zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDensityMomentName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source)
open GaussianGammaDensityMomentGrid (stage outer observation)
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_at)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "Ref" => GaussianGammaDensityMomentReference.nameF

def data (z R B A N : PTm n) : PTm n := sampleData z R B A N zero
private def body : PTm 6 := observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
def sampleF : PR 6 := PTm.toPR body
private def reader (p d : PTm n) : PTm n := PTm.app sampleF ![p,field0 d,field1 d,field2 d,field3 d,field4 d]
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B A N : PTm n) :
    Syn.subst σ (data z R B A N) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [data]
private theorem subst_reader {m : ℕ} (σ : Fin n → PTm m) (p d : PTm n) :
    Syn.subst σ (reader p d) = reader (Syn.subst σ p) (Syn.subst σ d) := by
  unfold reader
  change PTm.app _ _ = PTm.app _ _
  congr 1
  funext i
  fin_cases i
  · rfl
  · change Syn.subst σ (field0 d) = field0 (Syn.subst σ d)
    simp
  · change Syn.subst σ (field1 d) = field1 (Syn.subst σ d)
    simp
  · change Syn.subst σ (field2 d) = field2 (Syn.subst σ d)
    simp
  · change Syn.subst σ (field3 d) = field3 (Syn.subst σ d)
    simp
  · change Syn.subst σ (field4 d) = field4 (Syn.subst σ d)
    simp

theorem sample_program (p z R B A N : PTm n) : Γ ⊢[PRAAx]
    PTm.app sampleF ![p,z,R,B,A,N] ≐ observation p z R B A N := by
  have decode : Syn.subst (![p,z,R,B,A,N] : Fin 6 → PTm n) body = observation p z R B A N := by
    simp only [body,GaussianGammaDensityMomentGrid.subst_observation,Syn.subst_var]
    rfl
  simpa only [sampleF,decode] using toPR_eq (Γ := Γ) body ![p,z,R,B,A,N]

theorem name_at (p z R B A N : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A N) ≐ observation p z R B A N := by
  have program : Γ ⊢[PRAAx] ap2 nameF p (data z R B A N) ≐ reader p (data z R B A N) := by
    simpa only [nameF,ap2,subst_reader,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,data z R B A N]
  have fields : Γ ⊢[PRAAx] reader p (data z R B A N) ≐ PTm.app sampleF ![p,z,R,B,A,N] := by
    apply congrApp sampleF
    intro i
    fin_cases i
    · exact .eqRefl _
    · exact GaussianCompactRiemannName.field0_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field1_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field2_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field3_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field4_at _ _ _ _ _ _
  exact program.eqTrans (fields.eqTrans (sample_program p z R B A N))

theorem stage_budget (p : PTm n) : Γ ⊢[PRAAx] le (two*unit p) (unit (stage p)) := by
  have later : Γ ⊢[PRAAx] le (succ p) (stage p) := by dsimp only [stage]; ipra_le 1
  exact le_congr ((pw_succ two p).eqTrans (mul_comm _ _)) (.eqRefl _)
    (GaussianExponentialReference.unit_monotone later)

theorem original_reference_observations (p q z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A N))
      (ap2 Ref q (GaussianGammaDensityMomentReference.data z R B A N)) (unit p+unit q) (unit p*unit q) := by
  let S := unit (stage p)
  let O := unit (outer p R)
  let Q := unit q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hs := unit_positive (Γ := Γ) (stage p)
  have ho := unit_positive (Γ := Γ) (outer p R)
  have hden := positive_product _ _ hs hq
  have grown := GaussianExponentialReference.unit_monotone (Γ := Γ) (GaussianGammaDensityMomentGrid.outer_late p R)
  have first := distance_radius_mono _ _ _ _ Q (S*Q) hs hden (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianGammaDensityMomentGrid.observation_to_reference p z R B A N h)
  have second := distance_radius_mono _ _ _ _ (S+Q) (S*Q) (positive_product _ _ ho hq) hden
    (by ipra_le (𝔞 Q*𝔞 Q)*sl grown)
    (GaussianNameEquivalence.point_at Ref (GaussianGammaDensityMomentReference.data z R B A N) (outer p R) q
      (GaussianGammaDensityMomentReference.name_regular z R B A N h))
  have joined := distance_triangle_same _ _ _ _ _ _ hden first second
  exact distance_congr (name_at p z R B A N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hden (positive_product _ _ hp hq)
      (by ipra_le (𝔞 Q*𝔞 Q)*sl (stage_budget (Γ := Γ) p)) joined)

theorem original_reference_cross (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF Ref (data z R B A N) (GaussianGammaDensityMomentReference.data z R B A N) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,
    subst_data,GaussianGammaDensityMomentReference.subst_data,Syn.shift] using
    original_reference_observations (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N)) hs

theorem name_regular (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B A N) := by
  have e := original_reference_cross z R B A N h
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem original_integer_moment (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaCanonicalExponent.constantF (data z R B A N)
      (GaussianGammaRepeatedShift.risingProduct z B N) :=
  cross_trans _ _ _ _ _ _ (original_reference_cross z R B A N h)
    (GaussianGammaDensityMomentReference.original_value z R B A N h)

theorem original_observations (p q z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A N))
      (ap2 GaussianGammaCanonicalExponent.constantF q (GaussianGammaRepeatedShift.risingProduct z B N))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_integer_moment z R B A N h)

theorem actual_original_Gamma_density_integer_moment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF GaussianGammaCanonicalExponent.constantF
      (data (var 0) (var 1) (var 2) (var 3) (var 4)) (GaussianGammaRepeatedShift.risingProduct (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (original_integer_moment _ _ _ _ _ Prf.hyp0))
theorem actual_original_Gamma_density_integer_moment_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (name_regular _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDensityMomentName
