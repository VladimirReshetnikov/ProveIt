import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactorShift
import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactorShiftAlgebra

/-!
# The literal prefactor difference has the expected exponent

Compare both actual names with their rational expressions at one
observation clock. The exact polynomial calculation transfers to
independent observations of the original Stirling and Euler names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorShiftBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalPrefactor (negativeHalf quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorShift (differenceF differenceData difference_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_fast sum_distance product_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd qmul ofGaussian)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative)
open GaussianRationalReciprocal (bound_congr bounded_sum bounded_product bounded_difference)
open GaussianBarnesCanonicalCorrectionShift (halfShift)
open GaussianGammaEulerHeadLower (translated)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianStirlingConstant.nameF
local notation "G" => quadraticCoefficientF
local notation "C" => constantF

abbrev correctionF : PR 2 := addF C (multiplyF C G)
def correctionData (z B : PTm n) : PTm n :=
  addData negativeHalf (multiplyData C G (qnegative (halfShift z B)) quadraticCoefficientData)
abbrev nameF : PR 2 := addF S correctionF
def data (z B : PTm n) : PTm n := addData (GaussianStirlingConstant.nameData zero) (correctionData z B)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (data z B) = data (Syn.subst σ z) (Syn.subst σ B) := by
  simp [data,correctionData,quadraticCoefficientData,negativeHalf,one,two]

@[simp] private theorem subst_original_data {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (differenceData z B) = differenceData (Syn.subst σ z) (Syn.subst σ B) := by
  simp [GaussianBarnesCanonicalPrefactorShift.differenceData,GaussianBarnesCanonicalPrefactorShift.exponentData,
    GaussianBarnesCanonicalPrefactor.linearData,GaussianBarnesCanonicalPrefactor.correctionData,
    GaussianBarnesCanonicalPrefactor.polynomialData,GaussianBarnesCanonicalPrefactor.quadraticData,
    quadraticCoefficientData,negativeHalf,one,two]

theorem regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data z B) :=
  add_fast _ _ _ _ (GaussianStirlingConstant.name_regular zero) (add_fast _ _ _ _ (constant_regular _)
    (multiply_fast _ _ _ _ (constant_regular _) quadratic_coefficient_regular))

private structure Observation (Γ : List (Fm PTm n)) where
  f : PR 2
  x : PTm n
  value : PTm n → PTm n
  cost : PTm n
  radius : PTm n
  reg : Γ ⊢[PRAAx] pointCN f x
  close (p : PTm n) : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (value p) cost (unit p)
  bound (p : PTm n) : Γ ⊢[PRAAx] bounded (value p) radius one

private def leaf (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Observation Γ where
  f := f
  x := x
  value p := ap2 f p x
  cost := zero
  radius := U f x
  reg := h
  close p := GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive p)
  bound p := sample_bound f x p h

private def const (a : PTm n) : Observation Γ where
  f := C
  x := a
  value _ := a
  cost := zero
  radius := U C a
  reg := constant_regular _
  close p := distance_congr (constant_at p a).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero a _ (unit_positive p))
  bound p := bound_congr (constant_at p a) (.eqRefl _) (.eqRefl _) (sample_bound C a p (constant_regular _))

private def sum (a b : Observation Γ) : Observation Γ where
  f := addF a.f b.f
  x := addData a.x b.x
  value p := qadd (a.value p) (b.value p)
  cost := GaussianNameRingLaws.three+(a.cost+b.cost)
  radius := a.radius+b.radius
  reg := add_fast _ _ _ _ a.reg b.reg
  close p := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (GaussianNameRingLaws.add_sample_error _ _ _ _ p a.reg b.reg)
    (sum_distance _ _ _ _ _ _ _ (unit_positive p) (a.close p) (b.close p))
  bound p := bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) (a.bound p) (b.bound p))

private def product (a b : Observation Γ) : Observation Γ where
  f := multiplyF a.f b.f
  x := multiplyData a.f b.f a.x b.x
  value p := qmul (a.value p) (b.value p)
  cost := (multiplyModulus a.f b.f a.x b.x+one)+(a.cost*U b.f b.x+a.radius*b.cost)
  radius := a.radius*b.radius
  reg := multiply_fast _ _ _ _ a.reg b.reg
  close p := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (GaussianNameRingLaws.multiply_sample_error _ _ _ _ p a.reg b.reg)
    (product_distance _ _ _ _ _ _ _ _ _ (unit_positive p) (a.close p) (b.close p)
      (sample_bound b.f b.x p b.reg) (a.bound p))
  bound p := bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) (a.bound p) (b.bound p))

private def difference (a b : Observation Γ) : Observation Γ where
  f := GaussianNamedDifference.nameF a.f b.f
  x := GaussianNamedDifference.data a.x b.x
  value p := qsub (a.value p) (b.value p)
  cost := num 6+(a.cost+b.cost)
  radius := a.radius+b.radius
  reg := GaussianNamedDifference.name_regular _ _ _ _ a.reg b.reg
  close p := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (GaussianNamedDifference.sample_error _ _ _ _ p a.reg b.reg)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive p) (a.close p) (b.close p))
  bound p := bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) (a.bound p) (b.bound p))

private def stirling : Observation Γ := leaf S (GaussianStirlingConstant.nameData zero) (GaussianStirlingConstant.name_regular zero)
private def gammaCoefficient : Observation Γ := leaf G quadraticCoefficientData quadratic_coefficient_regular

private def original (z B : PTm n) : Observation Γ :=
  let a := const (Γ := Γ) (ofGaussian z B)
  sum (product a stirling) (product (const negativeHalf) (sum a
    (product (const (qmul (ofGaussian z B) (ofGaussian z B))) gammaCoefficient)))

private def shifted (z B : PTm n) : Observation Γ :=
  sum stirling (sum (const negativeHalf) (product (const (qnegative (halfShift z B))) gammaCoefficient))

private def cost (z B : PTm n) : PTm n :=
  (difference (original (translated z B one) B) (original z B) (Γ := Γ)).cost+(shifted (Γ := Γ) z B).cost

@[simp] private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) {Δ : List (Fm PTm m)} (z B : PTm n) :
    Syn.subst σ (cost (Γ := Γ) z B) = cost (Γ := Δ) (Syn.subst σ z) (Syn.subst σ B) := by
  simp [cost,original,shifted,leaf,const,sum,product,difference,stirling,gammaCoefficient,negativeHalf,one,two,
    GaussianNameRingLaws.three,quadraticCoefficientData]

private theorem original_observation (p z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 differenceF p (differenceData z B)) (ap2 nameF p (data z B)) (cost (Γ := Γ) z B) (unit p) := by
  let left := difference (original (translated z B one) B) (original z B) (Γ := Γ)
  let right := shifted (Γ := Γ) z B
  have realS := GaussianSignedNameExponentialOrder.real_sample_at (Γ := Γ) S (GaussianStirlingConstant.nameData zero) p
    (GaussianStirlingConstant.name_real zero)
  have eq : Γ ⊢[PRAAx] left.value p ≐ right.value p :=
    GaussianBarnesCanonicalPrefactorShiftAlgebra.exponent_shift z B _ _ hB realS.andE₁
  exact GaussianNameRingLaws.through_identity _ _ _ _ _ _ _ (unit_positive p) (left.close p) (right.close p) eq

theorem difference_cross (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent differenceF nameF (differenceData z B) (data z B) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost (Γ := Γ) z B)
    (difference_regular z B) (regular z B) (.allI ?_)
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,Δ,one] using hB.shift
  have cs := subst_cost (Γ := Γ) (Δ := Δ) (fun i => var i.succ) z B
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_original_data,subst_data,cs,Syn.shift,Δ] using
    original_observation (var 0) (Syn.shift z) (Syn.shift B) h

theorem actual_Barnes_prefactor_named_exponent_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent differenceF nameF (differenceData (var 0) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (difference_cross _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorShiftBinding
