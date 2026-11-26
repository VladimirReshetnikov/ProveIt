import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionDensity
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# An actual compact unit-substitution density sampler

The observations sum the original power at the exact exp(-t) chart
times the differences of the original decay observations. A computed
positive refinement of the original Euler mesh pays the quadratic cell
error. Its actual row query pays the accumulated observation errors.
The resulting PR2 is regular and agrees with the original compact Euler
name. Identification with integration on arbitrary rational unit meshes
is a separate reparametrization obligation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionCompactName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionDensity (density numerator denominator)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianEulerIntegrationByPartsGridObservation (rowCost)
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4 field5 mesh precision quadrature)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B a C E T : PTm n) : Fm PTm n := intervalSource z R B a C E T ⋏ le one C
def stage (p : PTm n) : PTm n := p+num 4
def refinement (p R C E T : PTm n) : PTm n := one+C+num 3*majorant R E T*C*C*unit (stage p)
def count (p R C E T : PTm n) : PTm n :=
  refinement p R C E T*mesh (stage p) (GaussianEulerCompactModulus.lipschitz R E T) T
def rowBudget (p R C E T : PTm n) : PTm n := num 20*majorant R E T*count p R C E T+T*rowCost R E T
def rowQuery (p R C E T : PTm n) : PTm n :=
  precision (stage p) T+GaussianFastValueCut.exponent (rowBudget p R C E T) (stage p)
def observation (p z R B a C E T : PTm n) : PTm n :=
  density (rowQuery p R C E T) (count p R C E T) z B a C E
def data (z R B a C E T : PTm n) : PTm n := sampleData z R B a C (pairT E T)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T : PTm n) :
    (source z R B a C E T).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [source]
@[simp] theorem subst_stage {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) : Syn.subst σ (stage p) = stage (Syn.subst σ p) := by simp [stage]
@[simp] theorem subst_refinement {m : ℕ} (σ : Fin n → PTm m) (p R C E T : PTm n) :
    Syn.subst σ (refinement p R C E T) = refinement (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [refinement]
@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (p R C E T : PTm n) :
    Syn.subst σ (count p R C E T) = count (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [count]
@[simp] theorem subst_rowBudget {m : ℕ} (σ : Fin n → PTm m) (p R C E T : PTm n) :
    Syn.subst σ (rowBudget p R C E T) = rowBudget (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [rowBudget]
@[simp] theorem subst_rowQuery {m : ℕ} (σ : Fin n → PTm m) (p R C E T : PTm n) :
    Syn.subst σ (rowQuery p R C E T) = rowQuery (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [rowQuery]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B a C E T : PTm n) :
    Syn.subst σ (observation p z R B a C E T) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [observation]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T : PTm n) :
    Syn.subst σ (data z R B a C E T) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [data]

private def body : PTm 8 := observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
def sampleF : PR 8 := PTm.toPR body
private def reader (p x : PTm n) : PTm n := PTm.app sampleF
  ![p,field0 x,field1 x,field2 x,field3 x,field4 x,fstT (field5 x),sndT (field5 x)]
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))

theorem sample_program (p z R B a C E T : PTm n) : Γ ⊢[PRAAx]
    PTm.app sampleF ![p,z,R,B,a,C,E,T] ≐ observation p z R B a C E T := by
  have decode : Syn.subst (![p,z,R,B,a,C,E,T] : Fin 8 → PTm n) body = observation p z R B a C E T := by
    simp only [body,subst_observation,Syn.subst_var]
    rfl
  simpa only [sampleF,decode] using toPR_eq (Γ := Γ) body ![p,z,R,B,a,C,E,T]

theorem name_at (p z R B a C E T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B a C E T) ≐ observation p z R B a C E T := by
  have program : Γ ⊢[PRAAx] ap2 nameF p (data z R B a C E T) ≐ reader p (data z R B a C E T) := by
    have decode : Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (reader (var 0) (var 1)) =
        reader p (data z R B a C E T) := by
      unfold reader
      change PTm.app _ _ = PTm.app _ _
      congr 1
      funext i
      fin_cases i
      · rfl
      · change Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (field0 (var 1)) = _
        simp
      · change Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (field1 (var 1)) = _
        simp
      · change Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (field2 (var 1)) = _
        simp
      · change Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (field3 (var 1)) = _
        simp
      · change Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (field4 (var 1)) = _
        simp
      · change Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (fstT (field5 (var 1))) = _
        simp
      · change Syn.subst (![p,data z R B a C E T] : Fin 2 → PTm n) (sndT (field5 (var 1))) = _
        simp
    simpa only [nameF,ap2,decode] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,data z R B a C E T]
  have fields : Γ ⊢[PRAAx] reader p (data z R B a C E T) ≐ PTm.app sampleF ![p,z,R,B,a,C,E,T] := by
    apply congrApp sampleF
    intro i
    fin_cases i
    · exact .eqRefl _
    · exact GaussianCompactRiemannName.field0_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field1_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field2_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field3_at _ _ _ _ _ _
    · exact GaussianCompactRiemannName.field4_at _ _ _ _ _ _
    · exact (congrFst (GaussianCompactRiemannName.field5_at _ _ _ _ _ _)).eqTrans (fst_pair E T)
    · exact (congrSnd (GaussianCompactRiemannName.field5_at _ _ _ _ _ _)).eqTrans (snd_pair E T)
  exact program.eqTrans (fields.eqTrans (sample_program p z R B a C E T))

theorem refinement_positive (p R C E T : PTm n) : Γ ⊢[PRAAx] le one (refinement p R C E T) :=
  le_trans (le_add_right one C) (le_add_right _ _)

theorem count_positive (p R C E T : PTm n) : Γ ⊢[PRAAx] le one (count p R C E T) :=
  positive_product _ _ (refinement_positive p R C E T) (GaussianCompactRiemannName.mesh_positive _ _ _)

theorem count_budget (p R C E T : PTm n) : Γ ⊢[PRAAx]
    le (num 3*majorant R E T*C*C*unit (stage p)) (count p R C E T) := by
  have base := GaussianCompactRiemannName.mesh_positive (Γ := Γ) (stage p) (GaussianEulerCompactModulus.lipschitz R E T) T
  have first : Γ ⊢[PRAAx] le (num 3*majorant R E T*C*C*unit (stage p)) (refinement p R C E T) := le_add_left _ _
  have last : Γ ⊢[PRAAx] le (refinement p R C E T) (count p R C E T) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (refinement p R C E T) base)
  exact le_trans first last

theorem finite_source (p z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionDensity.source z R B a C E T (count p R C E T) := by
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have base := GaussianCompactRiemannName.mesh_positive (Γ := Γ) (stage p) (GaussianEulerCompactModulus.lipschitz R E T) T
  have first : Γ ⊢[PRAAx] le C (refinement p R C E T) := le_trans (le_add_left C one) (le_add_right _ _)
  have last : Γ ⊢[PRAAx] le C (count p R C E T) := le_trans first
    (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (refinement p R C E T) base))
  have scaled : Γ ⊢[PRAAx] le C (E*count p R C E T) := le_trans last
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (count p R C E T) hE))
  exact .andI hs.andE₁ (.andI (count_positive _ _ _ _ _) (.andI hs.andE₂ scaled))

theorem finite_budget (p z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    le (numerator (rowQuery p R C E T) R E T C (count p R C E T)*unit (stage p))
      (two*denominator (rowQuery p R C E T) E (count p R C E T)) := by
  let N := count p R C E T
  let U := unit (rowQuery p R C E T)
  let P := unit (stage p)
  let K := majorant R E T
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have width : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left C a) hs.andE₁.andE₂.andE₂
  have curv : Γ ⊢[PRAAx] le (num 3*K*C*C*P) N := count_budget p R C E T
  have obs : Γ ⊢[PRAAx] le ((num 20*K*N+T*rowCost R E T)*P) U :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone (le_add_left _ _))
  have e2 : Γ ⊢[PRAAx] le one (E*E) := positive_product _ _ hE hE
  unfold numerator denominator
  ipra_le 𝔞(U)*sl curv+(𝔞(E)*𝔞(E)*𝔞(N))*sl obs+
    (𝔞(N)*𝔞(U))*sl e2+(𝔞(rowCost R E T)*𝔞(E)*𝔞(N)*𝔞(P))*sl width

theorem observation_to_old (p z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (observation p z R B a C E T)
      (ap2 GaussianEulerCompactAdditivity.nameF (stage p) (GaussianEulerCompactAdditivity.data z R B a C E T))
      (num 5) (unit (stage p)) := by
  let r := stage p
  let N := count p R C E T
  let s := rowQuery p R C E T
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hN := count_positive (Γ := Γ) p R C E T
  have hd := positive_product _ _ (positive_product _ _ (positive_product _ _ hE hE) hN) (unit_positive s)
  have finite := GaussianEulerUnitSubstitutionDensity.original_finite_bound s z R B a C E T N (finite_source p z R B a C E T hs)
  have first := distance_symmetric _ _ _ _ (unit_positive r)
    (distance_radius_mono _ _ _ _ two (unit r) hd (unit_positive r) (finite_budget p z R B a C E T hs) finite)
  have old := GaussianCompactMeshIndependence.arbitrary_refinement GaussianEulerIntegrandName.evaluatorF r s
    (refinement p R C E T) a C E (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B)
    (GaussianEulerCompactAdditivity.compact_input z R B a C E T hs.andE₁) (refinement_positive p R C E T) (le_add_right _ _)
  have grown : Γ ⊢[PRAAx] le (unit r) (unit (r+num 6)) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have second := distance_congr (.eqRefl _)
    (GaussianCompactRiemannName.name_at GaussianEulerIntegrandName.evaluatorF r a C E
      (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B)).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (num 3) (unit r) (unit_positive _) (unit_positive r) (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) grown)) old)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive r) first second)

theorem stage_budget (p : PTm n) : Γ ⊢[PRAAx] le (num 6*unit p) (unit (stage p)) := by
  have twoBit (r : PTm n) : Γ ⊢[PRAAx] unit (r+num 2) ≐ num 4*unit r :=
    (pw_add two r (num 2)).eqTrans ((congrMul (.eqRefl _) ((pw_succ two one).eqTrans
      (congrMul (pw_one two) (.eqRefl two)))).eqTrans (by dsimp only [unit]; ipra_ring))
  have four : Γ ⊢[PRAAx] unit (stage p) ≐ num 16*unit p :=
    (congrAp2 powF (by dsimp only [stage]; ipra_ring : Γ ⊢[PRAAx] stage p ≐ (p+num 2)+num 2) (.eqRefl two)).eqTrans
      ((twoBit (p+num 2)).eqTrans ((congrMul (.eqRefl _) (twoBit p)).eqTrans (by ipra_ring)))
  exact le_congr (.eqRefl _) four.eqSymm (le_of_eq_add (d := num 10*unit p) (by ipra_ring))

theorem original_observations (p q z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E T))
      (ap2 GaussianEulerCompactAdditivity.nameF q (GaussianEulerCompactAdditivity.data z R B a C E T))
      (unit p+unit q) (unit p*unit q) := by
  let r := stage p
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hr := unit_positive (Γ := Γ) r
  have first := distance_radius_mono _ _ _ _ (num 5*unit q) (unit r*unit q) hr (positive_product _ _ hr hq)
    (le_of_eq_add (d := zero) (by ipra_ring)) (observation_to_old p z R B a C E T hs)
  have second := GaussianNameEquivalence.point_at GaussianEulerCompactAdditivity.nameF
    (GaussianEulerCompactAdditivity.data z R B a C E T) r q (GaussianEulerCompactAdditivity.name_regular z R B a C E T hs.andE₁)
  have joined := distance_triangle_same _ _ _ _ _ _ (positive_product _ _ hr hq) first second
  apply distance_congr (name_at p z R B a C E T).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hr hq) (positive_product _ _ hp hq)
    (by ipra_le (𝔞(unit q)*𝔞(unit q))*sl (stage_budget (Γ := Γ) p)) joined

theorem original_compact_cross (z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianEulerCompactAdditivity.nameF (data z R B a C E T)
      (GaussianEulerCompactAdditivity.data z R B a C E T) := by
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) := by
    simpa [Fm.shift,Syn.shift] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,
    subst_data,GaussianEulerCompactAdditivity.subst_data,Syn.shift] using
    original_observations (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) ss

theorem name_regular (z R B a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B a C E T) := by
  have e := original_compact_cross z R B a C E T hs
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ e (GaussianNameEquivalence.cross_symm _ _ _ _ e)

theorem actual_original_unit_substitution_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent nameF GaussianEulerCompactAdditivity.nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (GaussianEulerCompactAdditivity.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (original_compact_cross _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_unit_substitution_density_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (name_regular _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionCompactName
