import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinDampedPoint

/-!
# Finite Euler scaling quadratures on a Mellin strip

Every transposed Mellin row compares to the original damped Euler
quadrature at scale (j+1)/1. A common observation choice pays for all
decay indices and leaves the finite geometric tail explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedStrip

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature
  field0 field1 field2 field3 field4 field5 field0_at field1_at field2_at field3_at field4_at field5_at)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianEulerPositiveScalingIntegrand (evaluatorF fixedData sample)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaZetaMellinDampedPoint (cost point_error)
open GaussianGammaZetaMellinDecayPrefix (errorNumerator errorDenominator)
open GaussianGammaZetaMellinStrip (window mellinValue tag_domain)
open GaussianGammaZetaMellinTranspose (matrix decay_index_cell decay_index_at transposedBody transposedData transposedValue)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum)
open GaussianRationalFubini (rowBody)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "parameterSource" => GaussianEulerExponentCompactBounds.source
local notation "stripData" => GaussianGammaZetaMellinStrip.data

def dampedRow (j q z D M A C E : PTm n) : PTm n :=
  quadrature evaluatorF q M A C E (fixedData z D (succ j) one)

def dampedBody : PTm 2 :=
  let d : PTm 2 := var 1
  dampedRow (var 0) (field0 d) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))
    (field1 d) (field2 d) (field3 d) (field4 d)

def dampedValue (q z D M N A C E : PTm n) : PTm n := sum dampedBody N (stripData q z D M N A C E)

def totalNumerator (h H N R T C : PTm n) : PTm n :=
  C*(majorant R H T*((H*H)*unit h)+(majorant R H T+cost R H T)*(H+N))

@[simp] theorem subst_dampedRow {m : ℕ} (σ : Fin n → PTm m) (j q z D M A C E : PTm n) :
    Syn.subst σ (dampedRow j q z D M A C E) =
      dampedRow (Syn.subst σ j) (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ D)
        (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [dampedRow,one]

@[simp] theorem subst_dampedValue {m : ℕ} (σ : Fin n → PTm m) (q z D M N A C E : PTm n) :
    Syn.subst σ (dampedValue q z D M N A C E) =
      dampedValue (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ N)
        (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [dampedValue]

@[simp] theorem subst_totalNumerator {m : ℕ} (σ : Fin n → PTm m) (h H N R T C : PTm n) :
    Syn.subst σ (totalNumerator h H N R T C) =
      totalNumerator (Syn.subst σ h) (Syn.subst σ H) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ T) (Syn.subst σ C) := by
  simp [totalNumerator,majorant,GaussianEulerCompactPowerMajorant.exponentRadius,one]

theorem damped_index_at (j q z D M N A C E : PTm n) :
    Γ ⊢[PRAAx] inst2 dampedBody j (stripData q z D M N A C E) ≐ dampedRow j q z D M A C E := by
  let d := stripData q z D M N A C E
  have raw : inst2 dampedBody j d = dampedRow j (field0 d) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))
      (field1 d) (field2 d) (field3 d) (field4 d) := by simp [dampedBody,inst2]
  rw [raw]
  let code : PTm 8 := dampedRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
  let x : Fin 8 → PTm n := ![j,field0 d,fstT (sndT (field5 d)),sndT (sndT (field5 d)),field1 d,field2 d,field3 d,field4 d]
  let y : Fin 8 → PTm n := ![j,q,z,D,M,A,C,E]
  have hp : Γ ⊢[PRAAx] field5 d ≐ pairT N (pairT z D) := field5_at _ _ _ _ _ _
  have hd := (congrSnd hp).eqTrans (snd_pair N (pairT z D))
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) code (σ := x) (σ' := y) (fun s => by
    fin_cases s
    · exact .eqRefl j
    · exact field0_at _ _ _ _ _ _
    · exact (congrFst hd).eqTrans (fst_pair _ _)
    · exact (congrSnd hd).eqTrans (snd_pair _ _)
    · exact field1_at _ _ _ _ _ _
    · exact field2_at _ _ _ _ _ _
    · exact field3_at _ _ _ _ _ _
    · exact field4_at _ _ _ _ _ _)
  have left : Syn.subst x code = dampedRow j (field0 d) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))
      (field1 d) (field2 d) (field3 d) (field4 d) := by
    dsimp only [code]
    rw [subst_dampedRow]
    rfl
  have right : Syn.subst y code = dampedRow j q z D M A C E := by
    dsimp only [code]
    rw [subst_dampedRow]
    rfl
  rw [left,right] at read
  exact read

theorem grid_cell_error (j i p q z R D M N A C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (hw : Γ ⊢[PRAAx] window A C E H T)
    (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] le i M) (hq : Γ ⊢[PRAAx] le q p) :
    Γ ⊢[PRAAx] distanceBounded (inst2 (rowBody matrix) i (pairT j (stripData p z D M N A C E)))
      (inst2 (sampleBody evaluatorF) i (sampleData q M A C E (fixedData z D (succ j) one)))
      (cost R H T) (unit q) := by
  have right : Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) i (sampleData q M A C E (fixedData z D (succ j) one)) ≐
      sample q z D (A*M+C*i) (E*M) (succ j) one :=
    sample_body_at evaluatorF i q M A C E (fixedData z D (succ j) one)
  exact distance_congr (decay_index_cell j i p z D M N A C E).eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (point_error j p q z R D (A*M+C*i) (E*M) H T hz (tag_domain i M A C E H T hw hM hi) hq)

theorem decay_index_error (j p q z R D M N A C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (hw : Γ ⊢[PRAAx] window A C E H T)
    (hM : Γ ⊢[PRAAx] le one M) (hq : Γ ⊢[PRAAx] le q p) :
    Γ ⊢[PRAAx] distanceBounded (inst2 transposedBody j (transposedData p z D M N A C E))
      (dampedRow j q z D M A C E) (C*cost R H T) (E*unit q) := by
  let f := rowBody matrix
  let g := sampleBody evaluatorF
  let x := pairT j (stripData p z D M N A C E)
  let y := sampleData q M A C E (fixedData z D (succ j) one)
  have cells : Γ ⊢[PRAAx] termsDistance f g M x y (cost R H T) (unit q) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] parameterSource (s z) (s R) (s D) (s H) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ws : Δ ⊢[PRAAx] window (s A) (s C) (s E) (s H) (s T) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hw.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift.wk
    have qs : Δ ⊢[PRAAx] le (s q) (s p) := by simpa [Δ,s,Fm.shift,Syn.shift] using hq.shift.wk
    simpa only [Δ,s,x,y,f,g,Syn.shift,subst_pairT,GaussianGammaZetaMellinStrip.subst_data,
      GaussianCompactRiemannName.subst_sampleData,GaussianEulerPositiveScalingIntegrand.subst_fixedData,
      GaussianGammaZetaMellinDampedPoint.subst_cost,GaussianCoefficientNameBounds.subst_unit,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      grid_cell_error (s j) (var 0) (s p) (s q) (s z) (s R) (s D) (s M) (s N) (s A) (s C) (s E)
        (s H) (s T) zs ws ms (le_of_lt Prf.hyp0) qs
  have raw := GaussianCompactScalarMajorant.common_mesh_distance f g M x y C E (cost R H T) (unit q)
    hM hw.andE₁.andE₂ (unit_positive q) cells
  exact distance_congr (decay_index_at j p z D M N A C E).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

theorem quadrature_error (p q z R D M N A C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (hw : Γ ⊢[PRAAx] window A C E H T)
    (hM : Γ ⊢[PRAAx] le one M) (hq : Γ ⊢[PRAAx] le q p) :
    Γ ⊢[PRAAx] distanceBounded (transposedValue p z D M N A C E) (dampedValue q z D M N A C E)
      (N*(C*cost R H T)) (E*unit q) := by
  let x := transposedData p z D M N A C E
  let y := stripData q z D M N A C E
  have rows : Γ ⊢[PRAAx] termsDistance transposedBody dampedBody N x y (C*cost R H T) (E*unit q) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N)::Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] parameterSource (s z) (s R) (s D) (s H) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ws : Δ ⊢[PRAAx] window (s A) (s C) (s E) (s H) (s T) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hw.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift.wk
    have qs : Δ ⊢[PRAAx] le (s q) (s p) := by simpa [Δ,s,Fm.shift,Syn.shift] using hq.shift.wk
    have left := decay_index_error (var 0) (s p) (s q) (s z) (s R) (s D) (s M) (s N) (s A) (s C) (s E)
      (s H) (s T) zs ws ms qs
    have right := damped_index_at (Γ := Δ) (var 0) (s q) (s z) (s D) (s M) (s N) (s A) (s C) (s E)
    simpa only [Δ,s,x,y,Syn.shift,GaussianGammaZetaMellinTranspose.subst_transposedData,GaussianGammaZetaMellinStrip.subst_data,
      GaussianGammaZetaMellinDampedPoint.subst_cost,GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul] using
      distance_congr (.eqRefl _) right.eqSymm (.eqRefl _) (.eqRefl _) left
  exact sum_distance _ _ N x y _ _ (positive_product _ _ hw.andE₁.andE₂ (unit_positive q)) rows

/-- The geometric cutoff and dyadic precision can be chosen independently.
The common Euler observation is late enough for all retained indices. -/
theorem scheduled_error (h z R D M N A C E H T : PTm n)
    (hz : Γ ⊢[PRAAx] parameterSource z R D H) (hw : Γ ⊢[PRAAx] window A C E H T)
    (hM : Γ ⊢[PRAAx] le one M) :
    let q := exponent N h
    let p := GaussianGammaZetaMellinStrip.clock q M N A C E
    Γ ⊢[PRAAx] distanceBounded (mellinValue p z D M N A C E) (dampedValue q z D M N A C E)
      (totalNumerator h H N R T C) (E*errorDenominator h H N) := by
  let q := exponent N h
  let p := GaussianGammaZetaMellinStrip.clock q M N A C E
  let P := majorant R H T
  let K := cost R H T
  let V := E*errorDenominator h H N
  let X := GaussianGammaZetaMellinStrip.gridBudget M N A C E
  have hq : Γ ⊢[PRAAx] le h q := le_add_right _ _
  have hp : Γ ⊢[PRAAx] le q p := le_add_right _ _
  have hX : Γ ⊢[PRAAx] le (X*unit h) (unit p) :=
    le_trans (le_mul_mono (le_refl X) (GaussianExponentialReference.unit_monotone hq)) (query_budget X q)
  have hE := hw.andE₁.andE₂
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ hE
    (positive_product _ _ (le_trans hz.andE₂.andE₁ (le_add_right H N)) (unit_positive h))
  have original := GaussianGammaZetaMellinStrip.quadrature_error p h z R D M N A C E H T hz hw hM hX
  have first := distance_symmetric _ _ _ V hV original
  have raw := quadrature_error p q z R D M N A C E H T hz hw hM hp
  have budget : Γ ⊢[PRAAx] le ((N*(C*K))*V) ((C*K*(H+N))*(E*unit q)) := by
    have later : Γ ⊢[PRAAx] le (N*unit h) (unit q) := query_budget N h
    dsimp only [V,errorDenominator]
    ipra_le 𝔞(C*K*E*(H+N))*sl later
  have last := distance_radius_mono _ _ _ _ (C*K*(H+N)) V (positive_product _ _ hE (unit_positive q)) hV budget
    (distance_congr (GaussianGammaZetaMellinTranspose.transpose p z D M N A C E).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) raw)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [totalNumerator,errorNumerator,P,K]; ipra_ring) (.eqRefl V)
    (distance_triangle_same _ _ _ _ _ _ hV first last)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedStrip
