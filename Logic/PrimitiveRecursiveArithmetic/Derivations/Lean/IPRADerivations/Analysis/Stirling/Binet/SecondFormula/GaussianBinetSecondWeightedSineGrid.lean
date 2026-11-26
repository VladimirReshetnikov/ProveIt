import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondWeightedSinePoint
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondDecayGrid
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# The scheduled sine approximation on the actual frozen Bose grid

Every old physical tag is retained. The new body uses the same fixed
sine rectangle schedule for each tag, with its corresponding frozen
decay moved to the sine clock. The error is summed with the original
integration weight.
-/

set_option autoImplicit false
set_option maxHeartbeats 790000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineGrid

open_ipra
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetSecondWeightedSinePoint (point subst_point cost subst_cost)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field5
    field0_at field1_at field2_at field3_at field4_at field5_at
    subst_field0 subst_field1 subst_field2 subst_field3 subst_field4 subst_field5)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def parameters (X Y D sign R K : PTm n) : PTm n := pairT (pairT R K) (fixedData X Y D sign)

private def pointReader (q a b T H J x : PTm n) : PTm n :=
  let z := sndT x
  point q (fstT z) (fstT (sndT z)) (fstT (sndT (sndT z))) (sndT (sndT (sndT z))) a b
    (fstT (fstT x)) T (sndT (fstT x)) H J

private def term (i d : PTm n) : PTm n :=
  pointReader (field0 d) (field2 d*i) (field1 d) (field2 d) (field3 d) (field4 d) (field5 d)

def body : PTm 2 := term (var 0) (var 1)

def data (q M T H J X Y D sign R K : PTm n) : PTm n :=
  sampleData q M T H J (parameters X Y D sign R K)

def value (q M T H J X Y D sign R K : PTm n) : PTm n :=
  leftSum body M (data q M T H J X Y D sign R K) T one

ipra_subst parameters

@[simp] private theorem subst_pointReader {m : ℕ} (σ : Fin n → PTm m) (q a b T H J x : PTm n) :
    Syn.subst σ (pointReader q a b T H J x) =
      pointReader (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ T)
        (Syn.subst σ H) (Syn.subst σ J) (Syn.subst σ x) := by simp [pointReader]

ipra_subst data

ipra_subst value [one]

private theorem reader_at (q a b T H J X Y D sign R K : PTm n) :
    Γ ⊢[PRAAx] pointReader q a b T H J (parameters X Y D sign R K) ≐
      point q X Y D sign a b R T K H J := by
  let x := parameters X Y D sign R K
  let z := sndT x
  have z₀ : Γ ⊢[PRAAx] z ≐ fixedData X Y D sign := snd_pair _ _
  have z₁ := (congrSnd z₀).eqTrans (snd_pair X (pairT Y (pairT D sign)))
  have z₂ := (congrSnd z₁).eqTrans (snd_pair Y (pairT D sign))
  have r : Γ ⊢[PRAAx] fstT x ≐ pairT R K := fst_pair _ _
  have ex := (congrFst z₀).eqTrans (fst_pair X (pairT Y (pairT D sign)))
  have ey := (congrFst z₁).eqTrans (fst_pair Y (pairT D sign))
  have ed := (congrFst z₂).eqTrans (fst_pair D sign)
  have es := (congrSnd z₂).eqTrans (snd_pair D sign)
  have er := (congrFst r).eqTrans (fst_pair R K)
  have ek := (congrSnd r).eqTrans (snd_pair R K)
  have bind0 : Γ ⊢[PRAAx] point q (fstT z) (fstT (sndT z)) (fstT (sndT (sndT z))) (sndT (sndT (sndT z))) a b
      (fstT (fstT x)) T (sndT (fstT x)) H J ≐
      point q X (fstT (sndT z)) (fstT (sndT (sndT z))) (sndT (sndT (sndT z))) a b
      (fstT (fstT x)) T (sndT (fstT x)) H J := by
    simpa only [subst_point,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (point (Syn.shift q) (var 0) (Syn.shift (fstT (sndT z))) (Syn.shift (fstT (sndT (sndT z)))) (Syn.shift (sndT (sndT (sndT z)))) (Syn.shift a) (Syn.shift b)
      (Syn.shift (fstT (fstT x))) (Syn.shift T) (Syn.shift (sndT (fstT x))) (Syn.shift H) (Syn.shift J)) ex
  have bind1 : Γ ⊢[PRAAx] point q X (fstT (sndT z)) (fstT (sndT (sndT z))) (sndT (sndT (sndT z))) a b
      (fstT (fstT x)) T (sndT (fstT x)) H J ≐
      point q X Y (fstT (sndT (sndT z))) (sndT (sndT (sndT z))) a b
      (fstT (fstT x)) T (sndT (fstT x)) H J := by
    simpa only [subst_point,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (point (Syn.shift q) (Syn.shift X) (var 0) (Syn.shift (fstT (sndT (sndT z)))) (Syn.shift (sndT (sndT (sndT z)))) (Syn.shift a) (Syn.shift b)
      (Syn.shift (fstT (fstT x))) (Syn.shift T) (Syn.shift (sndT (fstT x))) (Syn.shift H) (Syn.shift J)) ey
  have bind2 : Γ ⊢[PRAAx] point q X Y (fstT (sndT (sndT z))) (sndT (sndT (sndT z))) a b
      (fstT (fstT x)) T (sndT (fstT x)) H J ≐
      point q X Y D (sndT (sndT (sndT z))) a b
      (fstT (fstT x)) T (sndT (fstT x)) H J := by
    simpa only [subst_point,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (point (Syn.shift q) (Syn.shift X) (Syn.shift Y) (var 0) (Syn.shift (sndT (sndT (sndT z)))) (Syn.shift a) (Syn.shift b)
      (Syn.shift (fstT (fstT x))) (Syn.shift T) (Syn.shift (sndT (fstT x))) (Syn.shift H) (Syn.shift J)) ed
  have bind3 : Γ ⊢[PRAAx] point q X Y D (sndT (sndT (sndT z))) a b
      (fstT (fstT x)) T (sndT (fstT x)) H J ≐
      point q X Y D sign a b
      (fstT (fstT x)) T (sndT (fstT x)) H J := by
    simpa only [subst_point,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (point (Syn.shift q) (Syn.shift X) (Syn.shift Y) (Syn.shift D) (var 0) (Syn.shift a) (Syn.shift b)
      (Syn.shift (fstT (fstT x))) (Syn.shift T) (Syn.shift (sndT (fstT x))) (Syn.shift H) (Syn.shift J)) es
  have bind4 : Γ ⊢[PRAAx] point q X Y D sign a b
      (fstT (fstT x)) T (sndT (fstT x)) H J ≐
      point q X Y D sign a b
      R T (sndT (fstT x)) H J := by
    simpa only [subst_point,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (point (Syn.shift q) (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift a) (Syn.shift b)
      (var 0) (Syn.shift T) (Syn.shift (sndT (fstT x))) (Syn.shift H) (Syn.shift J)) er
  have bind5 : Γ ⊢[PRAAx] point q X Y D sign a b
      R T (sndT (fstT x)) H J ≐
      point q X Y D sign a b
      R T K H J := by
    simpa only [subst_point,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (point (Syn.shift q) (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift a) (Syn.shift b)
      (Syn.shift R) (Syn.shift T) (var 0) (Syn.shift H) (Syn.shift J)) ek
  exact bind0.eqTrans (bind1.eqTrans (bind2.eqTrans (bind3.eqTrans (bind4.eqTrans bind5))))

theorem row_at (i q M T H J X Y D sign R K : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (data q M T H J X Y D sign R K) ≐
      point q X Y D sign (T*i) M R T K H J := by
  let x := parameters X Y D sign R K
  let d := data q M T H J X Y D sign R K
  have read : inst2 body i d =
      pointReader (field0 d) (field2 d*i) (field1 d) (field2 d) (field3 d) (field4 d) (field5 d) := by
    simp only [body,term,inst2,subst_pointReader,subst_field0,subst_field1,subst_field2,subst_field3,
      subst_field4,subst_field5,Syn.subst_var,PTm.subst_mul,Matrix.cons_val_zero,Matrix.cons_val_one]
  let e : Fin 7 → PTm n := ![field0 d,field2 d*i,field1 d,field2 d,field3 d,field4 d,field5 d]
  let f : Fin 7 → PTm n := ![q,T*i,M,T,H,J,x]
  let schema : PTm 7 := pointReader (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
  have raw := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) schema (σ := e) (σ' := f) (fun j => by
    fin_cases j
    · exact field0_at _ _ _ _ _ _
    · exact congrMul (field2_at _ _ _ _ _ _) (.eqRefl i)
    · exact field1_at _ _ _ _ _ _
    · exact field2_at _ _ _ _ _ _
    · exact field3_at _ _ _ _ _ _
    · exact field4_at _ _ _ _ _ _
    · exact field5_at _ _ _ _ _ _)
  have left : Syn.subst e schema =
      pointReader (field0 d) (field2 d*i) (field1 d) (field2 d) (field3 d) (field4 d) (field5 d) := by
    dsimp only [schema]
    rw [subst_pointReader]
    rfl
  have right : Syn.subst f schema = pointReader q (T*i) M T H J x := by
    dsimp only [schema]
    rw [subst_pointReader]
    rfl
  rw [left,right] at raw
  rw [read]
  exact raw.eqTrans (reader_at q (T*i) M T H J X Y D sign R K)

private theorem grid_cell_error (i q M T H J X Y D sign R K : PTm n)
    (z : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le one M)
    (hJ : Γ ⊢[PRAAx] le one J) (hK : Γ ⊢[PRAAx] le D (K*X)) (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 GaussianBinetSecondDecayGrid.rowBody i (GaussianBinetSecondDecayGrid.rowData q M T H J X Y D sign))
      (inst2 body i (data q M T H J X Y D sign R K)) (cost K T) (unit q) := by
  have time : Γ ⊢[PRAAx] le (T*i) (M*T) :=
    le_congr (mul_comm i T) (.eqRefl _) (le_mul_mono (le_of_lt hi) (le_refl T))
  exact distance_congr (GaussianBinetSecondDecayGrid.row_at i q M T H J X Y D sign).eqSymm
    (row_at i q M T H J X Y D sign R K).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBinetSecondWeightedSinePoint.point_error q X Y D sign (T*i) M R T K H J z hm time hK hJ)

theorem grid_error (q M T H J X Y D sign R K : PTm n)
    (z : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le one M)
    (hJ : Γ ⊢[PRAAx] le one J) (hK : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetSecondDecayGrid.value q M T H J X Y D sign)
      (value q M T H J X Y D sign R K) (T*cost K T) (unit q) := by
  let f := GaussianBinetSecondDecayGrid.rowBody
  let x := GaussianBinetSecondDecayGrid.rowData q M T H J X Y D sign
  let y := data q M T H J X Y D sign R K
  have rows : Γ ⊢[PRAAx] termsDistance f body M x y (cost K T) (unit q) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    have hz : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) :=
      by simpa [Δ,s,Fm.shift,Syn.shift] using z.shift.wk
    have hms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hm.shift.wk
    have hjs : Δ ⊢[PRAAx] le one (s J) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hJ.shift.wk
    have hks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    simpa only [f,x,y,s,Δ,Syn.shift,GaussianBinetSecondDecayGrid.subst_rowData,subst_data,subst_cost,
      GaussianCoefficientNameBounds.subst_unit] using
      grid_cell_error (var 0) (s q) (s M) (s T) (s H) (s J) (s X) (s Y) (s D) (s sign) (s R) (s K)
        hz hms hjs hks Prf.hyp0
  have raw := GaussianCompactScalarMajorant.common_mesh_distance f body M x y T one (cost K T) (unit q)
    hm (le_refl one) (unit_positive q) rows
  exact distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (one_mul _) raw

theorem actual_second_Binet_frozen_grid_sine_substitution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (let q := var 0
     let M := var 1
     let T := var 2
     let H := var 3
     let J := var 4
     let X := var 5
     let Y := var 6
     let D := var 7
     let sign := var 8
     let R := var 9
     let K := var 10
     (source X Y D sign R ⋏ le one M) ⋏ (le one J ⋏ le D (K*X)) ⟶
       distanceBounded (GaussianBinetSecondDecayGrid.value q M T H J X Y D sign)
         (value q M T H J X Y D sign R K) (T*cost K T) (unit q)) :=
  closeUniv 11 (.impI (grid_error _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineGrid
