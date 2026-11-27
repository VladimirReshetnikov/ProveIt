import IPRADerivations.Analysis.Euler.ExponentialSubstitution.LogarithmicGrids.GaussianEulerExponentialLogCell
import IPRADerivations.Analysis.Euler.ExponentialSubstitution.Kernels.GaussianEulerExponentialSubstitutionCompactBound

/-!
# The finite logarithmic image grid of the original Euler quadrature

Each actual row uses the original logarithm difference between consecutive
affine nodes and the actual exponential substitution value at the left
node. Comparison with the original Euler quadrature is quantitative in
the number of cells and in the queried dyadic precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogGrid

open_ipra
open GaussianEulerExponentialLogCell (imageCell)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData field0 field1 field2 field3 field4 field5)
open GaussianRationalFiniteSum (sum multiplyBody sum_multiply multiply_body_at)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight)
open GaussianUniformFiniteSumBound (summandsBounded summand_bound_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalReciprocal (bound_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev imageData (p z B N a C E : PTm n) : PTm n := sampleData p N a C E (GaussianEulerIntegrandName.fixedData z B)
def imageRow (i y : PTm n) : PTm n :=
  imageCell (field0 y) (fstT (field5 y)) (sndT (field5 y))
    (field2 y*field1 y+field3 y*i) (field4 y*field1 y) (field3 y)
def imageBody : PTm 2 := imageRow (var 0) (var 1)
def imageSum (p z B N a C E : PTm n) : PTm n := sum imageBody N (imageData p z B N a C E)
def valueBounds (p z B N a C E M : PTm n) : Fm PTm n :=
  summandsBounded (sampleBody GaussianEulerExponentialSubstitutionIntegrand.evaluatorF) N
    (sampleData p N a C E (GaussianEulerExponentialSubstitutionIntegrand.fixedData z B)) M one
def source (p z B N a C E T M : PTm n) : Fm PTm n :=
  le one B ⋏ (le one a ⋏ (le one E ⋏ (le one N ⋏ (le (a+C) (E*T) ⋏ valueBounds p z B N a C E M))))
def observationCost (C T M : PTm n) : PTm n := two*M+C*(one+T)
def rowNumerator (p N C T M : PTm n) : PTm n := M*C*C*unit p+observationCost C T M*(N*N)
def rowDenominator (p N : PTm n) : PTm n := (N*N)*unit p

ipra_subst imageRow
ipra_subst imageSum
ipra_subst valueBounds
ipra_subst source
ipra_subst rowNumerator [observationCost]
ipra_subst rowDenominator

/-- The two logarithmic image grids read the same six cell coordinates. -/
theorem image_cell_congr (f : PTm 6) (i p z B N a C E : PTm n) :
    let y := imageData p z B N a C E
    Γ ⊢[PRAAx] Syn.subst ![field0 y,fstT (field5 y),sndT (field5 y),
      field2 y*field1 y+field3 y*i,field4 y*field1 y,field3 y] f ≐ Syn.subst ![p,z,B,a*N+C*i,E*N,C] f := by
  let x := GaussianEulerIntegrandName.fixedData z B
  let y := imageData p z B N a C E
  let args : Fin 6 → PTm n := ![field0 y,fstT (field5 y),sndT (field5 y),field2 y*field1 y+field3 y*i,field4 y*field1 y,field3 y]
  let vals : Fin 6 → PTm n := ![p,z,B,a*N+C*i,E*N,C]
  have time := GaussianCompactRiemannName.field1_at (Γ := Γ) p N a C E x
  have left := GaussianCompactRiemannName.field2_at (Γ := Γ) p N a C E x
  have width := GaussianCompactRiemannName.field3_at (Γ := Γ) p N a C E x
  have den := GaussianCompactRiemannName.field4_at (Γ := Γ) p N a C E x
  have fixed := GaussianCompactRiemannName.field5_at (Γ := Γ) p N a C E x
  have same : ∀ j, Γ ⊢[PRAAx] args j ≐ vals j := by
    intro j
    fin_cases j
    · exact GaussianCompactRiemannName.field0_at p N a C E x
    · exact fixed.fstE
    · exact fixed.sndE
    · exact congrAdd (congrMul left time) (congrMul width (.eqRefl _))
    · exact congrMul den time
    · exact width
  exact Prf.eqCongr f same

theorem image_row_at (i p z B N a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 imageBody i (imageData p z B N a C E) ≐ imageCell p z B (a*N+C*i) (E*N) C := by
  have read := image_cell_congr (Γ := Γ)
    (imageCell (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) i p z B N a C E
  simp only [GaussianEulerExponentialLogCell.subst_imageCell, Syn.subst_var] at read
  simp only [imageBody, inst2, subst_imageRow]
  exact read

theorem uniform_cell_budget (p u N C T M : PTm n) (hu : Γ ⊢[PRAAx] le one u) (hn : Γ ⊢[PRAAx] le N u) : Γ ⊢[PRAAx]
    le (GaussianEulerExponentialLogCell.errorNumerator p u C T M*rowDenominator p N)
      (rowNumerator p N C T M*GaussianEulerExponentialLogCell.errorDenominator p u) := by
  let P := unit p
  have first := mul_le_mul_right (M*C*C*P*P) (le_mul_mono hn hn)
  have second := mul_le_mul_right (C*(one+T)*(N*N)*P) (le_congr (one_mul u) (.eqRefl _) (mul_le_mul_right u hu))
  have exactBudget := add_le_add₂ (add_le_add₂ first (le_refl (Γ := Γ) (two*M*(u*u)*(N*N)*P))) second
  exact le_congr (by unfold GaussianEulerExponentialLogCell.errorNumerator rowDenominator; dsimp only [P]; ipra_ring)
    (by unfold rowNumerator observationCost GaussianEulerExponentialLogCell.errorDenominator; dsimp only [P]; ipra_ring) exactBudget

theorem original_row_error (i p z B N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source p z B N a C E T M)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 imageBody i (imageData p z B N a C E))
      (inst2 (multiplyBody (sampleBody GaussianEulerIntegrandName.evaluatorF)) i (pairT (weight C E N) (imageData p z B N a C E)))
      (rowNumerator p N C T M) (rowDenominator p N) := by
  let u := a*N+C*i
  let v := E*N
  have hN := hs.andE₂.andE₂.andE₂.andE₁
  have hE := hs.andE₂.andE₂.andE₁
  have h₁ := hs.andE₂.andE₁
  have ht : Γ ⊢[PRAAx] le u (T*v) := by
    have right := add_le_add₂ (le_refl (Γ := Γ) (a*N)) (mul_le_mul_right C (le_of_lt hi))
    have upper : Γ ⊢[PRAAx] le u ((a+C)*N) :=
      le_congr (by dsimp only [u]; ipra_ring) (by ipra_ring) right
    exact le_trans upper
      (le_congr (.eqRefl _) (by dsimp only [v]; ipra_ring) (mul_le_mul_right N hs.andE₂.andE₂.andE₂.andE₂.andE₁))
  have hn : Γ ⊢[PRAAx] le N u := le_trans
    (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N h₁)) (le_add_right _ _)
  have hu := le_trans hN hn
  have hv := positive_product _ _ hE hN
  let PF := GaussianEulerExponentialSubstitutionIntegrand.evaluatorF
  let px := GaussianEulerExponentialSubstitutionIntegrand.fixedData z B
  have point := summand_bound_at (sampleBody PF) N (sampleData p N a C E px) M one i hs.andE₂.andE₂.andE₂.andE₂.andE₂ hi
  have value := bound_congr ((GaussianCompactRiemannName.sample_body_at PF i p N a C E px).eqTrans
    (GaussianEulerExponentialSubstitutionIntegrand.sample_at p z B u v hs.andE₁)) (.eqRefl _) (.eqRefl _) point
  have row := GaussianEulerExponentialLogCell.original_cell_error p z B u v C T M
    (.andI (.andI hs.andE₁ (.andI hu hv)) ht) value
  have translated := (multiply_body_at (Γ := Γ) (sampleBody GaussianEulerIntegrandName.evaluatorF) (weight C E N) i (imageData p z B N a C E)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      (GaussianCompactRiemannName.sample_body_at GaussianEulerIntegrandName.evaluatorF i p N a C E (GaussianEulerIntegrandName.fixedData z B)))
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hu hu) (unit_positive _))
    (positive_product _ _ (positive_product _ _ hN hN) (unit_positive _))
    (uniform_cell_budget p u N C T M hu hn)
    (distance_congr (image_row_at i p z B N a C E).eqSymm translated.eqSymm (.eqRefl _) (.eqRefl _) row)

theorem original_finite_error (p z B N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source p z B N a C E T M) :
    Γ ⊢[PRAAx] distanceBounded (imageSum p z B N a C E)
      (quadrature GaussianEulerIntegrandName.evaluatorF p N a C E (GaussianEulerIntegrandName.fixedData z B))
      (rowNumerator p N C T M) (N*unit p) := by
  let f := sampleBody GaussianEulerIntegrandName.evaluatorF
  let x := imageData p z B N a C E
  let y := pairT (weight C E N) x
  let sh (u : PTm n) := Syn.shift u
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh p) (sh z) (sh B) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M) := by
    simpa only [Fm.shift,Syn.shift,sh,subst_source] using hs.shift
  have all : Γ ⊢[PRAAx] termsDistance imageBody (multiplyBody f) N x y (rowNumerator p N C T M) (rowDenominator p N) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,x,y,GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
      GaussianRationalRiemannRefinement.subst_weight,subst_pairT,subst_rowNumerator,subst_rowDenominator,Syn.shift,sh] using
      original_row_error (var 0) (sh p) (sh z) (sh B) (sh N) (sh a) (sh C) (sh E) (sh T) (sh M) hh.wk Prf.hyp0
  have hn := hs.andE₂.andE₂.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) p
  have hDen : Γ ⊢[PRAAx] le one (rowDenominator p N) := positive_product _ _ (positive_product _ _ hn hn) hp
  have compared := sum_distance imageBody (multiplyBody f) N x y _ _ hDen all
  exact distance_radius_mono _ _ _ _ _ _ hDen (positive_product _ _ hn hp)
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold rowDenominator; ipra_ring))
    (distance_congr (.eqRefl _) (sum_multiply f (weight C E N) N x) (.eqRefl _) (.eqRefl _) compared)

theorem actual_finite_logarithmic_image_Euler_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (imageSum (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 3) (var 4) (var 5) (var 6)
          (GaussianEulerIntegrandName.fixedData (var 1) (var 2)))
        (rowNumerator (var 0) (var 3) (var 5) (var 7) (var 8)) (var 3*unit (var 0))) :=
  closeUniv 9 (.impI (original_finite_error _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem original_value_bounds (p z R B N a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    valueBounds p z B N a C E (GaussianEulerExponentialSubstitutionCompactBound.majorant R E T) := by
  let sh (u : PTm n) := Syn.shift u
  have hv : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) :=
    by simpa only [Fm.shift,GaussianEulerCompactAdditivity.subst_intervalSource,Syn.shift,sh] using h.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hN.shift
  refine .allI (.impI ?_)
  let t := grid (var 0) (sh N) (sh a) (sh C) (sh E)
  let ctx := lt (var 0) (sh N) :: Γ.map Fm.shift
  have ht := GaussianCompactRiemannName.grid_inside (var 0) (sh N) (sh a) (sh C) (sh E)
    hv.andE₂.andE₁.wk hv.andE₁.andE₂.andE₁.wk hn.wk (le_of_lt Prf.hyp0)
  have actual := GaussianEulerExponentialSubstitutionCompactBound.original_inside_bound (sh p) t (sh z) (sh R) (sh B)
    (sh a) (sh C) (sh E) (sh T) hv.wk ht
  have readback := GaussianCompactRiemannName.sample_body_at (Γ := ctx) GaussianEulerExponentialSubstitutionIntegrand.evaluatorF
    (var 0) (sh p) (sh N) (sh a) (sh C) (sh E) (GaussianEulerExponentialSubstitutionIntegrand.fixedData (sh z) (sh B))
  simpa only [valueBounds,summandsBounded,GaussianCompactRiemannName.subst_sampleData,
    GaussianEulerExponentialSubstitutionIntegrand.subst_fixedData,GaussianEulerExponentialSubstitutionCompactBound.subst_majorant,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,t,ctx,sh] using
    (bound_congr readback.eqSymm (.eqRefl _) (.eqRefl _) actual)

theorem original_Euler_log_grid (p z R B N a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (imageSum p z B N a C E)
      (quadrature GaussianEulerIntegrandName.evaluatorF p N a C E (GaussianEulerIntegrandName.fixedData z B))
      (rowNumerator p N C T (GaussianEulerExponentialSubstitutionCompactBound.majorant R E T)) (N*unit p) :=
  original_finite_error p z B N a C E T _ (.andI h.andE₁.andE₁ (.andI h.andE₂.andE₁
    (.andI h.andE₁.andE₂.andE₁ (.andI hN (.andI h.andE₂.andE₂ (original_value_bounds p z R B N a C E T h hN))))))

theorem actual_original_Euler_log_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((GaussianEulerCompactAdditivity.intervalSource (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 4)) ⟶
      distanceBounded (imageSum (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7))
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 4) (var 5) (var 6) (var 7)
          (GaussianEulerIntegrandName.fixedData (var 1) (var 3)))
        (rowNumerator (var 0) (var 4) (var 6) (var 8) (GaussianEulerExponentialSubstitutionCompactBound.majorant (var 2) (var 7) (var 8)))
        (var 4*unit (var 0))) :=
  closeUniv 9 (.impI (original_Euler_log_grid _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialLogGrid
