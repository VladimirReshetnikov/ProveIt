import IPRADerivations.Analysis.GaussianEulerExponentialLogGrid
import IPRADerivations.Analysis.GaussianEulerExponentialSubstitutionNamedKernel

/-!
# The finite logarithmic image grid with the actual named-input kernel

The original affine nodes and their original logarithm increments are
unchanged. Replacing each pure exponential row by the genuine named
kernel at the old logarithm costs 4*J per row at precision p. Actual
finite sums then retain the quantitative original Euler grid error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialNamedLogGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4 field5 quadrature)
open GaussianRationalFiniteSum (sum)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianPositiveRationalLogarithmIncrement (increment)
open GaussianPositiveRationalLogarithm (logF)
open GaussianEulerExponentialLogGrid (imageData)
open GaussianCompactLogarithmBounds (domain)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def imageCell (p z B a b c : PTm n) : PTm n := qmul (increment p p a b c)
  (ap2 (GaussianEulerExponentialSubstitutionNamedKernel.nameF logF) p
    (GaussianEulerExponentialSubstitutionNamedKernel.data logF z B (GaussianPositiveRationalLogarithm.data a b)))
def imageRow (i y : PTm n) : PTm n := imageCell (field0 y) (fstT (field5 y)) (sndT (field5 y))
  (field2 y*field1 y+field3 y*i) (field4 y*field1 y) (field3 y)
def imageBody : PTm 2 := imageRow (var 0) (var 1)
def imageSum (p z B N a C E : PTm n) : PTm n := sum imageBody N (imageData p z B N a C E)
def observationCost (C T M J : PTm n) : PTm n := GaussianEulerExponentialLogGrid.observationCost C T M+num 4*J
def rowNumerator (p N C T M J : PTm n) : PTm n := M*C*C*unit p+observationCost C T M J*(N*N)

@[simp] theorem subst_imageCell {m : ℕ} (σ : Fin n → PTm m) (p z B a b c : PTm n) :
    Syn.subst σ (imageCell p z B a b c) = imageCell (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) := by simp [imageCell,increment]
@[simp] theorem subst_imageRow {m : ℕ} (σ : Fin n → PTm m) (i y : PTm n) :
    Syn.subst σ (imageRow i y) = imageRow (Syn.subst σ i) (Syn.subst σ y) := by simp [imageRow]
@[simp] theorem subst_imageSum {m : ℕ} (σ : Fin n → PTm m) (p z B N a C E : PTm n) :
    Syn.subst σ (imageSum p z B N a C E) = imageSum (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [imageSum,GaussianEulerExponentialLogGrid.imageData]
@[simp] theorem subst_observationCost {m : ℕ} (σ : Fin n → PTm m) (C T M J : PTm n) :
    Syn.subst σ (observationCost C T M J) = observationCost (Syn.subst σ C) (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ J) := by
  simp [observationCost,GaussianEulerExponentialLogGrid.observationCost]
@[simp] theorem subst_rowNumerator {m : ℕ} (σ : Fin n → PTm m) (p N C T M J : PTm n) :
    Syn.subst σ (rowNumerator p N C T M J) = rowNumerator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ C)
      (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ J) := by simp [rowNumerator]

theorem image_row_at (i p z B N a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 imageBody i (imageData p z B N a C E) ≐ imageCell p z B (a*N+C*i) (E*N) C := by
  let x := GaussianEulerIntegrandName.fixedData z B
  let y := imageData p z B N a C E
  let f : PTm 6 := imageCell (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
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
    · exact (congrFst fixed).eqTrans (fst_pair _ _)
    · exact (congrSnd fixed).eqTrans (snd_pair _ _)
    · exact congrAdd (congrMul left time) (congrMul width (.eqRefl _))
    · exact congrMul den time
    · exact width
  have first : Syn.subst args f = inst2 imageBody i y := by
    simp only [f,subst_imageCell,Syn.subst_var,imageBody,inst2,subst_imageRow,Matrix.cons_val_zero,Matrix.cons_val_one]
    rfl
  have second : Syn.subst vals f = imageCell p z B (a*N+C*i) (E*N) C := by simp only [f,subst_imageCell,Syn.subst_var]; rfl
  simpa only [first,second] using Prf.eqCongr f same

theorem row_domains (i N a C E T : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) (hend : Γ ⊢[PRAAx] le (a+C) (E*T)) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    domain (a*N+C*i) (E*N) E T ⋏ domain (a*N+C*i+C) (E*N) E T := by
  let u := a*N+C*i
  let v := E*N
  have cap : Γ ⊢[PRAAx] le N u := le_trans (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N ha)) (le_add_right _ _)
  have lo : Γ ⊢[PRAAx] le v (E*u) := le_congr (by dsimp only [v]; ipra_ring) (by ipra_ring) (mul_le_mul_right E cap)
  have up : Γ ⊢[PRAAx] le u (T*v) := le_trans
    (le_congr (by dsimp only [u]; ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (a*N)) (mul_le_mul_right C (le_of_lt hi))))
    (le_congr (.eqRefl _) (by dsimp only [v]; ipra_ring) (mul_le_mul_right N hend))
  have upNext : Γ ⊢[PRAAx] le (u+C) (T*v) := le_trans
    (le_congr (by dsimp only [u]; ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (a*N)) (mul_le_mul_right C hi)))
    (le_congr (.eqRefl _) (by dsimp only [v]; ipra_ring) (mul_le_mul_right N hend))
  have loNext : Γ ⊢[PRAAx] le v (E*(u+C)) :=
    le_trans lo (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E (le_add_right u C)))
  have hu := le_trans hN cap
  have hv := positive_product _ _ hE hN
  exact .andI (.andI (.andI hu hv) (.andI lo up))
    (.andI (.andI (le_trans hu (le_add_right _ _)) hv)
      (.andI loNext upNext))

theorem original_width_bound (i p z R B N a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (increment p p (a*N+C*i) (E*N) C) (two*GaussianCompactLogarithmBounds.radius E T) one := by
  have times := row_domains i N a C E T h.andE₂.andE₁ h.andE₁.andE₂.andE₁ hN h.andE₂.andE₂ hi
  have left := GaussianCompactLogarithmBounds.sample_bound p _ _ E T h.andE₁.andE₂.andE₁ times.andE₁
  have right := GaussianCompactLogarithmBounds.sample_bound p _ _ E T h.andE₁.andE₂.andE₁ times.andE₂
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_difference _ _ _ one _ one (le_refl one) (le_refl one) right left)

theorem original_row_comparison (i p z R B N a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 imageBody i (imageData p z B N a C E))
      (inst2 GaussianEulerExponentialLogGrid.imageBody i (imageData p z B N a C E))
      (num 4*GaussianCompactLogarithmBounds.radius E T) (unit p) := by
  have times := (row_domains i N a C E T h.andE₂.andE₁ h.andE₁.andE₂.andE₁ hN h.andE₂.andE₂ hi).andE₁
  have actual := GaussianEulerExponentialSubstitutionNamedKernel.original_log_observations p p z B (a*N+C*i) (E*N)
    (.andI h.andE₁.andE₁ times.andE₁)
  have compared := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) actual
  have scaled := GaussianNamedDifferenceQuotient.scale_distance (increment p p (a*N+C*i) (E*N) C) _ _ _ two (unit p)
    (unit_positive p) (original_width_bound i p z R B N a C E T h hN hi) compared
  exact distance_congr (image_row_at i p z B N a C E).eqSymm (GaussianEulerExponentialLogGrid.image_row_at i p z B N a C E).eqSymm
    (by ipra_ring) (.eqRefl _) scaled

theorem original_image_comparison (p z R B N a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (imageSum p z B N a C E) (GaussianEulerExponentialLogGrid.imageSum p z B N a C E)
      (num 4*GaussianCompactLogarithmBounds.radius E T*N) (unit p) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have rows : Γ ⊢[PRAAx] termsDistance imageBody GaussianEulerExponentialLogGrid.imageBody N
      (imageData p z B N a C E) (imageData p z B N a C E) (num 4*GaussianCompactLogarithmBounds.radius E T) (unit p) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,GaussianEulerExponentialLogGrid.imageData,GaussianCompactRiemannName.subst_sampleData,
      GaussianEulerIntegrandName.subst_fixedData,GaussianCompactLogarithmBounds.subst_radius,GaussianCoefficientNameBounds.subst_unit,
      PTm.subst_mul,PTm.subst_num,Syn.shift] using
      original_row_comparison (var 0) (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hs.wk ns.wk Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (sum_distance _ _ _ _ _ _ _ (unit_positive p) rows)

theorem original_Euler_log_grid (p z R B N a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (imageSum p z B N a C E)
      (quadrature GaussianEulerIntegrandName.evaluatorF p N a C E (GaussianEulerIntegrandName.fixedData z B))
      (rowNumerator p N C T (GaussianEulerExponentialSubstitutionCompactBound.majorant R E T) (GaussianCompactLogarithmBounds.radius E T))
      (N*unit p) := by
  have hD := positive_product _ _ hN (unit_positive (Γ := Γ) p)
  have first := distance_radius_mono _ _ _ _ (num 4*GaussianCompactLogarithmBounds.radius E T*(N*N)) (N*unit p)
    (unit_positive p) hD (le_of_eq_add (d := zero) (by ipra_ring)) (original_image_comparison p z R B N a C E T h hN)
  have last := GaussianEulerExponentialLogGrid.original_Euler_log_grid p z R B N a C E T h hN
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rowNumerator observationCost GaussianEulerExponentialLogGrid.rowNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first last)

theorem actual_original_named_kernel_log_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((GaussianEulerCompactAdditivity.intervalSource (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) ⋏ le one (var 4)) ⟶
      distanceBounded (imageSum (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7))
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 4) (var 5) (var 6) (var 7) (GaussianEulerIntegrandName.fixedData (var 1) (var 3)))
        (rowNumerator (var 0) (var 4) (var 6) (var 8) (GaussianEulerExponentialSubstitutionCompactBound.majorant (var 2) (var 7) (var 8))
          (GaussianCompactLogarithmBounds.radius (var 7) (var 8))) (var 4*unit (var 0))) :=
  closeUniv 9 (.impI (original_Euler_log_grid _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialNamedLogGrid
