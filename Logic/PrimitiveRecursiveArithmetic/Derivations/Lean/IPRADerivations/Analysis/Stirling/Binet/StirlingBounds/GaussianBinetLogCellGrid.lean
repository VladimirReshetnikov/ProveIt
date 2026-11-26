import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetLogHorizontalStep
import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetReciprocalMean

/-!
# The canonical logarithm across a finite reciprocal grid

The exact horizontal width is 1/M. Summing the original logarithm
increments across M cells telescopes to its two actual endpoint
observations. The local quadratic bound leaves a vanishing mesh error.
-/

set_option autoImplicit false
set_option maxHeartbeats 380000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLogCellGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianBinetReciprocalMean (gridData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents represents_rescale positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNormalizedTelescope (weight)
open GaussianRationalParameterTelescope (localRows local_error)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRightHalfPlaneLogarithm (source nameF)
open GaussianRightHalfPlaneLogarithmIncrementMargin (smallStep)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "L" => GaussianRightHalfPlaneLogarithm.data
local notation "rows" => GaussianBinetReciprocalMean.rowBody
local notation "reciprocalData" => GaussianBinetReciprocalMean.data

def size (A B D k : PTm n) : PTm n := two*(A+(k+one)*D+B)

def requiredMesh (A B D k : PTm n) : PTm n := num 128*(size A B D k+one)*(D*D)

def sampleData (p A B D neg k M : PTm n) : PTm n := pairT p (reciprocalData A B D neg k M)

def logRow (j p X Y E neg H : PTm n) : PTm n := ap2 nameF p (L (X+j*H) Y E neg)

def logBody : PTm 2 :=
  let x := sndT (var 1)
  let s := sndT x
  let t := sndT s
  let w := sndT t
  logRow (var 0) (fstT (var 1)) (fstT x) (fstT s) (fstT t) (fstT w) (sndT w)

def endpoint (p A B D neg k M : PTm n) : PTm n :=
  qsub (ap2 nameF p (L (M*(A+(k+one)*D)) (M*B) (M*D) neg))
    (ap2 nameF p (L (M*(A+k*D)) (M*B) (M*D) neg))

def numerator (p A D k M : PTm n) : PTm n := num 4*D*D*unit p+num 9*(M*M)*((A+k*D)*(A+k*D))

def denominator (p A D k M : PTm n) : PTm n := M*((A+k*D)*(A+k*D))*unit p

@[simp] theorem subst_size {m : ℕ} (σ : Fin n → PTm m) (A B D k : PTm n) :
    Syn.subst σ (size A B D k) = size (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ k) := by
  simp [size, one, two]

@[simp] theorem subst_requiredMesh {m : ℕ} (σ : Fin n → PTm m) (A B D k : PTm n) :
    Syn.subst σ (requiredMesh A B D k) = requiredMesh (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ k) := by
  simp [requiredMesh, one]

@[simp] theorem subst_sampleData {m : ℕ} (σ : Fin n → PTm m) (p A B D neg k M : PTm n) :
    Syn.subst σ (sampleData p A B D neg k M) = sampleData (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ k) (Syn.subst σ M) := by simp [sampleData]

@[simp] theorem subst_logRow {m : ℕ} (σ : Fin n → PTm m) (j p X Y E neg H : PTm n) :
    Syn.subst σ (logRow j p X Y E neg H) = logRow (Syn.subst σ j) (Syn.subst σ p) (Syn.subst σ X)
      (Syn.subst σ Y) (Syn.subst σ E) (Syn.subst σ neg) (Syn.subst σ H) := by simp [logRow]

private theorem log_data_congr (a a' b b' d d' s s' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hd : Γ ⊢[PRAAx] d ≐ d') (hs : Γ ⊢[PRAAx] s ≐ s') : Γ ⊢[PRAAx] L a b d s ≐ L a' b' d' s' := by
  simpa only [GaussianRightHalfPlaneLogarithm.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (L (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![a,b,d,s]) (σ' := ![a',b',d',s']) (fun i => by fin_cases i; exact ha; exact hb; exact hd; exact hs)

theorem log_at (p X Y E neg H j : PTm n) : Γ ⊢[PRAAx]
    inst2 logBody j (pairT p (gridData X Y E neg H)) ≐ logRow j p X Y E neg H := by
  let z := pairT p (gridData X Y E neg H)
  let x := sndT z
  let s := sndT x
  let t := sndT s
  let w := sndT t
  have ep : Γ ⊢[PRAAx] fstT z ≐ p := fst_pair _ _
  have ex : Γ ⊢[PRAAx] x ≐ gridData X Y E neg H := snd_pair _ _
  have es := (congrSnd ex).eqTrans (snd_pair X (pairT Y (pairT E (pairT neg H))))
  have et := (congrSnd es).eqTrans (snd_pair Y (pairT E (pairT neg H)))
  have ew := (congrSnd et).eqTrans (snd_pair E (pairT neg H))
  have exf := (congrFst ex).eqTrans (fst_pair X (pairT Y (pairT E (pairT neg H))))
  have ey := (congrFst es).eqTrans (fst_pair Y (pairT E (pairT neg H)))
  have ee := (congrFst et).eqTrans (fst_pair E (pairT neg H))
  have en := (congrFst ew).eqTrans (fst_pair neg H)
  have eh := (congrSnd ew).eqTrans (snd_pair neg H)
  have ed := log_data_congr (fstT x+j*sndT w) (X+j*H) (fstT s) Y (fstT t) E (fstT w) neg
    (congrAdd exf (congrMul (.eqRefl j) eh)) ey ee en
  simpa only [logBody, inst2, logRow, subst_ap2, GaussianRightHalfPlaneLogarithm.subst_data,
    PTm.subst_add, PTm.subst_mul, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, z, x, s, t, w] using congrAp2 nameF ep ed

private theorem width (M D : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianBinetLogHorizontalStep.step D (M*D) ≐ weight M := by
  have hE := positive_product _ _ hM hD
  exact canonical_unique _ _ (scale D oneCode) (M*D) (ofGaussian_canonical _ _ hE) (ofGaussian_canonical _ _ hM) hE
    (ofGaussian_represents _ _ hE) (represents_rescale (weight M) oneCode M D (ofGaussian_represents _ _ hM))

private theorem row_error (p A B D neg k M j : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) (hmesh : Γ ⊢[PRAAx] le (requiredMesh A B D k) M)
    (hj : Γ ⊢[PRAAx] lt j M) : Γ ⊢[PRAAx]
    distanceBounded (qsub (logRow (succ j) p (M*(A+k*D)) (M*B) (M*D) neg D)
      (logRow j p (M*(A+k*D)) (M*B) (M*D) neg D))
      (GaussianRationalHorner.qmul (weight M) (inst2 rows j (reciprocalData A B D neg k M)))
      (num 4*D*D*unit p+num 9*((M*(A+k*D))*(M*(A+k*D))))
      (((M*(A+k*D))*(M*(A+k*D)))*unit p) := by
  let A₀ := M*(A+k*D)
  let X := A₀+j*D
  let Y := M*B
  let E := M*D
  let U := unit p
  let C := size A B D k
  have hD := h.andE₂
  have hA := h.andE₁.andE₁
  have hE := positive_product M D hM hD
  have hA₀ := positive_product M (A+k*D) hM (le_trans hA (le_add_right _ _))
  have order : Γ ⊢[PRAAx] le A₀ X := le_add_right _ _
  have hx := le_trans hA₀ order
  have hs : Γ ⊢[PRAAx] source X E neg := .andI (.andI hx h.andE₁.andE₂) hE
  have margin : Γ ⊢[PRAAx] le E (D*X) := by
    dsimp only [E, X, A₀]
    ipra_le 𝔞(D)*𝔞(M)*sl hA+𝔞(M)*𝔞(k)*𝔞(D)^2+𝔞(j)*𝔞(D)^2
  have hsuc : Γ ⊢[PRAAx] le (succ j) M := hj
  have hle := le_of_lt hj
  have hsize : Γ ⊢[PRAAx] le (X+Y+(X+D)+Y) (C*E) := by
    dsimp only [X,Y,E,A₀,C,size]
    ipra_le 𝔞(D)*(sl hle+sl hsuc)+2*𝔞(M)*𝔞(A+(k+one)*D+B)*sl hD
  have small : Γ ⊢[PRAAx] smallStep D D C E := by
    unfold smallStep
    exact le_congr (by dsimp only [C, requiredMesh]; ipra_ring) (.eqRefl _) (mul_le_mul_right D hmesh)
  have main := GaussianBinetLogHorizontalStep.sample_error p X Y E neg D D C hs hD margin hsize small
  have firstDen := positive_product _ _ (positive_product _ _ hx hx) (unit_positive (Γ := Γ) p)
  have newDen := positive_product _ _ (positive_product _ _ hA₀ hA₀) (unit_positive (Γ := Γ) p)
  have sq := le_mul_mono order order
  have cap : Γ ⊢[PRAAx] le ((num 4*D*D*U+num 9*(X*X))*(A₀*A₀*U))
      ((num 4*D*D*U+num 9*(A₀*A₀))*(X*X*U)) := by ipra_le 4*𝔞(D)^2*𝔞(U)^2*sl sq
  have pulled := distance_radius_mono _ _ _ _ _ _ firstDen newDen cap main
  have rel : Γ ⊢[PRAAx] X+D ≐ A₀+succ j*D := by dsimp only [X]; ipra_ring
  have endEq : Γ ⊢[PRAAx] ap2 nameF p (L (X+D) Y E neg) ≐ logRow (succ j) p A₀ Y E neg D :=
    congrAp2 nameF (.eqRefl p) (log_data_congr _ _ _ _ _ _ _ _ rel (.eqRefl _) (.eqRefl _) (.eqRefl _))
  exact distance_congr (qsub_congr endEq (.eqRefl _))
    (qmul_congr (width M D hM hD) (GaussianBinetReciprocalMean.row_at A₀ Y E neg D j).eqSymm)
    (.eqRefl _) (.eqRefl _) pulled

private theorem mesh_local (p A B D neg k M : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) (hmesh : Γ ⊢[PRAAx] le (requiredMesh A B D k) M) : Γ ⊢[PRAAx]
    localRows logBody rows M (sampleData p A B D neg k M) (reciprocalData A B D neg k M) (weight M)
      (num 4*D*D*unit p+num 9*((M*(A+k*D))*(M*(A+k*D))))
      (((M*(A+k*D))*(M*(A+k*D)))*unit p) := by
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s neg) :=
    by simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have hm : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift.wk
  have hd : Δ ⊢[PRAAx] le (requiredMesh (s A) (s B) (s D) (s k)) (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hmesh.shift.wk
  let x := sampleData (s p) (s A) (s B) (s D) (s neg) (s k) (s M)
  let y := reciprocalData (s A) (s B) (s D) (s neg) (s k) (s M)
  have eb (j : PTm (n+1)) : Δ ⊢[PRAAx] inst2 logBody j x ≐
      logRow j (s p) (s M*(s A+s k*s D)) (s M*s B) (s M*s D) (s neg) (s D) :=
    log_at (s p) (s M*(s A+s k*s D)) (s M*s B) (s M*s D) (s neg) (s D) j
  have ew := GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) rows (weight (s M)) (var 0) y
  have estimate := row_error (s p) (s A) (s B) (s D) (s neg) (s k) (s M) (var 0) hs hm hd Prf.hyp0
  have exactStep := distance_congr (qsub_congr (eb (succ (var 0))).eqSymm (eb (var 0)).eqSymm) ew.eqSymm
    (.eqRefl _) (.eqRefl _) estimate
  simpa only [localRows, GaussianRationalParameterTelescope.forward_at, Δ,s,x,y,Syn.shift,subst_pairT,
    subst_sampleData,GaussianBinetReciprocalMean.subst_data,GaussianRationalNormalizedTelescope.subst_weight,
    PTm.subst_add, PTm.subst_mul,PTm.subst_num,GaussianCoefficientNameBounds.subst_unit] using exactStep

theorem finite_grid (p A B D neg k M : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) (hmesh : Γ ⊢[PRAAx] le (requiredMesh A B D k) M) : Γ ⊢[PRAAx]
    distanceBounded (endpoint p A B D neg k M) (GaussianBinetReciprocalMean.value A B D neg k M)
      (numerator p A D k M) (denominator p A D k M) := by
  let a := A+k*D
  let X := M*a
  let U := unit p
  let z := sampleData p A B D neg k M
  have ha : Γ ⊢[PRAAx] le one a := le_trans h.andE₁.andE₁ (le_add_right _ _)
  have hx := positive_product M a hM ha
  have hU := unit_positive (Γ := Γ) p
  have hDen := positive_product _ _ (positive_product _ _ hx hx) hU
  have newDen : Γ ⊢[PRAAx] le one (denominator p A D k M) :=
    positive_product _ _ (positive_product M (a*a) hM (positive_product _ _ ha ha)) hU
  have localSum := local_error logBody rows M z (reciprocalData A B D neg k M) (weight M)
    (num 4*D*D*U+num 9*(X*X)) (X*X*U) hDen (mesh_local p A B D neg k M h hM hmesh)
  have pair (j : PTm n) : Γ ⊢[PRAAx] inst2 logBody j z ≐ logRow j p X (M*B) (M*D) neg D :=
    log_at p X (M*B) (M*D) neg D j
  have fix (j V : PTm n) (e : Γ ⊢[PRAAx] X+j*D ≐ V) :
      Γ ⊢[PRAAx] logRow j p X (M*B) (M*D) neg D ≐ ap2 nameF p (L V (M*B) (M*D) neg) :=
    congrAp2 nameF (.eqRefl p) (log_data_congr _ _ _ _ _ _ _ _ e (.eqRefl _) (.eqRefl _) (.eqRefl _))
  have ep := qsub_congr ((pair M).eqTrans (fix M (M*(A+(k+one)*D)) (by dsimp only [X,a]; ipra_ring)))
    ((pair zero).eqTrans (fix zero X (by ipra_ring)))
  exact distance_congr ep (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hDen newDen (by dsimp only [X,a,U,numerator,denominator]; ipra_le 0) localSum)

theorem actual_horizontal_logarithm_finite_grid_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 3) (var 4) ⟶ le one (var 6) ⟶ le (requiredMesh (var 1) (var 2) (var 3) (var 5)) (var 6) ⟶
      distanceBounded (endpoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (GaussianBinetReciprocalMean.value (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 6)) (denominator (var 0) (var 1) (var 3) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (finite_grid _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLogCellGrid
