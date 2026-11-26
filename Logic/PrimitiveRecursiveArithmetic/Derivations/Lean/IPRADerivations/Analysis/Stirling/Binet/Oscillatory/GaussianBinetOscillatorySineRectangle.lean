import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetOscillatorySineRows

/-!
# Original finite arctangent rectangle and the damped sine quadrature

The actual transposed columns are gathered with their original time
weight. The regularized first entry and all positive sine quotients
are values of one primitive-recursive program. No columnwise bounds
are supplied by the caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineRectangle

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open GaussianBinetArctangentCosineRectangle (rectangle)
open GaussianBinetCosinePrimitive (endpoint)
open GaussianBinetExponentialIntegralGrid (row)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetImaginaryExponentialScale (coefficient_congr)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetOscillatorySineRows (numeratorBound all_time_column_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (field0 field1 field2 field3 field4 field5 sampleData fraction_congr)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply)
open GaussianRationalFubini (columnSumBody column_sum_at columnFirst)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative)
open RationalArithmetic (select)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "matrix" => GaussianBinetOscillatoryRectangleTranspose.matrix
local notation "rectData" => GaussianBinetOscillatoryRectangleTranspose.data

def entry (j r A B T N P C q : PTm n) : PTm n :=
  let a := T*j
  select (sg j) (fraction A B)
    (qmul (row r q P a N)
      (qmul (reciprocal (coefficient a N (polarity true))) (endpoint r (A*a) (B*N) C one)))

def body : PTm 2 :=
  let d : PTm 2 := var 1
  entry (var 0) (field0 d) (field1 d) (field2 d) (field3 d) (field4 d)
    (fstT (field5 d)) (fstT (sndT (field5 d))) (sndT (sndT (field5 d)))

def data (p X Y D sign A B R U L N : PTm n) : PTm n :=
  let T := D*L
  sampleData (p+N) A B T N (pairT (R*T) (pairT (U*T) (qnegative (argument X Y D sign))))

def value (p X Y D sign A B R U L N : PTm n) : PTm n :=
  qmul (weight (D*L) one N) (sum body N (data p X Y D sign A B R U L N))

@[simp] theorem subst_entry {m : ℕ} (σ : Fin n → PTm m) (j r A B T N P C q : PTm n) :
    Syn.subst σ (entry j r A B T N P C q) = entry (Syn.subst σ j) (Syn.subst σ r) (Syn.subst σ A)
      (Syn.subst σ B) (Syn.subst σ T) (Syn.subst σ N) (Syn.subst σ P) (Syn.subst σ C) (Syn.subst σ q) := by simp [entry,sg,one]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p X Y D sign A B R U L N : PTm n) :
    Syn.subst σ (data p X Y D sign A B R U L N) = data (Syn.subst σ p) (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ U)
      (Syn.subst σ L) (Syn.subst σ N) := by simp [data,GaussianLogGammaEulerRepresentation.subst_argument]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p X Y D sign A B R U L N : PTm n) :
    Syn.subst σ (value p X Y D sign A B R U L N) = value (Syn.subst σ p) (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ U)
      (Syn.subst σ L) (Syn.subst σ N) := by simp [value,one]

private theorem row_congr {p p' q q' S S' A A' B B' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hq : Γ ⊢[PRAAx] q ≐ q') (hS : Γ ⊢[PRAAx] S ≐ S')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx]
    row p q S A B ≐ row p' q' S' A' B' := by
  simpa only [GaussianBinetExponentialIntegralGrid.subst_row,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (row (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,q,S,A,B]) (σ' := ![p',q',S',A',B'])
      (fun i => by fin_cases i; exact hp; exact hq; exact hS; exact hA; exact hB)

private theorem select_congr (b : PTm n) {x x' y y' : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') : Γ ⊢[PRAAx] select b x y ≐ select b x' y' := by
  simpa only [RationalArithmetic.subst_select,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (select (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![b,x,y]) (σ' := ![b,x',y']) (fun i => by fin_cases i; exact .eqRefl b; exact hx; exact hy)

private theorem entry_congr (j : PTm n) {r r' A A' B B' T T' N N' P P' C C' q q' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hT : Γ ⊢[PRAAx] T ≐ T')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hP : Γ ⊢[PRAAx] P ≐ P') (hC : Γ ⊢[PRAAx] C ≐ C') (hq : Γ ⊢[PRAAx] q ≐ q') :
    Γ ⊢[PRAAx] entry j r A B T N P C q ≐ entry j r' A' B' T' N' P' C' q' := by
  have time := congrMul hT (.eqRefl j)
  have denom := congrMul hB hN
  have angle := congrMul hA time
  have inv : Γ ⊢[PRAAx] reciprocal (coefficient (T*j) N (polarity true)) ≐ reciprocal (coefficient (T'*j) N' (polarity true)) := by
    simpa only [GaussianRationalReciprocal.subst_reciprocal,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (reciprocal (var 0)) (coefficient_congr true time hN)
  have er (s : Bool) := row_congr hr (coefficient_congr s angle denom) (congrMul hC (.eqRefl one)) (.eqRefl one) (.eqRefl one)
  have sine : Γ ⊢[PRAAx] endpoint r (A*(T*j)) (B*N) C one ≐ endpoint r' (A'*(T'*j)) (B'*N') C' one :=
    qmul_congr (.eqRefl _) (qsub_congr (er true) (er false))
  have eb := qmul_congr (row_congr hr hq hP time hN) (qmul_congr inv sine)
  have ea := fraction_congr _ _ _ _ hA hB
  exact select_congr (sg j) ea eb

theorem row_at (j p X Y D sign A B R U L N : PTm n) : Γ ⊢[PRAAx]
    inst2 body j (data p X Y D sign A B R U L N) ≐ GaussianBinetOscillatorySineRows.value j p X Y D sign A B R U L N := by
  let d := data p X Y D sign A B R U L N
  let T := D*L
  let q := qnegative (argument X Y D sign)
  have read : inst2 body j d = entry j (field0 d) (field1 d) (field2 d) (field3 d) (field4 d)
      (fstT (field5 d)) (fstT (sndT (field5 d))) (sndT (sndT (field5 d))) := by
    simp only [inst2,body,subst_entry,GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,
      GaussianCompactRiemannName.subst_field2,GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,
      GaussianCompactRiemannName.subst_field5,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [read]
  have h : Γ ⊢[PRAAx] field5 d ≐ pairT (R*T) (pairT (U*T) q) := GaussianCompactRiemannName.field5_at _ _ _ _ _ _
  have tail := (congrSnd h).eqTrans (snd_pair _ _)
  exact entry_congr j (GaussianCompactRiemannName.field0_at _ _ _ _ _ _) (GaussianCompactRiemannName.field1_at _ _ _ _ _ _)
    (GaussianCompactRiemannName.field2_at _ _ _ _ _ _) (GaussianCompactRiemannName.field3_at _ _ _ _ _ _)
    (GaussianCompactRiemannName.field4_at _ _ _ _ _ _) ((congrFst h).eqTrans (fst_pair _ _))
    ((congrFst tail).eqTrans (fst_pair _ _)) ((congrSnd tail).eqTrans (snd_pair _ _))

private theorem cell_error (j p M X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L) (hA : Γ ⊢[PRAAx] le A (B*U))
    (hj : Γ ⊢[PRAAx] le j N) (hC : Γ ⊢[PRAAx] le (U*(D*L)) M) :
    let d := rectData p M X Y D sign A B R U L N
    Γ ⊢[PRAAx] distanceBounded (inst2 (multiplyBody (columnSumBody matrix)) j (pairT (weight A B M) (pairT M d)))
      (inst2 body j (data p X Y D sign A B R U L N)) (numeratorBound p M D A B U L N) ((B*M)*unit (p+N)) := by
  let d := rectData p M X Y D sign A B R U L N
  let w := weight A B M
  have read := (multiply_body_at (Γ := Γ) (columnSumBody matrix) w j (pairT M d)).eqTrans
    (qmul_congr (.eqRefl _) (column_sum_at matrix j M d))
  exact distance_congr read.eqSymm (row_at j p X Y D sign A B R U L N).eqSymm (.eqRefl _) (.eqRefl _)
    (all_time_column_error j p M X Y D sign A B R U L N hz hB hM hN hL hA hj hC)

theorem rectangle_error (p M X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L) (hA : Γ ⊢[PRAAx] le A (B*U))
    (hC : Γ ⊢[PRAAx] le (U*(D*L)) M) : Γ ⊢[PRAAx]
    distanceBounded (rectangle p M X Y D sign A B R U L N) (value p X Y D sign A B R U L N)
      ((D*L)*numeratorBound p M D A B U L N) ((B*M)*unit (p+N)) := by
  let d := rectData p M X Y D sign A B R U L N
  let w := weight A B M
  let W := weight (D*L) one N
  let x := pairT w (pairT M d)
  let y := data p X Y D sign A B R U L N
  let g := multiplyBody (columnSumBody matrix)
  let E := numeratorBound p M D A B U L N
  let H := (B*M)*unit (p+N)
  have rows : Γ ⊢[PRAAx] termsDistance g body N x y E H := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := Γ.map Fm.shift
    have z : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by simpa [Δ,s,Syn.shift,Fm.shift] using hz.shift
    have b : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Syn.shift,Fm.shift] using hB.shift
    have m : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Syn.shift,Fm.shift] using hM.shift
    have n' : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Syn.shift,Fm.shift] using hN.shift
    have l : Δ ⊢[PRAAx] le one (s L) := by simpa [Δ,s,Syn.shift,Fm.shift] using hL.shift
    have a : Δ ⊢[PRAAx] le (s A) (s B*s U) := by simpa [Δ,s,Syn.shift,Fm.shift] using hA.shift
    have c : Δ ⊢[PRAAx] le (s U*(s D*s L)) (s M) := by simpa [Δ,s,Syn.shift,Fm.shift] using hC.shift
    simpa only [d,w,x,y,g,E,H,s,Δ,Syn.shift,subst_data,subst_pairT,PTm.subst_mul,PTm.subst_add,
      GaussianBinetOscillatoryRectangleTranspose.subst_data,GaussianRationalRiemannRefinement.subst_weight,
      GaussianBinetOscillatorySineRows.subst_numeratorBound,GaussianCoefficientNameBounds.subst_unit] using
      cell_error (var 0) (s p) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s L) (s N)
        z.wk b.wk m.wk n'.wk l.wk a.wk (le_of_lt Prf.hyp0) c.wk
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (positive_product _ _ hB hM) (unit_positive _)
  have denom := positive_product _ _ (le_refl (Γ := Γ) one) hN
  have sums := sum_distance _ _ _ _ _ _ _ hH rows
  have mul := bounded_product W _ (D*L) (one*N) (N*E) H denom hH (weight_bound _ _ _ (le_refl one) hN) sums
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul W (sum g N x)) (qmul W (sum body N y)) ((D*L)*(N*E)) ((one*N)*H) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference W _ _).eqSymm (.eqRefl _) (.eqRefl _) mul
  have matchLeft : Γ ⊢[PRAAx] qmul W (sum g N x) ≐ rectangle p M X Y D sign A B R U L N :=
    (qmul_congr (.eqRefl _) (sum_multiply (columnSumBody matrix) w N (pairT M d))).eqTrans
      ((qmul_associative W w _).eqSymm.eqTrans
        ((qmul_congr (qmul_commutative W w) (.eqRefl _)).eqTrans
          (GaussianBinetOscillatoryRectangleTranspose.returned_transpose p M X Y D sign A B R U L N).eqSymm))
  exact distance_radius_mono _ _ ((D*L)*(N*E)) ((one*N)*H) ((D*L)*E) H
    (positive_product _ _ denom hH) hH (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr matchLeft (.eqRefl _) (.eqRefl _) (.eqRefl _) scaled)

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineRectangle
