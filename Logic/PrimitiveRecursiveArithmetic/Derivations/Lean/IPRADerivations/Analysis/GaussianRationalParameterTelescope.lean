import IPRADerivations.Analysis.GaussianRationalRiemannRefinement
import IPRADerivations.Analysis.GaussianFastValueCut

/-!
# Finite parameter telescopes for actual Gaussian sample programs

The fixed terms `f` and `g` evaluate a path and its slopes at numerical
indices. The local adjacent-error and slope-error envelopes are explicit
inputs. Quantifier-free induction telescopes the original finite sum;
its constant complex step is neither rounded nor replaced by a new name.
The encoded specialization proves exactly that N copies of h/(D*N)
give h/D, and retains independent endpoint observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalParameterTelescope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian qadd qmul positive_product canonical_unique)
open GaussianRationalMetric (bounded distanceBounded qsub bounded_to_cleared bounded_of_cleared)
open GaussianRationalFiniteSum (sum multiplyBody)
open GaussianRationalRiemannRefinement (termsDistance constantBody)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def forward (f : PTm 2) : PTm 2 :=
  qsub (inst2 f (succ (var 0)) (var 1)) (inst2 f (var 0) (var 1))
def localRows (f g : PTm 2) (N x y c A D : PTm n) : Fm PTm n :=
  termsDistance (forward f) (multiplyBody g) N x (pairT c y) A D
def slopeRows (g : PTm 2) (N y v B E : PTm n) : Fm PTm n :=
  termsDistance g constantBody N y v B E
def numerator (N A D V W B E : PTm n) : PTm n := N*(A*W*E+V*B*D)
def denominator (D W E : PTm n) : PTm n := D*W*E
def step (h D N : PTm n) : PTm n := ofGaussian h (D*N)
def encodedNumerator (N A D X Y B E : PTm n) : PTm n := N*A*Y*E+X*B*D
def encodedDenominator (D Y E : PTm n) : PTm n := D*Y*E
def encodedInput (f g : PTm 2) (N x y h F v A D X Y B E : PTm n) : Fm PTm n :=
  le one N ⋏ (le one F ⋏ (le one D ⋏ (le one Y ⋏ (le one E ⋏
    (bounded (ofGaussian h F) X Y ⋏ (localRows f g N x y (step h F N) A D ⋏ slopeRows g N y v B E))))))

@[simp] theorem forward_at (f : PTm 2) (i x : PTm n) :
    inst2 (forward f) i x = qsub (inst2 f (succ i) x) (inst2 f i x) := by
  change Syn.subst ![i,x] (forward f) = _
  simp only [forward,GaussianRationalMetric.subst_qsub,subst_inst2,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
@[simp] theorem subst_localRows {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (N x y c A D : PTm n) :
    (localRows f g N x y c A D).subst σ = localRows f g (Syn.subst σ N) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ c) (Syn.subst σ A) (Syn.subst σ D) := by simp [localRows]
@[simp] theorem subst_slopeRows {m : ℕ} (σ : Fin n → PTm m) (g : PTm 2) (N y v B E : PTm n) :
    (slopeRows g N y v B E).subst σ = slopeRows g (Syn.subst σ N) (Syn.subst σ y)
      (Syn.subst σ v) (Syn.subst σ B) (Syn.subst σ E) := by simp [slopeRows]
@[simp] theorem subst_step {m : ℕ} (σ : Fin n → PTm m) (h D N : PTm n) :
    Syn.subst σ (step h D N) = step (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ N) := by simp [step]
@[simp] theorem subst_encodedInput {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (N x y h F v A D X Y B E : PTm n) :
    (encodedInput f g N x y h F v A D X Y B E).subst σ = encodedInput f g (Syn.subst σ N) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ h) (Syn.subst σ F) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ D)
      (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ B) (Syn.subst σ E) := by simp [encodedInput]

private def forwardLaw (f : PTm 2) (x k : PTm n) : Fm PTm n :=
  sum (forward f) k x ≐ qsub (inst2 f k x) (inst2 f zero x)
@[simp] private theorem subst_forwardLaw {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x k : PTm n) :
    (forwardLaw f x k).subst σ = forwardLaw f (Syn.subst σ x) (Syn.subst σ k) := by simp [forwardLaw]

theorem forward_sum (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    sum (forward f) N x ≐ qsub (inst2 f N x) (inst2 f zero x) := by
  have all : Γ ⊢[PRAAx] .all (forwardLaw f (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (GaussianCoefficientNormOrder.qsub_self _).eqSymm
    · simp only [subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine (GaussianRationalFiniteSum.sum_succ (forward f) _ _).eqTrans ?_
      rw [forward_at]
      exact (qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans
        ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianReconstructionRoots.difference_chain _ _ _))
  have result : Γ ⊢[PRAAx] forwardLaw f x N := by
    simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact result

theorem local_error (f g : PTm 2) (N x y c A D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] localRows f g N x y c A D) : Γ ⊢[PRAAx]
    distanceBounded (qsub (inst2 f N x) (inst2 f zero x)) (qmul c (sum g N y)) (N*A) D :=
  distance_congr (forward_sum f N x) (GaussianRationalFiniteSum.sum_multiply g c N y) (.eqRefl _) (.eqRefl _)
    (GaussianRationalRiemannRefinement.sum_distance (forward f) (multiplyBody g) N x (pairT c y) A D hD h)

theorem constant_slope_product (N c v : PTm n) : Γ ⊢[PRAAx]
    qmul c (sum constantBody N v) ≐ qmul (natScale N c) v :=
  (qmul_congr (.eqRefl _) (GaussianRationalRiemannRefinement.constant_sum v N)).eqTrans
    ((GaussianRationalNaturalScale.natScale_product N c v).eqTrans
      ((GaussianRationalNaturalScale.natScale_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative c v)).eqTrans
        ((GaussianRationalNaturalScale.natScale_product N v c).eqSymm.eqTrans
          (GaussianRationalPowerAlgebra.qmul_commutative v (natScale N c)))))

theorem fixed_slope_error (f g : PTm 2) (N x y c v A D V W B E : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hW : Γ ⊢[PRAAx] le one W) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] bounded c V W)
    (hl : Γ ⊢[PRAAx] localRows f g N x y c A D)
    (hs : Γ ⊢[PRAAx] slopeRows g N y v B E) : Γ ⊢[PRAAx]
    distanceBounded (qsub (inst2 f N x) (inst2 f zero x)) (qmul (natScale N c) v)
      (numerator N A D V W B E) (denominator D W E) := by
  have first := local_error f g N x y c A D hD hl
  have slopes := GaussianRationalRiemannRefinement.sum_distance g constantBody N y v B E hE hs
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hW hE hc slopes
  have last : Γ ⊢[PRAAx] distanceBounded (qmul c (sum g N y)) (qmul c (sum constantBody N v))
      (V*(N*B)) (W*E) := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference c (sum g N y) (sum constantBody N v)).eqSymm
    (.eqRefl _) (.eqRefl _) product
  have actual := distance_congr (.eqRefl _) (constant_slope_product N c v) (.eqRefl _) (.eqRefl _) last
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ (N*A) D (V*(N*B)) (W*E)
    hD (positive_product _ _ hW hE) first actual
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring) (by unfold denominator; ipra_ring) joined

theorem step_bound (h F N X Y : PTm n) (hF : Γ ⊢[PRAAx] le one F) (hN : Γ ⊢[PRAAx] le one N)
    (hY : Γ ⊢[PRAAx] le one Y) (hh : Γ ⊢[PRAAx] bounded (ofGaussian h F) X Y) : Γ ⊢[PRAAx]
    bounded (step h F N) X (Y*N) := by
  have fn := positive_product _ _ hF hN
  have yn := positive_product _ _ hY hN
  have clear := bounded_to_cleared _ _ F X Y hF hY (GaussianRationalHorner.ofGaussian_represents h F hF) hh
  apply bounded_of_cleared _ _ (F*N) X (Y*N) fn yn (GaussianRationalHorner.ofGaussian_represents h (F*N) fn)
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (N*N) clear)

theorem whole_step (h F N : PTm n) (hF : Γ ⊢[PRAAx] le one F) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    natScale N (step h F N) ≐ ofGaussian h F := by
  have fn := positive_product _ _ hF hN
  exact canonical_unique _ _ (ComplexLogarithmRemainder.scale N h) (F*N)
    (GaussianRationalNaturalScale.natScale_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hF) fn
    (GaussianRationalNaturalScale.natScale_represents _ _ _ _ fn (GaussianRationalHorner.ofGaussian_represents _ _ fn))
    (GaussianRationalHorner.represents_rescale _ _ _ N (GaussianRationalHorner.ofGaussian_represents _ _ hF))

theorem encoded_fixed_slope_error (f g : PTm 2) (N x y h F v A D X Y B E : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hF : Γ ⊢[PRAAx] le one F) (hD : Γ ⊢[PRAAx] le one D)
    (hY : Γ ⊢[PRAAx] le one Y) (hE : Γ ⊢[PRAAx] le one E)
    (hh : Γ ⊢[PRAAx] bounded (ofGaussian h F) X Y)
    (hl : Γ ⊢[PRAAx] localRows f g N x y (step h F N) A D)
    (hs : Γ ⊢[PRAAx] slopeRows g N y v B E) : Γ ⊢[PRAAx]
    distanceBounded (qsub (inst2 f N x) (inst2 f zero x)) (qmul (ofGaussian h F) v)
      (encodedNumerator N A D X Y B E) (encodedDenominator D Y E) := by
  have yn := positive_product _ _ hY hN
  have oldDen := positive_product _ _ (positive_product _ _ hD yn) hE
  have newDen := positive_product _ _ (positive_product _ _ hD hY) hE
  have old := distance_congr (.eqRefl _) (qmul_congr (whole_step h F N hF hN) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (fixed_slope_error f g N x y (step h F N) v A D X (Y*N) B E hD yn hE (step_bound h F N X Y hF hN hY hh) hl hs)
  exact distance_radius_mono _ _ _ _ _ _ oldDen newDen
    (le_of_eq_add (d := zero) (by unfold numerator encodedNumerator encodedDenominator; ipra_ring)) old

theorem endpoint_readback (f : PTm 2) (N x left right target A D : PTm n)
    (h0 : Γ ⊢[PRAAx] inst2 f zero x ≐ left) (hN : Γ ⊢[PRAAx] inst2 f N x ≐ right)
    (h : Γ ⊢[PRAAx] distanceBounded (qsub (inst2 f N x) (inst2 f zero x)) target A D) : Γ ⊢[PRAAx]
    distanceBounded (qsub right left) target A D := distance_congr (qsub_congr hN h0) (.eqRefl _) (.eqRefl _) (.eqRefl _) h

theorem independent_endpoints (f : PTm 2) (N x left right target A D L S M T : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hS : Γ ⊢[PRAAx] le one S) (hT : Γ ⊢[PRAAx] le one T)
    (hl : Γ ⊢[PRAAx] distanceBounded left (inst2 f zero x) L S)
    (hr : Γ ⊢[PRAAx] distanceBounded right (inst2 f N x) M T)
    (h : Γ ⊢[PRAAx] distanceBounded (qsub (inst2 f N x) (inst2 f zero x)) target A D) : Γ ⊢[PRAAx]
    distanceBounded (qsub right left) target ((M*S+L*T)*D+A*(T*S)) ((T*S)*D) :=
  GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (positive_product _ _ hT hS) hD
    (GaussianFastValueCut.distance_difference right left (inst2 f N x) (inst2 f zero x) M T L S hT hS hr hl) h

theorem actual_finite_parameter_forward_telescope_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum (forward f) (var 0) (var 1) ≐ qsub (inst2 f (var 0) (var 1)) (inst2 f zero (var 1))) :=
  closeUniv 2 (forward_sum f _ _)

theorem actual_finite_parameter_local_error_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 5) ⋏ localRows f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⟶
      distanceBounded (qsub (inst2 f (var 0) (var 1)) (inst2 f zero (var 1)))
        (qmul (var 3) (sum g (var 0) (var 2))) (var 0*var 4) (var 5)) :=
  closeUniv 6 (.impI (local_error f g _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_encoded_whole_parameter_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 1) ⋏ le one (var 2)) ⟶ natScale (var 2) (step (var 0) (var 1) (var 2)) ≐ ofGaussian (var 0) (var 1)) :=
  closeUniv 3 (.impI (whole_step _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_encoded_parameter_telescope_error_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (encodedInput f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⟶
      distanceBounded (qsub (inst2 f (var 0) (var 1)) (inst2 f zero (var 1)))
        (qmul (ofGaussian (var 3) (var 4)) (var 5))
        (encodedNumerator (var 0) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11))
        (encodedDenominator (var 7) (var 9) (var 11))) :=
  closeUniv 12 (.impI (encoded_fixed_slope_error f g _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalParameterTelescope
