import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngleResidual
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalSeparatedReconstruction
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineSquaredNormalization

/-!
# The literal odd sine root sample list

The primitive-recursive list takes the original divided-angle samples
at indices 1 through J. Its exact lookup supplies the selected Cayley
sine margin and root residual to the finite reconstruction estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineSampleRootList

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentDivisionAngleResidual (rootSample sineSample positiveSample negativeSample mesh_positive
  sine_at_sample positiveBudget sampled_root_residual)
open GaussianArctangentCayleyExponentialStep (conjugate_unit_bound)
open GaussianArctangentCayleyValues (unit_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNameReciprocal (lower)
open GaussianRationalHorner (evaluate positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (qone qone_bounded bound_congr bounded_product bounded_difference)
open GaussianRationalReconstruction (product)
open GaussianRationalSeparatedDeflation (separation laterResiduals)
open GaussianRationalSeparatedReconstruction (differencesBounded errorNumerator reconstruction_distance)
open GaussianSineSquaredPolynomial (coefficients coefficients_length coefficients_monic)
open GaussianSineSquaredResidual (multiplier_bound)
open GaussianSineSquaredTrace (sineValue fromSine)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (p J z : PTm n) : PTm n := pairT p (pairT J z)
def body : PTm 2 := rootSample (fstT (var 1)) (succ (var 0)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def roots (p J z : PTm n) : PTm n := sequence body J (data p J z)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (p J z : PTm n) :
    Syn.subst σ (data p J z) = data (Syn.subst σ p) (Syn.subst σ J) (Syn.subst σ z) := by
  simp [data]

@[simp] theorem subst_roots {m : ℕ} (σ : Fin n → PTm m) (p J z : PTm n) :
    Syn.subst σ (roots p J z) = roots (Syn.subst σ p) (Syn.subst σ J) (Syn.subst σ z) := by
  simp [roots]

theorem roots_length (p J z : PTm n) : Γ ⊢[PRAAx] length (roots p J z) ≐ J :=
  sequence_length _ _ _

theorem body_at (p J z j : PTm n) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.inst2 body j (data p J z) ≐ rootSample p (succ j) J z := by
  simpa [body,LeanProofs.IPRA.inst2] using Prf.eqCongr (Γ := Γ)
    (rootSample (var 0) (succ (var 1)) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (data p J z),j,fstT (sndT (data p J z)),sndT (sndT (data p J z))])
    (σ' := ![p,j,J,z]) (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact .eqRefl _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem roots_at (p J z j : PTm n) (hj : Γ ⊢[PRAAx] lt j J) :
    Γ ⊢[PRAAx] entry (roots p J z) j ≐ rootSample p (succ j) J z :=
  (sequence_decode body hj).eqTrans (body_at _ _ _ _)

def sineMargins (p J z D : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift J) ⟶ lower (sineSample (Syn.shift p) (succ (var 0)) (Syn.shift J) (Syn.shift z)) (Syn.shift D))

@[simp] theorem subst_sineMargins {m : ℕ} (σ : Fin n → PTm m) (p J z D : PTm n) :
    (sineMargins p J z D).subst σ = sineMargins (Syn.subst σ p) (Syn.subst σ J) (Syn.subst σ z) (Syn.subst σ D) := by
  simp [sineMargins, Syn.subst_shift, Syn.shift_subst]

theorem sine_margin_at (p J z D j : PTm n) (hm : Γ ⊢[PRAAx] sineMargins p J z D) (hj : Γ ⊢[PRAAx] lt j J) :
    Γ ⊢[PRAAx] lower (sineSample p (succ j) J z) D := by
  have gate : Γ ⊢[PRAAx] lt j J ⟶ lower (sineSample p (succ j) J z) D := by
    simpa [sineMargins] using hm.allE j
  exact .impE gate hj

theorem sine_bound (p k J z : PTm n) : Γ ⊢[PRAAx] bounded (sineSample p k J z) one one := by
  let a := positiveSample p k J z
  let b := negativeSample p k J z
  have hm := mesh_positive (Γ := Γ) p k J z
  have hd : Γ ⊢[PRAAx] bounded (qsub a b) two one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_difference a b one one one one (le_refl _) (le_refl _)
        (unit_bound _ _ hm) (conjugate_unit_bound _ _ hm))
  have hp := bounded_product GaussianNamedSineFromExponential.multiplier (qsub a b) one two two one
    (le_succ_self one) (le_refl _) multiplier_bound hd
  exact bound_congr (sine_at_sample p k J z) (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_succ_self one) (le_refl _)) (le_refl _)
      (le_congr (by ipra_ring) (by ipra_ring) (le_refl two)) hp)

theorem root_bound (p k J z : PTm n) : Γ ⊢[PRAAx] bounded (rootSample p k J z) (num 8) one := by
  let s := sineSample p k J z
  have hs := sine_bound (Γ := Γ) p k J z
  have sq : Γ ⊢[PRAAx] bounded (GaussianRationalHorner.qmul s s) one one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_product s s one one one one (le_refl _) (le_refl _) hs hs)
  have d : Γ ⊢[PRAAx] bounded (qsub qone (GaussianRationalHorner.qmul s s)) two one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_difference qone (GaussianRationalHorner.qmul s s) one one one one
      (le_refl _) (le_refl _) qone_bounded sq)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_product (naturalPoint (num 4)) _ (num 4) one two one (le_refl _) (le_refl _)
      (GaussianNamedNaturalScale.natural_point_bound _) d)

theorem root_differences (p J z y B : PTm n) (hy : Γ ⊢[PRAAx] bounded y B one) :
    Γ ⊢[PRAAx] differencesBounded (roots p J z) y (B+num 8) := by
  refine .allI (.impI ?_)
  let P := Syn.shift p
  let N := Syn.shift J
  let Z := Syn.shift z
  let Y := Syn.shift y
  let A := Syn.shift B
  let j : PTm (n+1) := var 0
  let Δ := lt j (length (roots P N Z)) :: Γ.map Fm.shift
  have hj : Δ ⊢[PRAAx] lt j N := lt_congr (.eqRefl _) (roots_length P N Z) Prf.hyp0
  have hy' : Δ ⊢[PRAAx] bounded Y A one := by simpa [Δ,Fm.shift,Syn.shift,P,N,Z,Y,A,j,one] using hy.shift.wk
  have hr := bound_congr (roots_at P N Z j hj).eqSymm (.eqRefl _) (.eqRefl _) (root_bound P (succ j) N Z)
  have h : Δ ⊢[PRAAx] bounded (qsub Y (entry (roots P N Z) j)) (A+num 8) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_difference Y (entry (roots P N Z) j) A one (num 8) one (le_refl _) (le_refl _) hy' hr)
  simpa [differencesBounded,Syn.shift,P,N,Z,Y,A,j,Δ] using h

theorem root_residuals (p J z D : PTm n) (hd : Γ ⊢[PRAAx] le one D) (hm : Γ ⊢[PRAAx] sineMargins p J z D) :
    Γ ⊢[PRAAx] laterResiduals (coefficients J) (roots p J z) zero (D*positiveBudget J) (unit p) := by
  refine .allI (.impI (.impI ?_))
  let P := Syn.shift p
  let N := Syn.shift J
  let Z := Syn.shift z
  let H := Syn.shift D
  let j : PTm (n+1) := var 0
  let Δ := le zero j :: lt j (length (roots P N Z)) :: Γ.map Fm.shift
  have hd' : Δ ⊢[PRAAx] le one H := by simpa [Δ,Fm.shift,Syn.shift,P,N,Z,H,j,one] using hd.shift.wk.wk
  have hm' : Δ ⊢[PRAAx] sineMargins P N Z H := by simpa [Δ,Fm.shift,Syn.shift,P,N,Z,H,j] using hm.shift.wk.wk
  have hj : Δ ⊢[PRAAx] lt j N := lt_congr (.eqRefl _) (roots_length P N Z) Prf.hyp1
  have sample := sampled_root_residual P (succ j) N Z H hj hd' (sine_margin_at P N Z H j hm' hj)
  have cast := GaussianRationalMonicReduction.evaluate_congr (.eqRefl (coefficients N)) (roots_at P N Z j hj).eqSymm
  have rate : Δ ⊢[PRAAx] bounded (evaluate (coefficients N) (entry (roots P N Z) j)) (H*positiveBudget N) (unit P) :=
    bound_congr cast (.eqRefl _) (.eqRefl _)
      (bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_succ_self one) (unit_positive P)) (unit_positive P)
        (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) sample)
  simpa [laterResiduals,Syn.shift,P,N,Z,H,j,Δ,positiveBudget,two,one] using rate

theorem reconstruction (p J z D S y B : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hs : Γ ⊢[PRAAx] le one S)
    (hm : Γ ⊢[PRAAx] sineMargins p J z D) (hsep : Γ ⊢[PRAAx] separation (roots p J z) S)
    (hy : Γ ⊢[PRAAx] bounded y B one) :
    Γ ⊢[PRAAx] distanceBounded (evaluate (coefficients J) y) (product (roots p J z) J y)
      (errorNumerator (D*positiveBudget J) S J (B+num 8) J) (unit p) :=
  reconstruction_distance _ _ _ _ _ _ _ _ (coefficients_length J) (roots_length p J z) (coefficients_monic J)
    (unit_positive p) hs (root_residuals p J z D hd hm) hsep (root_differences p J z y B hy)

theorem normalization_at_four (p J z D S : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hs : Γ ⊢[PRAAx] le one S)
    (hm : Γ ⊢[PRAAx] sineMargins p J z D) (hsep : Γ ⊢[PRAAx] separation (roots p J z) S) :
    Γ ⊢[PRAAx] distanceBounded (naturalPoint (succ (two*J))) (product (roots p J z) J (naturalPoint (num 4)))
      (errorNumerator (D*positiveBudget J) S J (num 4+num 8) J) (unit p) :=
  GaussianRationalDistanceOrder.distance_congr (GaussianSineSquaredNormalization.normalization J)
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (reconstruction p J z D S (naturalPoint (num 4)) (num 4) hd hs hm hsep
      (GaussianNamedNaturalScale.natural_point_bound _))

theorem actual_sine_sample_root_list_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ entry (roots (var 0) (var 1) (var 2)) (var 3) ≐
      rootSample (var 0) (succ (var 3)) (var 1) (var 2)) :=
  closeUniv 4 (.impI (roots_at _ _ _ _ Prf.hyp0))

theorem actual_sine_sample_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (((le one (var 3) ⋏ le one (var 4)) ⋏ (sineMargins (var 0) (var 1) (var 2) (var 3) ⋏
        separation (roots (var 0) (var 1) (var 2)) (var 4))) ⟶ bounded (var 5) (var 6) one ⟶
      distanceBounded (evaluate (coefficients (var 1)) (var 5)) (product (roots (var 0) (var 1) (var 2)) (var 1) (var 5))
        (errorNumerator (var 3*positiveBudget (var 1)) (var 4) (var 1) (var 6+num 8) (var 1)) (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (reconstruction _ _ _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂
    Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineSampleRootList
