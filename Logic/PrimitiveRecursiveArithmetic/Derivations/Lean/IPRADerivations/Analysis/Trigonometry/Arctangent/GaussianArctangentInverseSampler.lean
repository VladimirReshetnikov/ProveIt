import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentClampedTarget
import IPRADerivations.Analysis.Geometry.GaussianRationalHalfAngle
import IPRADerivations.Analysis.RationalArithmetic.RationalCubeMidpoint

/-!
# The actual rational sampler for the inverse arctangent

At each precision the program decodes the imaginary coordinate of the
supplied angle sample. It clamps the finite crossing to the unit
interval and returns the selected index divided by the actual mesh.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentInverseSampler

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code scale oneCode zeroCode im eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentClampedTarget (clamped clamped_le clampedSpec native_clamped zero_index)
open GaussianArctangentExponentialPrefix (source)
open GaussianArctangentRationalTarget (targetPoint)
open GaussianRationalHorner (canonical canonical_unique ofGaussian ofGaussian_represents ofGaussian_canonical
  represents represents_congr scalar_congr qzero zero_represents)
open GaussianRootAlgebra (equal equal_of_values re_one im_one re_scale im_scale)
open RationalIntegerNormalization (positivePart)
open RationalSupMetric (numeratorOf denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def ordinate (f : PR 2) (p x : PTm n) : PTm n := sndT (ap2 f p x)
def targetNumerator (f : PR 2) (p x : PTm n) : PTm n := positivePart (numeratorOf (ordinate f p x))
def targetDenominator (f : PR 2) (p x : PTm n) : PTm n := denominatorOf (ordinate f p x)
def mesh (p : PTm n) : PTm n := GaussianArctangentPartialQuadrature.mesh p
def clearing (f : PR 2) (p x : PTm n) : PTm n :=
  two*(mesh p*mesh p)+two*targetDenominator f p x
def index (f : PR 2) (p x : PTm n) : PTm n :=
  clamped (targetNumerator f p x) (targetDenominator f p x) (mesh p) (clearing f p x)
def raw (f : PR 2) (p x : PTm n) : PTm n :=
  RationalGaussianEmbedding.embed (RationalCubeMidpoint.fraction (index f p x) (mesh p))
def rawF (f : PR 2) : PR 2 := PTm.toPR (raw f (var 0) (var 1) : PTm 2)
def signedTarget (f : PR 2) (p x : PTm n) : PTm n :=
  ofGaussian (code (ZT.ofNat zero) (numeratorOf (ordinate f p x))) (targetDenominator f p x)

@[simp] theorem subst_ordinate {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (ordinate f p x) = ordinate f (Syn.subst σ p) (Syn.subst σ x) := by simp [ordinate]
@[simp] theorem subst_targetNumerator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (targetNumerator f p x) = targetNumerator f (Syn.subst σ p) (Syn.subst σ x) := by
  simp [targetNumerator,numeratorOf,ZT.subst]
@[simp] theorem subst_targetDenominator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (targetDenominator f p x) = targetDenominator f (Syn.subst σ p) (Syn.subst σ x) := by
  simp [targetDenominator,denominatorOf]
@[simp] theorem subst_mesh {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (mesh p) = mesh (Syn.subst σ p) := by simp [mesh]
@[simp] theorem subst_clearing {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (clearing f p x) = clearing f (Syn.subst σ p) (Syn.subst σ x) := by simp [clearing]

private theorem subst_crossing {m : ℕ} (σ : Fin n → PTm m) (T M L : PTm n) :
    Syn.subst σ (GaussianArctangentGridSearch.crossing T M L) =
      GaussianArctangentGridSearch.crossing (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ L) := by
  unfold GaussianArctangentGridSearch.crossing
  simp only [Search.mu,subst_ap2,ConciseIPRA.PTm.subst_succ]
  refine congrArg (ap2 _ (succ (Syn.subst σ M))) ?_
  change Syn.subst σ (pairT T (pairT M L)) = pairT (Syn.subst σ T) (pairT (Syn.subst σ M) (Syn.subst σ L))
  simp

private theorem subst_clamped {m : ℕ} (σ : Fin n → PTm m) (Q D M L : PTm n) :
    Syn.subst σ (clamped Q D M L) = clamped (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [clamped,GaussianArctangentRationalTarget.chosen,GaussianArctangentRationalTarget.target,
    subst_crossing,Products.fact]

@[simp] theorem subst_index {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (index f p x) = index f (Syn.subst σ p) (Syn.subst σ x) := by
  simp only [index,subst_clamped,subst_targetNumerator,subst_targetDenominator,subst_mesh,subst_clearing]
@[simp] theorem subst_raw {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (raw f p x) = raw f (Syn.subst σ p) (Syn.subst σ x) := by
  simp [raw,RationalCubeMidpoint.fraction]
@[simp] theorem subst_signedTarget {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (signedTarget f p x) = signedTarget f (Syn.subst σ p) (Syn.subst σ x) := by
  simp only [signedTarget,GaussianRationalHorner.subst_ofGaussian,ComplexLogarithmRemainder.subst_code,
    ZT.subst_ofNat,ConciseIPRA.PTm.subst_zero,subst_targetDenominator]
  simp [numeratorOf,ZT.subst]

theorem raw_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (rawF f) p x ≐ raw f p x := by
  simpa only [rawF,ap2,subst_raw,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (raw f (var 0) (var 1) : PTm 2) ![p,x]

theorem mesh_positive (p : PTm n) : Γ ⊢[PRAAx] le one (mesh p) :=
  GaussianArctangentPartialQuadrature.mesh_positive p

theorem target_denominator_positive (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] le one (targetDenominator f p x) :=
  RationalArgmin.denominator_positive _

theorem source_certificate (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] source (mesh p) (clearing f p x) :=
  .andI (mesh_positive p) (le_add_right _ _)

theorem target_clearing (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] le (two*targetDenominator f p x) (clearing f p x) :=
  le_add_left _ _

theorem index_le (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le (index f p x) (mesh p) :=
  clamped_le _ _ _ _ (target_denominator_positive f p x) (target_clearing f p x)

theorem index_spec (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] clampedSpec (targetNumerator f p x) (targetDenominator f p x) (mesh p) (clearing f p x) :=
  native_clamped _ _ _ _ (source_certificate f p x) (target_denominator_positive f p x) (target_clearing f p x)

theorem raw_represents (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] represents (raw f p x) (scale (index f p x) oneCode) (mesh p) := by
  let j := index f p x
  let M := mesh p
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _)
    (RationalGaussianEmbedding.embed_from_representation _ _ _
      (RationalCubeMidpoint.fraction_represents j M (mesh_positive p)))
  apply equal_of_values <;>
    simp only [RationalGaussianEmbedding.native,eval_re_code,eval_im_code,re_scale,im_scale,re_one,im_one,ZT.toZ_ofNat] <;>
    (try ipra_simps) <;> ring

theorem raw_real_represents (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (raw f p x)) (ZT.ofNat (index f p x)) (mesh p) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (raw_represents f p x).andE₁
  apply ZT.derive
  simp only [re_scale,re_one,ZT.toZ_ofNat]
  ring

theorem raw_canonical (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] canonical (raw f p x) :=
  RationalGaussianEmbedding.embed_canonical _

theorem raw_axis (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (raw f p x) :=
  RationalGaussianEmbedding.embed_axis _

theorem raw_embedding (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    raw f p x ≐ RationalGaussianEmbedding.embed (RationalCubeMidpoint.fraction (index f p x) (mesh p)) :=
  .eqRefl _

theorem ordinate_represents (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (ordinate f p x) (numeratorOf (ordinate f p x)) (targetDenominator f p x) :=
  .eqRefl _

theorem signed_target_ordinate_represents (f : PR 2) (p x : PTm n) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (sndT (signedTarget f p x))
      (numeratorOf (ordinate f p x)) (targetDenominator f p x) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ (target_denominator_positive f p x)).andE₂
  exact ZT.derive (eval_im_code _ _)

theorem nonnegative_numerator_value (f : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).neg (numeratorOf (ordinate f p x)).pos) :
    ZT.toZ Γ (ZT.ofNat (targetNumerator f p x)) = ZT.toZ Γ (numeratorOf (ordinate f p x)) :=
  GaussianRationalHalfAngle.positive_part_value _ h

theorem nonnegative_target_readback (f : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).neg (numeratorOf (ordinate f p x)).pos) :
    Γ ⊢[PRAAx] targetPoint (targetNumerator f p x) (targetDenominator f p x) ≐ signedTarget f p x := by
  let a := scale (targetNumerator f p x) imaginaryCode
  let b := code (ZT.ofNat zero) (numeratorOf (ordinate f p x))
  let D := targetDenominator f p x
  have hD := target_denominator_positive (Γ := Γ) f p x
  have e : Γ ⊢[PRAAx] equal a b := by
    apply equal_of_values
    · simp only [a,b,re_scale,imaginaryCode,eval_re_code,ZT.toZ_ofNat]
      ipra_simps
      ring
    · simp only [a,b,im_scale,imaginaryCode,eval_im_code,ZT.toZ_ofNat]
      have hv := nonnegative_numerator_value f p x h
      rw [ZT.toZ_ofNat] at hv
      ipra_simps
      linear_combination hv
  exact canonical_unique _ _ b D (ofGaussian_canonical _ _ hD) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ hD)) (ofGaussian_represents _ _ hD)

theorem nonpositive_index_zero (f : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).pos (numeratorOf (ordinate f p x)).neg) :
    Γ ⊢[PRAAx] index f p x ≐ zero := by
  let Q := targetNumerator f p x
  let D := targetDenominator f p x
  let M := mesh p
  let L := clearing f p x
  have hQ : Γ ⊢[PRAAx] Q ≐ zero := h
  have e : Γ ⊢[PRAAx] clamped Q D M L ≐ clamped zero D M L := by
    simpa only [subst_clamped,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (clamped (var 0) (var 1) (var 2) (var 3) : PTm 4)
        (σ := ![Q,D,M,L]) (σ' := ![zero,D,M,L])
        (fun i => by fin_cases i; exact hQ; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
  exact e.eqTrans (zero_index _ _ _ (target_denominator_positive f p x) (target_clearing f p x))

theorem raw_zero (f : PR 2) (p x : PTm n) (h : Γ ⊢[PRAAx] index f p x ≐ zero) :
    Γ ⊢[PRAAx] raw f p x ≐ qzero := by
  have hp := mesh_positive (Γ := Γ) p
  have e : Γ ⊢[PRAAx] equal (scale (index f p x) oneCode) zeroCode := by
    apply equal_of_values
    · have he := natEq h
      simp only [re_scale,re_one,GaussianRootAlgebra.re_zero]
      ipra_simps
      linear_combination he
    · simp only [im_scale,im_one,GaussianRootAlgebra.im_zero]
      ring
  exact canonical_unique _ _ zeroCode (mesh p) (raw_canonical _ _ _) GaussianRationalSyntheticDivision.qzero_canonical
    hp (represents_congr (.eqRefl _) e (.eqRefl _) (raw_represents f p x)) (zero_represents _)

theorem nonpositive_raw_zero (f : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] le (numeratorOf (ordinate f p x)).pos (numeratorOf (ordinate f p x)).neg) :
    Γ ⊢[PRAAx] raw f p x ≐ qzero :=
  raw_zero f p x (nonpositive_index_zero f p x h)

theorem actual_arctangent_inverse_sampler_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((ap2 (rawF f) (var 0) (var 1) ≐ raw f (var 0) (var 1)) ⋏
        le (index f (var 0) (var 1)) (mesh (var 0))) :=
  closeUniv 2 (.andI (raw_at f _ _) (index_le f _ _))

theorem actual_arctangent_inverse_nonpositive_zero_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le (numeratorOf (ordinate f (var 0) (var 1))).pos (numeratorOf (ordinate f (var 0) (var 1))).neg ⟶
        ap2 (rawF f) (var 0) (var 1) ≐ qzero) :=
  closeUniv 2 (.impI ((raw_at f _ _).eqTrans (nonpositive_raw_zero f _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentInverseSampler
