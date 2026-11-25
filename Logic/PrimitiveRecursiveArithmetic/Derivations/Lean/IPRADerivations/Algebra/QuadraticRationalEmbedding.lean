import IPRADerivations.Algebra.QuadraticRationalCongruence
import IPRADerivations.Core.CertificateTactics

/-!
# Original rational scalars and the actual positive quadratic root

The actual scalar map q ↦ (q,0) reflects original rational equality and
strict order, through its proved positive-denominator representation.
The actual rational pair (0,1) is positive and its actual square equals
the original normalized integer radicand in sign-zero equality.
Only a positive INTEGER radicand is used; rational radicands and towers
remain distinct source obligations.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalEq left)
open QuadraticSignCertificates (first second equal negative_first negative_second)
open QuadraticConeOrder (equal_of_values equal_symm add_first add_second)
open QuadraticIntegerEmbedding (integer integer_first integer_second)
open QuadraticRationalClearing (represents)
open QuadraticRationalPairArithmetic (positive isZero multiply)
open QuadraticRationalEqualityOrder (difference equivalent less cross)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def zeroScalar : PTm n := QuadraticRationalPairArithmetic.scalar zero
def oneScalar : PTm n := QuadraticRationalPairArithmetic.scalar one
def embed (q : PTm n) : PTm n := pairT q zeroScalar
def root : PTm n := pairT zeroScalar oneScalar
def crossNumerator (q r : PTm n) : ZT n := numeratorOf q*ZT.ofNat (denominatorOf r)-numeratorOf r*ZT.ofNat (denominatorOf q)
@[simp] theorem subst_zeroScalar {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (zeroScalar : PTm n) = (zeroScalar : PTm l) := by simp [zeroScalar]
@[simp] theorem subst_oneScalar {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (oneScalar : PTm n) = (oneScalar : PTm l) := by simp [oneScalar,one]
@[simp] theorem subst_embed {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) :
    Syn.subst σ (embed q) = embed (Syn.subst σ q) := by simp [embed]
@[simp] theorem subst_root {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (root : PTm n) = (root : PTm l) := by simp [root]
@[simp] theorem subst_crossNumerator {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    (crossNumerator q r).subst σ = crossNumerator (Syn.subst σ q) (Syn.subst σ r) := by simp [crossNumerator]

theorem zero_scalar_represents (D : PTm n) : Γ ⊢[PRAAx]
    LeanProofs.IPRA.Analysis.RationalArithmetic.represents zeroScalar (ZT.ofNat zero) D := by
  change Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents
    (QuadraticRationalPairArithmetic.scalar zero) (ZT.ofNat zero) D
  ipra_lc 𝔞(D)*ZT.toZ_eq (QuadraticRationalPairArithmetic.scalar_represents (Γ := Γ) zero)
theorem embedding_represents (q D : PTm n) (a : ZT n)
    (hq : Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.RationalArithmetic.represents q a D) : Γ ⊢[PRAAx]
    represents (embed q) (integer a) D := by
  refine .andI ?_ ?_
  · apply QuadraticRationalPairArithmetic.scalar_code_congr _ _ (fst_pair _ _)
    exact QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ (integer_first a).symm hq
  · apply QuadraticRationalPairArithmetic.scalar_code_congr _ _ (snd_pair _ _)
    apply QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ ?_ (zero_scalar_represents D)
    rw [ZT.toZ_ofNat,integer_second]; ipra_simps
theorem original_embedding_represents (q : PTm n) : Γ ⊢[PRAAx]
    represents (embed q) (integer (numeratorOf q)) (denominatorOf q) :=
  embedding_represents _ _ _ (LeanProofs.IPRA.Analysis.RationalRepresentations.represents_self q)
theorem embedding_sign (d q : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sign d (embed q) ≐ QuadraticSignCertificates.tag (numeratorOf q) :=
  (QuadraticRationalClearing.representation_sign _ _ _ _ hd (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive q)
    (original_embedding_represents q)).eqTrans (QuadraticIntegerEmbedding.integer_sign _ _ hd)
theorem scalar_cross (q r : PTm n) : Γ ⊢[PRAAx]
    equal (cross (integer (numeratorOf q)) (denominatorOf q) (integer (numeratorOf r)) (denominatorOf r))
      (integer (crossNumerator q r)) := by
  apply equal_of_values <;> simp only [cross,crossNumerator,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,
    integer_first,integer_second,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat] <;> ring
theorem embedding_difference_sign (d q r : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sign d (difference (embed q) (embed r)) ≐
      QuadraticSignCertificates.sign d (integer (crossNumerator q r)) :=
  (QuadraticRationalClearing.representation_sign _ _ _ _ hd
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product
      (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive q) (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive r))
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ (original_embedding_represents q) (original_embedding_represents r))).eqTrans
      (QuadraticConeOrder.sign_congr _ _ _ hd (scalar_cross q r))
theorem rational_eq_of_cross_zero (q r : PTm n) (h : Γ ⊢[PRAAx] ZT.eq (crossNumerator q r) (ZT.ofNat zero)) : Γ ⊢[PRAAx] rationalEq q r := by
  apply LeanProofs.IPRA.Analysis.RationalArithmetic.value_equality
  ipra_lc [crossNumerator] ZT.toZ_eq h
theorem cross_zero_of_rational_eq (q r : PTm n) (h : Γ ⊢[PRAAx] rationalEq q r) : Γ ⊢[PRAAx]
    ZT.eq (crossNumerator q r) (ZT.ofNat zero) := by
  apply ZT.derive
  have e := natEq h
  simp only [left,Q.mk_add,Q.mk_mul,map_add,map_mul] at e
  simp only [crossNumerator,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_zero,map_zero]
  simp only [ZT.toZ]
  linear_combination e
theorem embedding_equal_reflect (d q r : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equivalent d (embed q) (embed r)) : Γ ⊢[PRAAx] rationalEq q r :=
  rational_eq_of_cross_zero _ _ (QuadraticIntegerEmbedding.integer_zero_reflect _ _ hd
    ((embedding_difference_sign _ _ _ hd).eqSymm.eqTrans h))
theorem embedding_equivalent (d q r : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] rationalEq q r) : Γ ⊢[PRAAx] equivalent d (embed q) (embed r) :=
  (embedding_difference_sign _ _ _ hd).eqTrans
    (QuadraticIntegerEmbedding.integer_isZero _ _ hd (cross_zero_of_rational_eq _ _ h))
theorem embedding_injective_iff (d q r : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (equivalent d (embed q) (embed r)) (rationalEq q r) :=
  .andI (.impI (embedding_equal_reflect _ _ _ hd.wk Prf.hyp0)) (.impI (embedding_equivalent _ _ _ hd.wk Prf.hyp0))

theorem strict_cross (q r : PTm n) (h : Γ ⊢[PRAAx] lt (left q r) (left r q)) : Γ ⊢[PRAAx]
    zle (ZT.ofNat one) (crossNumerator r q) := by
  apply zle_of_comb (sl h) ?_ (nn_sl h)
  simp only [crossNumerator,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat,sl_def,left]
  simp only [ZT.toZ]
  ipra_simps; ring
theorem strict_of_cross (q r : PTm n) (h : Γ ⊢[PRAAx] zle (ZT.ofNat one) (crossNumerator r q)) : Γ ⊢[PRAAx]
    lt (left q r) (left r q) := by
  apply le_of_comb (zsl h) ?_ (nn_zsl h)
  simp only [crossNumerator,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat,zsl_def,left]
  simp only [ZT.toZ]
  ipra_simps; ring
theorem embedding_less (d q r : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] lt (left q r) (left r q)) : Γ ⊢[PRAAx] less d (embed q) (embed r) :=
  (embedding_difference_sign _ _ _ hd).eqTrans (QuadraticIntegerEmbedding.integer_positive _ _ hd (strict_cross _ _ h))
theorem embedding_less_reflect (d q r : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] less d (embed q) (embed r)) : Γ ⊢[PRAAx] lt (left q r) (left r q) :=
  strict_of_cross _ _ (QuadraticIntegerEmbedding.integer_positive_reflect _ _ hd ((embedding_difference_sign _ _ _ hd).eqSymm.eqTrans h))
theorem embedding_order_iff (d q r : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    Fm.iff (less d (embed q) (embed r)) (lt (left q r) (left r q)) :=
  .andI (.impI (embedding_less_reflect _ _ _ hd.wk Prf.hyp0)) (.impI (embedding_less _ _ _ hd.wk Prf.hyp0))

theorem root_represents : Γ ⊢[PRAAx] represents (root : PTm n) QuadraticIntegerOrder.root one := by
  refine .andI ?_ ?_
  · apply QuadraticRationalPairArithmetic.scalar_code_congr _ _ (fst_pair _ _)
    apply QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ ?_ (zero_scalar_represents one)
    simp only [QuadraticIntegerOrder.root,QuadraticSignCertificates.naturalPair,
      QuadraticSignCertificates.first_value,ZT.toZ_ofNat]
  · apply QuadraticRationalPairArithmetic.scalar_code_congr _ _ (snd_pair _ _)
    apply QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ ?_ (QuadraticRationalPairArithmetic.scalar_represents one)
    simp only [QuadraticIntegerOrder.root,QuadraticSignCertificates.naturalPair,
      QuadraticSignCertificates.second_value,ZT.toZ_ofNat]
theorem root_positive (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] positive d root :=
  (QuadraticRationalClearing.representation_sign _ _ _ _ hd (le_refl one) root_represents).eqTrans
    (QuadraticIntegerOrder.root_positive d hd)
theorem native_unit_cross (A B : PTm n) : Γ ⊢[PRAAx] equal (cross A (one*one) B one) (QuadraticIntegerOrder.difference A B) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,negative_first,negative_second,
    QuadraticPositiveScaling.scale_first,QuadraticPositiveScaling.scale_second,Q.mk_mul,Q.mk_one,map_mul,map_one] <;> ring
theorem root_square (d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    equivalent d (multiply d root root) (embed (QuadraticRationalPairArithmetic.scalar d)) := by
  apply QuadraticRationalCongruence.equivalent_of_representations _ _ _ _ _ _ _ hd
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (le_refl one) (le_refl one)) (le_refl one)
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (le_refl one) (le_refl one) root_represents root_represents)
    (embedding_represents _ _ _ (QuadraticRationalPairArithmetic.scalar_represents d))
  exact QuadraticIntegerOrder.zero_value_congr _ _ _ hd (equal_symm (native_unit_cross _ _)) (QuadraticIntegerOrder.root_square d hd)

def output (d q : PTm n) : PTm n := pairT (embed q)
  (pairT (QuadraticRationalClearing.sign d (embed q)) (pairT root (multiply d root root)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d q : PTm n) : PTm n := ap2 outputF d q
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (d q : PTm n) :
    Syn.subst σ (output d q) = output (Syn.subst σ d) (Syn.subst σ q) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (d q : PTm n) :
    Syn.subst σ (run d q) = run (Syn.subst σ d) (Syn.subst σ q) := by simp [run]
theorem program_at (d q : PTm n) : Γ ⊢[PRAAx] run d q ≐ output d q := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,q]
theorem returned_scalar (d q : PTm n) : Γ ⊢[PRAAx] fstT (run d q) ≐ embed q :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_sign (d q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d q)) ≐ QuadraticRationalClearing.sign d (embed q) :=
  (congrFst ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_root (d q : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d q))) ≐ root :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_square (d q : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d q))) ≐ multiply d root root :=
  (congrSnd ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_exact_sign (d q : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    fstT (sndT (run d q)) ≐ QuadraticSignCertificates.tag (numeratorOf q) :=
  (returned_sign _ _).eqTrans (embedding_sign _ _ hd)

theorem original_rational_scalar_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (represents (embed (var 0)) (integer (numeratorOf (var 0))) (denominatorOf (var 0))) :=
  closeUniv 1 (original_embedding_represents _)
theorem original_rational_scalar_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ QuadraticRationalClearing.sign (var 0) (embed (var 1)) ≐
      QuadraticSignCertificates.tag (numeratorOf (var 1))) := closeUniv 2 (.impI (embedding_sign _ _ Prf.hyp0))
theorem original_rational_scalar_injective_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ Fm.iff (equivalent (var 0) (embed (var 1)) (embed (var 2))) (rationalEq (var 1) (var 2))) :=
  closeUniv 3 (.impI (embedding_injective_iff _ _ _ Prf.hyp0))
theorem original_rational_scalar_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ Fm.iff (less (var 0) (embed (var 1)) (embed (var 2)))
      (lt (left (var 1) (var 2)) (left (var 2) (var 1)))) := closeUniv 3 (.impI (embedding_order_iff _ _ _ Prf.hyp0))
theorem original_rational_positive_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ (positive (var 0) root ⋏
      equivalent (var 0) (multiply (var 0) root root) (embed (QuadraticRationalPairArithmetic.scalar (var 0))))) :=
  closeUniv 1 (.impI (.andI (root_positive _ Prf.hyp0) (root_square _ Prf.hyp0)))
theorem actual_rational_scalar_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem returned_original_rational_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ fstT (sndT (run (var 0) (var 1))) ≐ QuadraticSignCertificates.tag (numeratorOf (var 1))) :=
  closeUniv 2 (.impI (returned_exact_sign _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticRationalEmbedding
