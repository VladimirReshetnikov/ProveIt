import IPRADerivations.Analysis.GaussianStirlingAllOrderLogTruncation
import IPRADerivations.Analysis.GaussianSignedNameExponentialOrder

/-!
# Real samples of the actual periodic kernel and its signed scale

The name at each precision returns the original embedded scalar
prefix at the explicitly advanced normalization clock. Scaling
by the literal signed coefficient preserves its real axis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperAxis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderImproperName (nameF data raw rawF rawData rate raw_at)
open GaussianStirlingAllOrderPanelPartsBinding (prefixAt)
open GaussianStirlingAllOrderLogTruncation (signedF signedData)
open GaussianStirlingAllOrderTruncationAlgebra (signedScale)
open GaussianStirlingAllOrderPanelPartsNames (constantCap)
open GaussianBoundedConstantProductName (sample_at)
open GaussianFastValueCut (name_at exponent)
open GaussianNamedSmallPerturbationTransport (recode_fixed)
open GaussianNameArithmetic (recode_congr)
open GaussianRationalHorner (canonical_congr qmul_canonical)
open GaussianSignedNameExponentialOrder (realSamples)
open RationalGaussianEmbedding (embed embed_canonical embed_axis axis_congr axis_multiply)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sample_readback (m : ℕ) (p A B : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF m) p (data m A B) ≐ raw m (exponent (rate m B) p) A B := by
  let j := exponent (rate m B) p
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (raw m j A B) := embed_canonical _
  exact (name_at (rawF m) (rate m B) (rawData A B) p).eqTrans
    ((recode_congr (raw_at m j A B)).eqTrans (recode_fixed _ hc))

theorem real_at (m : ℕ) (p A B : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF m) p (data m A B)) ⋏
      RationalGaussianEmbedding.axis (ap2 (nameF m) p (data m A B)) := by
  have h := sample_readback (Γ := Γ) m p A B
  exact .andI (canonical_congr h (embed_canonical _)) (axis_congr h.eqSymm (embed_axis _))

theorem signed_real_at (m : ℕ) (p A B : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (signedF m) p (signedData m A B)) ⋏
      RationalGaussianEmbedding.axis (ap2 (signedF m) p (signedData m A B)) := by
  let c : PTm n := signedScale m
  let j := exponent (constantCap c) p
  have h := sample_at (Γ := Γ) (nameF m) p (constantCap c) c (data m A B)
  exact .andI (canonical_congr h (qmul_canonical _ _))
    (axis_congr h.eqSymm (axis_multiply _ _ (embed_axis _) (real_at m j A B).andE₂))

theorem real_samples (m : ℕ) (A B : PTm n) : Γ ⊢[PRAAx] realSamples (nameF m) (data m A B) := by
  refine .allI ?_
  simpa only [Syn.shift,GaussianStirlingAllOrderImproperName.subst_data] using
    real_at (Γ := Γ.map Fm.shift) m (var 0) (Syn.shift A) (Syn.shift B)

theorem signed_real_samples (m : ℕ) (A B : PTm n) : Γ ⊢[PRAAx] realSamples (signedF m) (signedData m A B) := by
  refine .allI ?_
  simpa only [Syn.shift,GaussianStirlingAllOrderLogTruncation.subst_signedData] using
    signed_real_at (Γ := Γ.map Fm.shift) m (var 0) (Syn.shift A) (Syn.shift B)

theorem actual_improper_real_samples_closed (m : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (realSamples (nameF m) (data m (var 0) (var 1))) :=
  closeUniv 2 (real_samples m _ _)

theorem actual_signed_improper_real_samples_closed (m : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (realSamples (signedF m) (signedData m (var 0) (var 1))) :=
  closeUniv 2 (signed_real_samples m _ _)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperAxis
