import OAI.Combinatorics.Progressions.Estimates.AllocatedNormalizedSiteTwist

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {n : Fin m → ℕ} {E : Fin m → Type*}

noncomputable def mixedSiteResidueReduction {period M : ℕ} (h : period ∣ M)
    (w : (∀ j, Fin (n j) → ZMod M) × (∀ j, E j → ZMod M)) :
    (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period) :=
  (fun j i => ZMod.castHom h (ZMod period) (w.1 j i),
   fun j i => ZMod.castHom h (ZMod period) (w.2 j i))

theorem mixedSiteResidueReduction_cast {I : Fin m → Type*} (d period M : ℕ) (h : period ∣ M)
    (w : MixedCoveredJetSource I (fun _ => Unit) E n d) :
    mixedSiteResidueReduction h (mixedCoveredSiteResidue d M w) = mixedCoveredSiteResidue d period w := by
  simp only [mixedSiteResidueReduction, mixedCoveredSiteResidue, map_intCast, map_natCast]

variable {A V : Type*} (e : A → ScalarSiteExpansion V) (k : ∀ a, (e a).Term)
variable (selected : A → Σ j : Fin m, Fin (n j))

noncomputable def mixedSiteGridResidue {M : ℕ} (h : ∀ a, (e a).period (k a) ∣ M)
    (w : (∀ j, Fin (n j) → ZMod M) × (∀ j, E j → ZMod M)) : ∀ a, ZMod ((e a).period (k a)) :=
  fun a => ZMod.castHom (h a) (ZMod ((e a).period (k a))) (w.1 (selected a).1 (selected a).2)

theorem mixedSiteGridResidue_cast {I : Fin m → Type*} (d M : ℕ)
    (h : ∀ a, (e a).period (k a) ∣ M)
    (w : MixedCoveredJetSource I (fun _ => Unit) E n d) :
    mixedSiteGridResidue e k selected h (mixedCoveredSiteResidue d M w) =
      fun a => ((w.1 (selected a).1).2 (selected a).2 () : ZMod ((e a).period (k a))) := by
  funext a
  change ZMod.castHom (h a) (ZMod ((e a).period (k a)))
    (((w.1 (selected a).1).2 (selected a).2 () : ℤ) : ZMod M) = _
  exact map_intCast _ _

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) {spatialPeriod period M : ℕ}
variable (hs : ∀ x, q x * spatialPeriod ∣ M)
variable (hg : ∀ a, (e a).period (k a) ∣ M) (hi : period ∣ M)
variable (t : X → SpatialSiteLabel α spatialPeriod b r) (s : Finset α)
variable (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
variable (gridLabel : ∀ a, ZMod ((e a).period (k a)))

variable [DecidableEq (∀ a, ZMod ((e a).period (k a)))]

noncomputable def allocatedCommonResidueMask (u : X → ZMod M)
    (w : (∀ j, Fin (n j) → ZMod M) × (∀ j, E j → ZMod M)) : ℂ :=
  (physicalResidueSpatialMaskMod root D base residue q b r hs t s u *
    (if mixedSiteResidueReduction hi w = label then (1 : ℂ) else 0)) *
    (if mixedSiteGridResidue e k selected hg w = gridLabel then (1 : ℂ) else 0)

theorem allocatedCommonResidueMask_eval {I : Fin m → Type*} (d : ℕ)
    (u : X → ℤ) (w : MixedCoveredJetSource I (fun _ => Unit) E n d) :
    allocatedCommonResidueMask e k selected root D base residue q b r hs hg hi t s label gridLabel
      (fun x => (u x : ZMod M)) (mixedCoveredSiteResidue d M w) =
    (physicalResidueSpatialMask root D base residue q b r t s u *
      (if mixedCoveredSiteResidue d period w = label then (1 : ℂ) else 0)) *
      (if (fun a => ((w.1 (selected a).1).2 (selected a).2 () : ZMod ((e a).period (k a)))) = gridLabel
        then (1 : ℂ) else 0) := by
  simp only [allocatedCommonResidueMask, physicalResidueSpatialMaskMod_eval,
    mixedSiteResidueReduction_cast, mixedSiteGridResidue_cast]

theorem allocatedCommonResidueMask_norm (u : X → ZMod M)
    (w : (∀ j, Fin (n j) → ZMod M) × (∀ j, E j → ZMod M)) :
    ‖allocatedCommonResidueMask e k selected root D base residue q b r hs hg hi t s label gridLabel u w‖ ≤ 1 := by
  unfold allocatedCommonResidueMask
  split_ifs <;> simp only [mul_one, mul_zero, norm_zero, zero_le_one]
  exact physicalResidueSpatialMaskMod_norm root D base residue q b r hs t s u

end Erdos3.VectorPolynomial

end

end OAI
