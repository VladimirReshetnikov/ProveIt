import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductName
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.FiniteOperations.GaussianBoundedInverseApartness

/-!
# Appending one row to a named Gaussian product

The literal last row can be split off as an ordinary named
multiplication. The full product, the prefix product, and the
last row keep their independently normalized observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductAppend

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiplyRawF multiplyModulus multiply_raw_at
  multiply_regular product_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast normalized_to_sample multiply_one_left)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ rowBoundsAt rowDistance)
open GaussianNamedFiniteProductName (nameF data name_at rawF rawData raw_at raw_regular rowBounds rowRegular
  modulus name_regular name_bound)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lastRow (f : PR 3) (g : PR 2) (N x y : PTm n) : Fm PTm n :=
  .all (ap3 f (var 0) (Syn.shift N) (Syn.shift x) ≐ ap2 g (var 0) (Syn.shift y))

@[simp] theorem subst_lastRow {l : ℕ} (σ : Fin n → PTm l) (f : PR 3) (g : PR 2) (N x y : PTm n) :
    (lastRow f g N x y).subst σ = lastRow f g (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [lastRow,Syn.subst_shift,Syn.shift_subst]

theorem last_row_at (f : PR 3) (g : PR 2) (p N x y : PTm n) (h : Γ ⊢[PRAAx] lastRow f g N x y) :
    Γ ⊢[PRAAx] ap3 f p N x ≐ ap2 g p y := by
  simpa only [lastRow,Fm.subst_eq,subst_ap3,subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem empty_cross (f : PR 3) (R L x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) oneF (data zero R L x) x := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have exactValue := (name_at (Γ := Δ) f p zero (sh R) (sh L) (sh x)).eqTrans (sample_zero _ _ _)
  have h := cross_at (Γ := Δ) oneF oneF (sh x) (sh x) p q (cross_refl _ _ (one_fast _))
  simpa [Δ,sh,p,q,Syn.shift] using
    distance_congr ((one_at p (sh x)).eqTrans exactValue.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _) h

theorem empty_bounds (f : PR 3) (R x : PTm n) : Γ ⊢[PRAAx] rowBounds f zero R x := by
  simp only [rowBounds,rowBoundsAt,Syn.shift,ConciseIPRA.PTm.subst_zero]
  refine .allI (.allI (.impI ?_))
  exact lt_zero_absurd _ Prf.hyp0

theorem empty_regular (f : PR 3) (L x : PTm n) : Γ ⊢[PRAAx] rowRegular f zero L x := by
  simp only [rowRegular,rowDistance,Syn.shift,ConciseIPRA.PTm.subst_zero]
  refine .allI (.allI (.allI (.impI ?_)))
  exact lt_zero_absurd _ Prf.hyp0

private def errorBudget (g : PR 2) (N R L y : PTm n) : PTm n := (modulus N R L+one)*U g y

private theorem append_error (f : PR 3) (g : PR 2) (p N R L x y : PTm n)
    (hb : Γ ⊢[PRAAx] rowBounds f N R x) (hr : Γ ⊢[PRAAx] rowRegular f N L x)
    (hg : Γ ⊢[PRAAx] pointCN g y) (he : Γ ⊢[PRAAx] lastRow f g N x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (rawF f) p (rawData (succ N) x))
      (ap2 (multiplyRawF (nameF f) g) p (GaussianNameArithmetic.data (data N R L x) y))
      (errorBudget g N R L y) (unit p) := by
  let a := ap2 (rawF f) p (rawData N x)
  let b := ap2 (nameF f) p (data N R L x)
  let c := ap2 g p y
  have h := unit_positive (Γ := Γ) p
  have dx := normalized_to_sample (rawF f) (modulus N R L) (rawData N x) p (raw_regular f N R L x hb hr)
  have left := (raw_at (Γ := Γ) f p (succ N) x).eqTrans ((sample_succ f p N x).eqTrans
    (qmul_congr (raw_at f p N x).eqSymm (last_row_at f g p N x y he)))
  have right := multiply_raw_at (Γ := Γ) (nameF f) g p (data N R L x) y
  exact distance_congr left.eqSymm right.eqSymm (by unfold errorBudget; ipra_ring) (.eqRefl _)
    (product_distance a b c c (modulus N R L+one) zero (unit p) (U g y)
      (GaussianNamedFiniteProduct.radius R N) h (distance_symmetric _ _ _ _ h dx)
      (distance_refl_zero c (unit p) h) (sample_bound g y p hg) (name_bound f p N R L x hb))

theorem append_cross (f : PR 3) (g : PR 2) (N R S L M x y : PTm n)
    (hb : Γ ⊢[PRAAx] rowBounds f N R x) (hr : Γ ⊢[PRAAx] rowRegular f N L x)
    (hB : Γ ⊢[PRAAx] rowBounds f (succ N) S x) (hR : Γ ⊢[PRAAx] rowRegular f (succ N) M x)
    (hg : Γ ⊢[PRAAx] pointCN g y) (he : Γ ⊢[PRAAx] lastRow f g N x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (multiplyF (nameF f) g)
      (data (succ N) S M x) (multiplyData (nameF f) g (data N R L x) y) := by
  have hp := name_regular f N R L x hb hr
  refine GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _
    (errorBudget g N R L y) (raw_regular f (succ N) S M x hB hR)
    (multiply_regular (nameF f) g (data N R L x) y hp hg) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have b : Δ ⊢[PRAAx] rowBounds f (sh N) (sh R) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hb.shift
  have r : Δ ⊢[PRAAx] rowRegular f (sh N) (sh L) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hr.shift
  have v : Δ ⊢[PRAAx] pointCN g (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hg.shift
  have e : Δ ⊢[PRAAx] lastRow f g (sh N) (sh x) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using he.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,errorBudget,Syn.shift,sh,Δ] using
    append_error f g (var 0) (sh N) (sh R) (sh L) (sh x) (sh y) b r v e

theorem singleton_cross (f : PR 3) (g : PR 2) (R L x y : PTm n)
    (hb : Γ ⊢[PRAAx] rowBounds f one R x) (hr : Γ ⊢[PRAAx] rowRegular f one L x)
    (hg : Γ ⊢[PRAAx] pointCN g y) (he : Γ ⊢[PRAAx] lastRow f g zero x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) g (data one R L x) y := by
  let X := data zero R L x
  have h0 := name_regular f zero R L x (empty_bounds (Γ := Γ) f R x) (empty_regular f L x)
  have h1 : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF X y :=
    cross_trans _ _ _ _ _ _ (empty_cross f R L x) (GaussianBoundedInverseApartness.ones_equivalent x y)
  have product := multiply_cross (nameF f) oneF g g X y y y h0 (one_fast y) hg hg h1 (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ (append_cross f g zero R R L L x y (empty_bounds _ _ _) (empty_regular _ _ _)
    hb hr hg he) (cross_trans _ _ _ _ _ _ product (multiply_one_left g y hg))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductAppend
