import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerExponentialHead
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerCofinal
import IPRADerivations.Analysis.Gamma.GaussianGammaRightHalfPlane

/-!
# The exponential of the canonical right-half-plane log-Gamma

The cofinal logarithm and every sufficiently late finite head have a
common explicit disk. Their negative exponentials are compared at the
same actual inner precision by the scalar exponential Lipschitz bound.
A single cutoff also satisfies the original reciprocal Gamma rate.
Named exponential inversion then identifies the positive exponential
with the original Gamma name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (qF qData exponential_input)
open GaussianLogGammaEulerCofinal (late_cutoff_distance)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl cross_at)
open GaussianNameRingLaws (negativeF negativeData oneF)
open GaussianRadiusExponentialName (input boundedSamples inputPrecision index)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (qsub qnegative qnegative_canonical distanceBounded bounded)
open GaussianRationalSyntheticDivision (qzero_add)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "H" => GaussianLogGammaEulerNormalizedHead.nameF
local notation "hd" => GaussianLogGammaEulerNormalizedHead.data
local notation "cd" => GaussianLogGammaEulerCofinal.canonicalData
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "gdata" => GaussianGammaC7Name.data
local notation "gf" => GaussianGammaC7Name.nameF
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def disk (A B D neg : PTm n) : PTm n := U F (cd A B D neg)+two
def expF : PR 2 := E F
def expData (A B D neg : PTm n) : PTm n := ed (disk A B D neg) (cd A B D neg)
def reciprocalF : PR 2 := E (negativeF F)
def reciprocalData (A B D neg : PTm n) : PTm n := ed (disk A B D neg) (negativeData (cd A B D neg))

@[simp] theorem subst_disk {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (disk A B D neg) = disk (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by
  simp [disk,two,one]

@[simp] theorem subst_reciprocalData {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (reciprocalData A B D neg) =
      reciprocalData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by simp [reciprocalData]

private theorem original_source (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (native A B neg) (radius A B) D :=
  .andI (GaussianLogGammaEulerResidualRadius.radius_positive A B D neg h)
    (.andI h.andE₂ (GaussianLogGammaEulerResidualRadius.source_of_right_half_plane A B D neg h).andE₂)

private theorem cofinal_input (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] input F (disk A B D neg) (cd A B D neg) := by
  let x := cd A B D neg
  have reg := GaussianLogGammaEulerCofinal.canonical_regular A B D neg h
  have widen : Γ ⊢[PRAAx] le (U F x) (disk A B D neg) := le_add_right (U F x) two
  exact GaussianExponentialRadiusIndependence.input_widen _ _ _ _ (exponential_input _ _ reg) widen

private theorem head_bound (p A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hN : Γ ⊢[PRAAx] le (GaussianLogGammaEulerCofinal.cutoff (radius A B) zero) N) :
    Γ ⊢[PRAAx] bounded (ap2 H p (hd A B D neg N)) (disk A B D neg) one := by
  let R := radius A B
  let x := cd A B D neg
  let a := ap2 F zero x
  let b := ap2 H p (hd A B D neg N)
  let M := U F x
  have hs := GaussianLogGammaEulerResidualRadius.source_of_right_half_plane A B D neg h
  have hp := unit_positive (Γ := Γ) p
  have u0 : Γ ⊢[PRAAx] unit (zero : PTm n) ≐ one := pw_zero two
  have near := distance_congr (GaussianLogGammaEulerCofinal.sample_at zero A B D neg R).eqSymm
    (.eqRefl _) (congrAdd u0 (.eqRefl _)) (congrMul u0 (.eqRefl _))
    (late_cutoff_distance zero p A B D neg R N hs hN)
  have small : Γ ⊢[PRAAx] distanceBounded b a two one :=
    distance_symmetric _ _ _ _ (le_refl one)
      (distance_radius_mono a b _ _ two one (positive_product _ _ (le_refl one) hp) (le_refl one)
        (by ipra_le sl hp) near)
  have base := GaussianNameBounds.sample_bound F x zero (GaussianLogGammaEulerCofinal.canonical_regular A B D neg h)
  have total := GaussianRationalReciprocal.bounded_sum a (qsub b a) M one two one (le_refl _) (le_refl _) base small
  have cb : Γ ⊢[PRAAx] GaussianRationalHorner.canonical b :=
    GaussianNameArithmetic.add_canonical _ _ _ _ p
  exact GaussianRationalReciprocal.bound_congr (GaussianRationalLinearProduct.add_sub_right a b cb)
    (by dsimp only [disk,M]; ipra_ring) (one_mul _) total

private theorem head_input (A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hN : Γ ⊢[PRAAx] le (GaussianLogGammaEulerCofinal.cutoff (radius A B) zero) N) :
    Γ ⊢[PRAAx] input H (disk A B D neg) (hd A B D neg N) := by
  have hpos := le_trans (GaussianLogGammaEulerCofinal.cutoff_positive (radius A B) zero) hN
  refine .andI (GaussianLogGammaEulerNormalizedHead.regular A B D neg N h hpos) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source (sh A) (sh D) (sh neg) := by
    simpa [Fm.shift,Syn.shift,sh,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le (GaussianLogGammaEulerCofinal.cutoff (radius (sh A) (sh B)) zero) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh] using hN.shift
  simpa only [boundedSamples,Syn.shift,GaussianLogGammaEulerNormalizedHead.subst_data,subst_disk,sh]
    using head_bound (var 0) (sh A) (sh B) (sh D) (sh neg) (sh N) hs ns

private def negativeQuery (W p : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (one+one) (inputPrecision W p)

private theorem negative_value (f : PR 2) (x p : PTm n) :
    Γ ⊢[PRAAx] ap2 (negativeF f) p (negativeData x) ≐
      qnegative (ap2 f (GaussianFastValueCut.exponent (one+one) p) x) := by
  let v := ap2 f (GaussianFastValueCut.exponent (one+one) p) x
  exact (GaussianNameRingLaws.negative_at f x p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qzero_add _ (qnegative_canonical v))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qnegative_canonical v)))

private theorem negative_exponentials_near (p A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg)
    (hzero : Γ ⊢[PRAAx] le (GaussianLogGammaEulerCofinal.cutoff (radius A B) zero) N)
    (hlate : Γ ⊢[PRAAx] le (GaussianLogGammaEulerCofinal.cutoff (radius A B) (negativeQuery (disk A B D neg) p)) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 reciprocalF p (reciprocalData A B D neg))
      (ap2 (E (negativeF H)) p (ed (disk A B D neg) (negativeData (hd A B D neg N)))) one (unit p) := by
  let W := disk A B D neg
  let t := inputPrecision W p
  let k := negativeQuery W p
  let R := radius A B
  let x := cd A B D neg
  let y := hd A B D neg N
  let a := ap2 F k x
  let b := ap2 H k y
  let u := ap2 (negativeF F) t (negativeData x)
  let v := ap2 (negativeF H) t (negativeData y)
  let K := index W p
  have hs := GaussianLogGammaEulerResidualRadius.source_of_right_half_plane A B D neg h
  have left := GaussianExponentialInverse.negative_input F W x (cofinal_input A B D neg h)
  have right := GaussianExponentialInverse.negative_input H W y (head_input A B D neg N h hzero)
  have hk := unit_positive (Γ := Γ) k
  have ht := unit_positive (Γ := Γ) t
  have near : Γ ⊢[PRAAx] distanceBounded a b two (unit k) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hk hk) hk (le_of_eq_add (d := zero) (by ipra_ring))
      (distance_congr (GaussianLogGammaEulerCofinal.sample_at k A B D neg R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (late_cutoff_distance k k A B D neg R N hs hlate))
  have changed : Γ ⊢[PRAAx] distanceBounded u v two (unit k) :=
    distance_congr (negative_value F x t).eqSymm (negative_value H y t).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianNamedDifference.negative_distance a b _ _ hk near)
  have clocks : Γ ⊢[PRAAx] le (unit t) (unit k) :=
    GaussianExponentialReference.unit_monotone (le_add_right t _)
  have sameClock : Γ ⊢[PRAAx] distanceBounded u v two (unit t) :=
    distance_radius_mono _ _ _ _ _ _ hk ht
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) clocks) changed
  have raw := GaussianRationalRadiusExponentialLipschitz.scalar_sum_lipschitz u v W two (unit t) K ht
    (GaussianRadiusExponentialName.bounded_samples_at _ _ _ _ left.andE₂)
    (GaussianRadiusExponentialName.bounded_samples_at _ _ _ _ right.andE₂) sameClock
  have small : Γ ⊢[PRAAx] le
      ((GaussianRationalRadiusExponentialLipschitz.factor W K*two)*unit p)
      (num 4*GaussianRationalRadiusExponentialLipschitz.factor W K*unit p) :=
    le_of_eq_add (d := two*GaussianRationalRadiusExponentialLipschitz.factor W K*unit p) (by ipra_ring)
  have budget := le_trans small (GaussianRadiusExponentialName.precision_budget (Γ := Γ) W p)
  exact distance_congr (GaussianRadiusExponentialName.sample_at (negativeF F) W p (negativeData x)).eqSymm
    (GaussianRadiusExponentialName.sample_at (negativeF H) W p (negativeData y)).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ ht (unit_positive p) (le_congr (.eqRefl _) (one_mul _).eqSymm budget) raw)

private theorem reciprocal_diagonal (p A B D neg : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] distanceBounded (ap2 reciprocalF p (reciprocalData A B D neg))
      (GaussianGammaC7Name.sample p (native A B neg) (radius A B) D) (num 6) (unit p) := by
  let R := radius A B
  let z := native A B neg
  let W := disk A B D neg
  let N₀ := GaussianLogGammaEulerCofinal.cutoff R zero
  let N₁ := GaussianLogGammaEulerCofinal.cutoff R (negativeQuery W p)
  let N₂ := GaussianGammaEulerApproximationName.cutoff p R
  let N := N₀+N₁+N₂
  let y := hd A B D neg N
  have hs := GaussianLogGammaEulerResidualRadius.source_of_right_half_plane A B D neg h
  have h0 : Γ ⊢[PRAAx] le N₀ N := le_trans (le_add_right _ N₁) (le_add_right _ N₂)
  have h1 : Γ ⊢[PRAAx] le N₁ N := le_trans (le_add_left _ N₀) (le_add_right _ N₂)
  have h2 : Γ ⊢[PRAAx] le N₂ N := le_add_left _ (N₀+N₁)
  have hN := le_trans (GaussianLogGammaEulerCofinal.cutoff_positive R zero) h0
  have hp := unit_positive (Γ := Γ) p
  have actual := negative_exponentials_near p A B D neg N h h0 h1
  have head := GaussianExponentialInverse.negative_input H W y (head_input A B D neg N h h0)
  have expHead := exponential_input (negativeF H) (negativeData y) head.andE₁
  have widen := GaussianExponentialRadiusIndependence.same_input_cross _ _ _ _ head expHead
  have finite := GaussianLogGammaEulerExponentialHead.reciprocal_equivalent A B D neg R N hs hN
  have equals := cross_at _ _ _ _ p p (cross_trans _ _ _ _ _ _ widen finite)
  have second := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) equals
  have guards := GaussianGammaEulerApproximationName.cutoff_guards (Γ := Γ) p R
  have cv : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R D N :=
    .andI (original_source A B D neg h) (.andI (le_trans guards.andE₁ h2) (le_trans guards.andE₂.andE₁ h2))
  have budget : Γ ⊢[PRAAx] le (GaussianGammaEulerApproximationName.rate R*unit p) N :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (GaussianGammaEulerApproximationName.rate R))
      (GaussianExponentialReference.unit_monotone (le_succ_self p))) (le_trans guards.andE₂.andE₂ h2)
  have raw := GaussianGammaEulerConvergence.observation_error p p z R D N cv
  have payment : Γ ⊢[PRAAx] le
      (GaussianNamedSmallPerturbationTransport.budgetNumerator p p (GaussianGammaPerturbationExponent.numerator R) N
        (GaussianGammaC9Bound.majorant R)*unit p)
      (num 3*GaussianNamedSmallPerturbationTransport.budgetDenominator p p N) := by
    ipra_le 𝔞 (unit p)*𝔞 (unit p)*sl budget using
      unfold GaussianNamedSmallPerturbationTransport.budgetNumerator
        GaussianNamedSmallPerturbationTransport.budgetDenominator GaussianGammaEulerApproximationName.rate
      ipra_simps
      ring
  have third := distance_radius_mono _ _ _ _ _ _ (GaussianNamedSmallPerturbationTransport.denominator_positive p p N hN)
    hp payment raw
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp actual second) third)

theorem reciprocal_equivalent (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent reciprocalF gf (reciprocalData A B D neg) (gdata (native A B neg) (radius A B) D) := by
  have reg := GaussianExponentialInverse.negative_input F _ _ (cofinal_input A B D neg h)
  refine GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (num 6)
    (GaussianRadiusExponentialName.name_regular _ _ _ reg)
    (GaussianGammaC7Name.name_regular _ _ _ (original_source A B D neg h)) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source (sh A) (sh D) (sh neg) := by
    simpa [Fm.shift,Syn.shift,sh,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source] using h.shift
  simpa [GaussianNamedDiagonalRate.diagonalRate,GaussianGammaC7Name.sample,Syn.shift,sh] using
    reciprocal_diagonal (var 0) (sh A) (sh B) (sh D) (sh neg) hs

private theorem native_real_margin (A B D neg : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] GaussianGammaRightHalfPlane.realMargin (native A B neg) D D := by
  apply zle_of_toZ (D*LeanProofs.IPRA.PTm.monus A one)
  have e := natEq (eq_add_of_le hA)
  simp only [GaussianLogGammaEulerResidualDomain.native,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -𝔞 D*e

/-- The actual canonical log-Gamma exponential is the original
Gaussian Gamma on every encoded positive rational right-half-plane input. -/
theorem gamma_equivalent (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent expF GaussianGammaReciprocalInverse.gammaF (expData A B D neg)
      (GaussianGammaReciprocalInverse.gammaData (native A B neg) (radius A B) D D) := by
  let z := native A B neg
  let R := radius A B
  let W := disk A B D neg
  let x := cd A B D neg
  let g := gdata z R D
  let y := expData A B D neg
  let r := reciprocalData A B D neg
  have hi := cofinal_input A B D neg h
  have hf := GaussianRadiusExponentialName.name_regular F W x hi
  have hr := GaussianRadiusExponentialName.name_regular (negativeF F) W (negativeData x)
    (GaussianExponentialInverse.negative_input F W x hi)
  have hs := original_source A B D neg h
  have hg := GaussianGammaC7Name.name_regular z R D hs
  have poles := GaussianGammaRightHalfPlane.original_right_half_plane_source z R D D hs h.andE₂
    (native_real_margin A B D neg h.andE₁.andE₁)
  have apart := (GaussianGammaReciprocalInverse.original_gamma_inverse z R D one D poles).andE₁.andE₂
  have swap := GaussianNameRingLaws.multiply_commutative reciprocalF expF r y hr hf
  have pair := GaussianExponentialInverse.exponential_inverse F W x hi
  have replaces := GaussianGammaAdjacentCutoff.multiply_cross gf reciprocalF expF expF g r y y hg hr hf hf
    (cross_symm _ _ _ _ (reciprocal_equivalent A B D neg h)) (cross_refl _ _ hf)
  have product := cross_trans _ _ _ _ _ _ replaces (cross_trans _ _ _ _ _ _ swap
    (cross_trans _ _ _ _ _ _ pair (GaussianNamedExponentialDifferenceIdentity.ones_equivalent x g)))
  exact cross_symm _ _ _ _
    (GaussianBoundedInverseApartness.reciprocal_matches_inverse gf expF _ g y hg hf apart product)

theorem actual_canonical_log_Gamma_exponentiates_to_original_Gamma_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶
        crossEquivalent expF GaussianGammaReciprocalInverse.gammaF (expData (var 0) (var 1) (var 2) (var 3))
          (GaussianGammaReciprocalInverse.gammaData (native (var 0) (var 1) (var 3)) (radius (var 0) (var 1)) (var 2) (var 2))) :=
  closeUniv 4 (.impI (gamma_equivalent _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialLimit
