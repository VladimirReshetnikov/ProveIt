import IPRADerivations.Analysis.GaussianGammaDigammaFiniteSum
import IPRADerivations.Analysis.GaussianGammaDigammaMonotone
import IPRADerivations.Analysis.GaussianGammaDigammaReal
import IPRADerivations.Analysis.GaussianGammaDigammaRescale

/-!
# Native digamma bracketing by positive integers

For positive a,b,N, both N+a/b and N+1 lie between N and N+a.
The native monotonicity and the finite reciprocal sum between the
integer endpoints give a bound a/N with explicit observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaIntegerBracket

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum reciprocal_entry finite_sample_error)
open GaussianGammaDigammaMonotone (monotone)
open GaussianGammaDigammaRescale (integer_rescale)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qadd positive_product ofGaussian_canonical)
open GaussianRationalMetric (bounded qsub distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance constantBody sum_distance)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper upper_mono upper_triangle radius_of_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "RF" => GaussianGammaDigammaReal.nameF
local notation "rd" => GaussianGammaDigammaReal.data
local notation "qrzero" => GaussianRationalHorner.qzero

private theorem fixed_sample_canonical (p a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 DF p (dd a b)) :=
  GaussianNameArithmetic.multiply_canonical GaussianGammaC7Name.nameF GaussianEulerLogarithmicImproperName.nameF
    (GaussianGammaDigammaNative.reciprocalData a b) (GaussianGammaDigammaNative.derivativeData a b) p

theorem reciprocal_sum_bound (N A : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (reciprocalSum N one A) qrzero A N := by
  have all : Γ ⊢[PRAAx] termsDistance reciprocalBody constantBody A (pairT N one) qrzero one N := by
    refine .allI (.impI ?_)
    let M := Syn.shift N
    let j : PTm (n+1) := var 0
    let Δ := lt j (Syn.shift A) :: Γ.map Fm.shift
    have h : Γ.map Fm.shift ⊢[PRAAx] le one M := by simpa [M,Fm.shift,Syn.shift] using hN.shift
    have hm : Δ ⊢[PRAAx] le M (index M one j) := le_add_right _ _
    have hd := le_trans h.wk hm
    have bound := GaussianRationalReciprocal.bound_congr
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point one (index M one j) hd).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one (index M one j) hd)
    have smaller := GaussianCoefficientNameBounds.bounded_radius_mono _ one (index M one j) one M hd h.wk
      (le_congr (one_mul _).eqSymm (one_mul _).eqSymm hm) bound
    have dist : Δ ⊢[PRAAx] distanceBounded (fraction one (index M one j)) qrzero one M :=
      GaussianRationalReciprocal.bound_congr
        (GaussianRationalReconstruction.qsub_zero_right _ (ofGaussian_canonical _ _ hd)).eqSymm
        (.eqRefl _) (.eqRefl _) smaller
    have actual := distance_congr (reciprocal_entry M one j).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) dist
    simpa only [termsDistance,Syn.shift,M,j,Δ,subst_pairT,GaussianRationalRiemannRefinement.constant_entry,
      GaussianRationalHorner.subst_qzero,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using actual
  have err := sum_distance reciprocalBody constantBody A (pairT N one) qrzero one N hN all
  have s := (GaussianRationalRiemannRefinement.constant_sum (Γ := Γ) qrzero A).eqTrans
    ((GaussianRationalNaturalScale.natScale_as_product A qrzero).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))
  exact distance_congr (.eqRefl _) s (by ipra_ring) (.eqRefl _) err

def denominator (p N : PTm n) : PTm n := N*unit p
def edgeNumerator (p N A : PTm n) : PTm n := num 5*A*N+A*unit p
def numerator (p N A : PTm n) : PTm n := (num 5*A+num 8)*N+A*unit p

set_option maxHeartbeats 800000 in
theorem edge_distance (p N A : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 DF p (dd (index N one A) one)) (ap2 DF p (dd N one)) (edgeNumerator p N A) (denominator p N) := by
  have hp := unit_positive (Γ := Γ) p
  have h := finite_sample_error p N one A (.andI hN (le_refl one))
  have g := reciprocal_sum_bound N A hN
  have near := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hp hN h g
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalReconstruction.qsub_zero_right _ (GaussianRationalMetric.qsub_canonical _ _))
    (by unfold edgeNumerator; ipra_ring) (by unfold denominator; ipra_ring) near

private theorem integer_source (N : PTm n) (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] source N one :=
  .andI hn (le_refl one)

theorem lower_order (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] realOrder DF DF (dd N one) (dd (index a b N) b) := by
  let r := index a b N
  have h := GaussianGammaDigammaFiniteSum.row_source a b N hs
  have hn : Γ ⊢[PRAAx] source (b*N) b := .andI (positive_product _ _ hs.andE₂ hN) hs.andE₂
  have order := monotone (b*N) r b hn h (by unfold r index; ipra_le 𝔞 a)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (integer_rescale N b hN hs.andE₂)) (cross_refl _ _ (GaussianGammaDigammaNative.name_regular _ _ h)) order

theorem upper_order (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] realOrder DF DF (dd (index a b N) b) (dd (index N one a) one) := by
  let r := index a b N
  let s := index N one a
  have h := GaussianGammaDigammaFiniteSum.row_source a b N hs
  have hs' : Γ ⊢[PRAAx] le one s := le_trans hN (le_add_right _ _)
  have hn : Γ ⊢[PRAAx] source (b*s) b := .andI (positive_product _ _ hs.andE₂ hs') hs.andE₂
  have order := monotone r (b*s) b h hn (by unfold r s index; ipra_le 𝔞 a*sl hs.andE₂)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (GaussianGammaDigammaNative.name_regular _ _ h)) (integer_rescale s b hs' hs.andE₂) order

private theorem cofinal_chain (p N A x y l u : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hx : Γ ⊢[PRAAx] upper (fstT x) (fstT u) two (unit p))
    (he : Γ ⊢[PRAAx] distanceBounded u l (edgeNumerator p N A) (denominator p N))
    (hy : Γ ⊢[PRAAx] upper (fstT l) (fstT y) two (unit p)) :
    Γ ⊢[PRAAx] upper (fstT x) (fstT y) ((num 5*A+num 4)*N+A*unit p) (denominator p N) := by
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hN hp
  have e := scalar_upper _ _ _ _ hd he
  have res := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ hx e) hy
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hd) hp) res
    (le_of_eq_add (d := zero) (by unfold denominator edgeNumerator; ipra_ring))

theorem raw_bounds (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] upper (fstT (ap2 DF p (dd (index a b N) b))) (fstT (ap2 DF p (dd (succ N) one)))
      ((num 5*a+num 4)*N+a*unit p) (denominator p N) ⋏
    upper (fstT (ap2 DF p (dd (succ N) one))) (fstT (ap2 DF p (dd (index a b N) b)))
      ((num 5*a+num 4)*N+a*unit p) (denominator p N) := by
  let s := index N one a
  let x := dd (index a b N) b
  let y := dd (succ N) one
  let l := dd N one
  let u := dd s one
  have hp := unit_positive (Γ := Γ) p
  have hLo := lower_order a b N hs hN
  have hHi := upper_order a b N hs hN
  have hL := monotone N (succ N) one (integer_source N hN) (integer_source _ (zero_lt_succ _)) (le_succ_self _)
  have hS : Γ ⊢[PRAAx] le one s := le_trans hN (le_add_right _ _)
  have hR := monotone (succ N) s one (integer_source _ (zero_lt_succ _)) (integer_source _ hS)
    (by unfold s index; ipra_le sl hs.andE₁)
  have small (a b : PTm n) (h : Γ ⊢[PRAAx] realOrder DF DF a b) : Γ ⊢[PRAAx]
      upper (fstT (ap2 DF p a)) (fstT (ap2 DF p b)) two (unit p) :=
    upper_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp)
      (real_order_at DF DF a b p p h) (le_of_eq_add (d := zero) (by ipra_ring))
  have ec := edge_distance p N a hN
  exact .andI (cofinal_chain p N a _ _ _ _ hN (small x u hHi) ec (small l y hL))
    (cofinal_chain p N a _ _ _ _ hN (small y u hR) ec (small l x hLo))

theorem real_sample_distance (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 RF p (rd (index a b N) b)) (ap2 RF p (rd (succ N) one))
      (numerator p N a) (denominator p N) := by
  let A := index a b N
  let B := succ N
  let X := ap2 RF p (rd A b)
  let Y := ap2 RF p (rd B one)
  have hp := unit_positive (Γ := Γ) p
  have hn := positive_product _ _ hN hp
  have hx := GaussianGammaDigammaFiniteSum.row_source a b N hs
  have hy := integer_source (Γ := Γ) B (zero_lt_succ _)
  have cx := GaussianGammaDigammaReal.original_cross A b hx
  have cy := GaussianGammaDigammaReal.original_cross B one hy
  have convert (f g : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
      Γ ⊢[PRAAx] upper (fstT (ap2 f p x)) (fstT (ap2 g p y)) two (unit p) :=
    scalar_upper _ _ _ _ hp (distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp)
      hp (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at f g x y p p h))
  have combine (x y X' Y' : PTm n) (l : Γ ⊢[PRAAx] upper (fstT x) (fstT X') two (unit p))
      (m : Γ ⊢[PRAAx] upper (fstT X') (fstT Y') ((num 5*a+num 4)*N+a*unit p) (denominator p N))
      (r : Γ ⊢[PRAAx] upper (fstT Y') (fstT y) two (unit p)) :
      Γ ⊢[PRAAx] upper (fstT x) (fstT y) (numerator p N a) (denominator p N) :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hp hn) hp)
      (upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l m) r)
      (le_of_eq_add (d := zero) (by unfold numerator denominator; ipra_ring))
  have bounds := raw_bounds p a b N hs hN
  have lo := combine X Y _ _ (convert _ _ _ _ (cross_symm _ _ _ _ cx)) bounds.andE₁ (convert _ _ _ _ cy)
  have hi := combine Y X _ _ (convert _ _ _ _ (cross_symm _ _ _ _ cy)) bounds.andE₂ (convert _ _ _ _ cx)
  have rx := GaussianSignedNameExponentialOrder.real_sample_at RF (rd A b) p (GaussianGammaDigammaReal.name_real (Γ := Γ) A b)
  have ry := GaussianSignedNameExponentialOrder.real_sample_at RF (rd B one) p (GaussianGammaDigammaReal.name_real (Γ := Γ) B one)
  exact distance_congr (RationalGaussianEmbedding.canonical_axis_roundtrip _ rx.andE₁ rx.andE₂)
    (RationalGaussianEmbedding.canonical_axis_roundtrip _ ry.andE₁ ry.andE₂) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hn (radius_of_upper _ _ _ _ lo hi))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaIntegerBracket
