import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentInverseForward
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentInverseGap
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentPhysicalRefinement

/-!
# Regular inverse of twice the arctangent

The selected finite inverse points remain in the unit interval. Their
forward errors and the lower slope bound give a Cauchy modulus for the
actual inverse observations at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentClampedTarget (nativeValue)
open GaussianArctangentInverseForward (input forward_at)
open GaussianArctangentInverseSampler (ordinate mesh index raw rawF raw_at index_le mesh_positive)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open RationalCubeMidpoint (fraction)
open RationalValueBounds (radius radius_congr radius_triangle radius_symmetric radius_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def modulus : PTm n := num 10

def forwardSample (f : PR 2) (r p x : PTm n) : PTm n :=
  GaussianArctangentNamedSlope.ordinate r (index f p x) (mesh p)

theorem forward_sample_error (f : PR 2) (r p x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] radius (forwardSample f r p x) (ordinate f p x) (num 8) (unit p) := by
  let U := unit p
  let M := mesh p
  let j := index f p x
  let a := forwardSample f r p x
  let b := sndT (nativeValue j M)
  have atGrid : Γ ⊢[PRAAx] radius a b (num 4) M :=
    GaussianArctangentPhysicalRefinement.ordinate_at r j M (mesh_positive p) (index_le f p x)
  have first : Γ ⊢[PRAAx] radius a b one U :=
    radius_mono a b (num 4) M one U (mesh_positive p) atGrid
      (le_congr (.eqRefl _) (by change Γ ⊢[PRAAx] num 4*U ≐ one*(num 4*U); ipra_ring) (le_refl _))
  have rest := forward_at f p x z h
  have hp := unit_positive (Γ := Γ) p
  exact radius_mono a (ordinate f p x) (one*U+num 7*U) (U*U) (num 8) U
    (positive_product _ _ hp hp) (radius_triangle a b (ordinate f p x) one U (num 7) U first rest)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))

theorem forward_sample_later (f : PR 2) (r t p x z : PTm n) (h : Γ ⊢[PRAAx] input f x z)
    (ht : Γ ⊢[PRAAx] le p t) :
    Γ ⊢[PRAAx] radius (forwardSample f r t x) (ordinate f p x) modulus (unit p) := by
  let U := unit p
  let V := unit t
  let W := V*U
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) t
  have hw := positive_product _ _ hv hu
  have hstep : Γ ⊢[PRAAx] radius (ordinate f t x) (ordinate f p x) (V+U) W :=
    imaginary_coordinate_radius _ _ _ _ hw (GaussianNameEquivalence.point_at f x t p h.andE₁)
  have joined := radius_triangle (forwardSample f r t x) (ordinate f t x) (ordinate f p x) (num 8) V (V+U) W
    (forward_sample_error f r t x z h) hstep
  have huV : Γ ⊢[PRAAx] le U V := GaussianGammaHalfPiName.unit_mono p t ht
  exact radius_mono _ _ _ _ modulus U (positive_product _ _ hv hw) joined
    (by dsimp only [W,modulus]; ipra_le 9*𝔞 U*𝔞 V*sl huV)

theorem forward_pair_error (f : PR 2) (p q x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] radius (forwardSample f p p x) (forwardSample f q q x)
      (num 9*(unit p+unit q)) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let W := U*V
  let a := forwardSample f p p x
  let b := forwardSample f q q x
  let y := ordinate f p x
  let w := ordinate f q x
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hw := positive_product _ _ hu hv
  have hstep : Γ ⊢[PRAAx] radius y w (U+V) W :=
    imaginary_coordinate_radius _ _ _ _ hw (GaussianNameEquivalence.point_at f x p q h.andE₁)
  have first := forward_sample_error f p p x z h
  have last := radius_symmetric b w (num 8) V (forward_sample_error f q q x z h)
  have joined := radius_triangle a w b _ _ (num 8) V
    (radius_triangle a y w (num 8) U (U+V) W first hstep) last
  exact radius_mono a b _ _ (num 9*(U+V)) W (positive_product _ _ (positive_product _ _ hu hw) hv) joined
    (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring))

theorem fraction_pair_error (f : PR 2) (p q x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] radius (fraction (index f p x) (mesh p)) (fraction (index f q x) (mesh q))
      (modulus*(unit p+unit q)) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let W := U*V
  have hw := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have b := GaussianArctangentInverseGap.inverse_radius p q (index f p x) (mesh p) (index f q x) (mesh q)
    (num 9*(U+V)) W (mesh_positive p) (mesh_positive q) (index_le f p x) (index_le f q x)
    (forward_pair_error f p q x z h)
  exact radius_mono _ _ _ _ (modulus*(U+V)) W (positive_product _ _ hw hw) b
    (le_of_eq_add (d := zero) (by dsimp only [W,modulus]; ipra_ring))

theorem raw_pair_error (f : PR 2) (p q x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] distanceBounded (raw f p x) (raw f q x) (modulus*(unit p+unit q)) (unit p*unit q) :=
  RationalGaussianNameEmbedding.distance_from_radius _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive q)) (fraction_pair_error f p q x z h)

theorem raw_regular (f : PR 2) (x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular (rawF f) modulus x := by
  refine .allI (.allI ?_)
  let X := Syn.shift (Syn.shift x)
  let Z := Syn.shift (Syn.shift z)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input f X Z := by
    simpa [Fm.shift,Syn.shift,X,Z] using h.shift.shift
  simpa only [GaussianFastValueCut.regular,Syn.shift,modulus,PTm.subst_num,X] using
    distance_congr (raw_at f (var 1) X).eqSymm (raw_at f (var 0) X).eqSymm (.eqRefl _) (.eqRefl _)
      (raw_pair_error f (var 1) (var 0) X Z hs)

def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def data (x : PTm n) : PTm n := GaussianFastValueCut.nameData modulus x
def precision (p : PTm n) : PTm n := GaussianFastValueCut.exponent modulus p

theorem precision_later (p : PTm n) : Γ ⊢[PRAAx] le p (precision p) := le_add_right _ _

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (data x) = data (Syn.subst σ x) := by simp [data,modulus]

theorem name_regular (f : PR 2) (x z : PTm n) (h : Γ ⊢[PRAAx] input f x z) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x) :=
  GaussianFastValueCut.name_fast (rawF f) modulus x (raw_regular f x z h)

theorem name_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p (data x) ≐ raw f (precision p) x := by
  have readback := raw_at (Γ := Γ) f (precision p) x
  have can := GaussianRationalHorner.canonical_congr readback
    (GaussianArctangentInverseSampler.raw_canonical f (precision p) x)
  exact (GaussianFastValueCut.name_at (rawF f) modulus x p).eqTrans
    ((GaussianExponentialReference.recode_fixed _ can).eqTrans readback)

theorem name_represents (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (ap2 (nameF f) p (data x)))
      (ZT.ofNat (index f (precision p) x)) (mesh (precision p)) :=
  GaussianRationalHorner.scalar_congr (congrFst (name_at f p x)).eqSymm (ZT.derive rfl) (.eqRefl _)
    (GaussianArctangentInverseSampler.raw_real_represents f (precision p) x)

theorem actual_arctangent_raw_inverse_modulus_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ GaussianFastValueCut.regular (rawF f) modulus (var 0)) :=
  closeUniv 2 (.impI (raw_regular f _ _ Prf.hyp0))

theorem actual_arctangent_inverse_name_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))

theorem actual_arctangent_inverse_name_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (nameF f) (var 0) (data (var 1)) ≐ raw f (precision (var 0)) (var 1)) :=
  closeUniv 2 (name_at f _ _)

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedInverse
