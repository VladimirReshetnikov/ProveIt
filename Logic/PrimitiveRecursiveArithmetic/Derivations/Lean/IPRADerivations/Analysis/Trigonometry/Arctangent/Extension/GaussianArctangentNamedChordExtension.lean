import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.Coordinates.GaussianArctangentCayleyProjections
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.Correctness.GaussianArctangentInverseForward

/-!
# The arctangent chord bound for regular named parameters

The literal sine coordinate and the original forward extension meet on
the same clipped rational argument at a cofinal query. The rational
chord inequality at that argument transfers to the two independent
observations of the extension and the normalized product name.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedChordExtension

open_ipra
open GaussianArctangentCayleyTrig (sinePoint)
open GaussianArctangentInverseForward (imaginaryOrder)
open GaussianArctangentInverseSampler (ordinate)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentNamedExtension (clock numerator denominator denominator_positive numerator_le)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameEquivalence (point_at)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def sineF (f : PR 2) : PR 2 :=
  GaussianArctangentCayleyProjections.sineProjectionF f
def sineData (x : PTm n) : PTm n := GaussianArctangentNamedCayley.data x
def productF (f : PR 2) : PR 2 := multiplyF (sineF f) quarterF
def productData (f : PR 2) (x z : PTm n) : PTm n := multiplyData (sineF f) quarterF (sineData x) z
def parameterPrecision (t : PTm n) : PTm n :=
  GaussianArctangentCayleyProjections.samplePrecision t

ipra_subst productData [sineData]

private theorem parameter_precision_later (t : PTm n) : Γ ⊢[PRAAx] le t (parameterPrecision t) := by
  let r := GaussianFastValueCut.exponent (GaussianArctangentNamedCayley.modulus : PTm n) t
  have h : Γ ⊢[PRAAx] le r (GaussianArctangentNamedCayley.queryPrecision r) :=
    le_trans (le_add_right _ _) (le_add_right _ _)
  exact le_trans (le_add_right _ _) h

theorem sine_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (sineF f) (sineData x) :=
  GaussianImaginaryCoordinateName.name_regular _ _ (GaussianArctangentNamedCayley.name_regular f x hf)

theorem product_regular (f : PR 2) (x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (productF f) (productData f x z) :=
  multiply_fast _ _ _ _ (sine_regular f x hf) (quarter_regular z)

def slackCost (f : PR 2) (x z : PTm n) : PTm n :=
  multiplyModulus (sineF f) quarterF (sineData x) z+num 5

private theorem chord_slack (f : PR 2) (x z p q t : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] upperSlack (ordinate (GaussianArctangentNamedExtension.nameF f) p x)
      (ordinate (productF f) q (productData f x z))
      (unit p+unit q) (unit p*unit q) (slackCost f x z) t := by
  let r := parameterPrecision t
  let r' := clock r
  let A := numerator f r x
  let B := denominator f r x
  let F := GaussianArctangentNamedExtension.nameF f
  let G := productF f
  let gd := productData f x z
  let a := ap2 F p x
  let u := ap2 F r x
  let v := qmul (sinePoint B A) (ap2 quarterF t z)
  let w := ap2 G t gd
  let b := ap2 G q gd
  let P := unit p
  let Q := unit q
  let T := unit t
  let R := unit r
  let J := unit r'
  let L := multiplyModulus (sineF f) quarterF (sineData x) z
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have hr := unit_positive (Γ := Γ) r
  have hj := unit_positive (Γ := Γ) r'
  have tr : Γ ⊢[PRAAx] le T R :=
    GaussianExponentialReference.unit_monotone (parameter_precision_later t)
  have tj : Γ ⊢[PRAAx] le T J :=
    GaussianExponentialReference.unit_monotone (le_trans (parameter_precision_later t) (le_add_right _ _))
  have extension := GaussianArctangentNamedExtension.name_regular f x hf
  have sine := sine_regular f x hf
  have quarter := quarter_regular (Γ := Γ) z
  have product := product_regular f x z hf
  have first := upper_of_radius _ _ _ _
    (imaginary_coordinate_radius _ _ _ _ (positive_product _ _ hp hr) (point_at F x p r extension))
  have left : Γ ⊢[PRAAx] upper (sndT a) (sndT u) (P+T) (P*T) :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hp hr) first (by
      change Γ ⊢[PRAAx] le ((P+R)*(P*T)) ((P+T)*(P*R))
      ipra_le 𝔟 P*𝔟 P*sl tr)
  have chord := upper_congr (Γ := Γ) (congrSnd (GaussianArctangentNamedExtension.sample_at f r x)).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianArctangentNamedChord.original_chord_at r' t A B z
      (denominator_positive f r x) (numerator_le f r x))
  have mid : Γ ⊢[PRAAx] upper (sndT u) (sndT v) two T :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hj ht) chord (by
      change Γ ⊢[PRAAx] le ((J+T)*T) (two*(J*T))
      ipra_le 𝔟 T*sl tj)
  have norm : Γ ⊢[PRAAx] distanceBounded w v (L+one) T :=
    distance_congr (.eqRefl _) (qmul_congr (GaussianArctangentCayleyProjections.sine_sample_at f t x) (.eqRefl _))
      (.eqRefl _) (.eqRefl _)
      (GaussianNameRingLaws.multiply_sample_error (sineF f) quarterF (sineData x) z t sine quarter)
  have move : Γ ⊢[PRAAx] upper (sndT v) (sndT w) (L+one) T :=
    upper_of_radius _ _ _ _
      (imaginary_coordinate_radius _ _ _ _ ht (distance_symmetric _ _ _ _ ht norm))
  have right : Γ ⊢[PRAAx] upper (sndT w) (sndT b) (T+Q) (T*Q) :=
    upper_of_radius _ _ _ _
      (imaginary_coordinate_radius _ _ _ _ (positive_product _ _ ht hq) (point_at G gd t q product))
  have joined := upper_triangle _ _ _ _ _ _ _
    (upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left mid) move) right
  have hD := positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hp ht) ht) ht)
    (positive_product _ _ ht hq)
  apply upper_mono _ _ _ _ _ _ hD joined
  exact le_of_eq_add (d := LeanProofs.ConciseIPRA.PTm.zero) (by
    dsimp only [P,Q,T,L,upperSlack,slackCost]
    ipra_ring)

theorem original_chord_at (f : PR 2) (x z p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] upper (ordinate (GaussianArctangentNamedExtension.nameF f) p x)
      (ordinate (productF f) q (productData f x z))
      (unit p+unit q) (unit p*unit q) :=
  remove_upper_slack _ _ _ _ (slackCost f x z)
    (chord_slack f x z p q (precision (ordinate (GaussianArctangentNamedExtension.nameF f) p x)
      (ordinate (productF f) q (productData f x z)) (unit p*unit q) (slackCost f x z)) hf)

theorem original_chord (f : PR 2) (x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] imaginaryOrder (GaussianArctangentNamedExtension.nameF f) (productF f) x (productData f x z) := by
  let X := Syn.shift (Syn.shift x)
  let Z := Syn.shift (Syn.shift z)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f X := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift,X] using hf.shift.shift
  refine .allI (.allI ?_)
  simpa only [imaginaryOrder,subst_productData,Syn.shift,X,Z] using
    original_chord_at f X Z (var 1) (var 0) hs

theorem actual_named_arctangent_sine_chord_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (pointCN f (var 0) ⟶ imaginaryOrder (GaussianArctangentNamedExtension.nameF f) (productF f) (var 0)
      (productData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_chord f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedChordExtension
