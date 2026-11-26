import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaHarmonicLogBalance
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope

/-!
# Elementary positive-rational digamma bounds in iPRA

For every positive rational x, the original digamma name is between
the named reals log x − 1/x and log x − 1/(2x). The proof uses the
literal Euler slope, the right rectangle and trapezoid inequalities,
and a cofinal observation of the original logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaElementaryBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaFiniteSum (index reciprocalSum)
open GaussianGammaDigammaHarmonicCells (halfReciprocal point_fraction_represents)
open GaussianGammaDigammaHarmonicPrefix (prefixCell endpointPair prefix_bounds)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianHarmonicLogarithmName (sample sample_at)
open GaussianHarmonicLogarithmProduct (mesh mesh_later)
open GaussianNamedDifference (difference_distance sample_error)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qzero positive_product ofGaussian_canonical scalar_congr)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingTailComparison (point_add_order)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalGaussianEmbedding (scalar_zero_represents)
open RationalHarmonicInterval (horizon left_horizon)
open RationalValueBounds (upper upper_of_radius upper_order_right upper_triangle upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "EF" => GaussianGammaDigammaEulerDerivative.nameF
local notation "ed" => GaussianGammaDigammaEulerDerivative.data
local notation "HF" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data

def nameF : PR 2 := GaussianNamedDifference.nameF HF constantF
def lowerData (a b : PTm n) : PTm n := GaussianNamedDifference.data (hd a b) (fraction b a)
def upperData (a b : PTm n) : PTm n := GaussianNamedDifference.data (hd a b) (halfReciprocal a b)

@[simp] theorem subst_lowerData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (lowerData a b) = lowerData (Syn.subst σ a) (Syn.subst σ b) := by simp [lowerData]
@[simp] theorem subst_upperData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (upperData a b) = upperData (Syn.subst σ a) (Syn.subst σ b) := by simp [upperData]

theorem endpoint_regular (a b c : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN nameF (GaussianNamedDifference.data (hd a b) c) :=
  GaussianNamedDifference.name_regular HF constantF _ _ (GaussianHarmonicLogarithmName.name_regular a b hs) (constant_regular c)

private theorem sub_antitone (z x y : PTm n) (h : Γ ⊢[PRAAx] rationalLE (fstT x) (fstT y)) :
    Γ ⊢[PRAAx] rationalLE (fstT (qsub z y)) (fstT (qsub z x)) := by
  have e (c : PTm n) : Γ ⊢[PRAAx] fstT (qnegative c) ≐ RationalArithmetic.negative (fstT c) := fst_pair _ _
  exact point_add_order z z (qnegative y) (qnegative x) (RationalArgmin.reflexive _)
    (rationalLE_congr (e y).eqSymm (e x).eqSymm (RationalAlgebra.negative_antitone _ _ h))

private theorem fraction_nonnegative (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] rationalLE (fstT qzero) (fstT (fraction a b)) := by
  have hz := scalar_congr (RationalGaussianRealPart.real_zero (Γ := Γ)).eqSymm (.eqRefl _) (.eqRefl _) (scalar_zero_represents one)
  apply RationalArithmetic.order_of_representations _ _ (ZT.ofNat zero) (ZT.ofNat a) one b hz (point_fraction_represents a b hb)
    (le_refl one) hb
  apply zle_of_toZ a
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem half_le_endpoints (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] rationalLE (fstT (halfReciprocal a b)) (fstT (endpointPair a b N)) := by
  have hA : Γ ⊢[PRAAx] le one (index a b N) := le_trans ha (le_add_right _ _)
  have hD := positive_product _ _ (le_succ_self one) hA
  have order := point_add_order (halfReciprocal a b) (halfReciprocal a b) qzero (halfReciprocal (index a b N) b)
    (RationalArgmin.reflexive _) (fraction_nonnegative b _ hD)
  exact rationalLE_congr (congrFst (GaussianRationalLinearProduct.qadd_zero_right _
    (ofGaussian_canonical _ _ (positive_product _ _ (le_succ_self one) ha)))) (.eqRefl _) order

private theorem cutoff_order (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx]
      (rationalLE (fstT (qsub (qsub (ap2 logF p N) (sample p (index a b N) a)) (fraction b a)))
        (fstT (qsub (ap2 logF p N) (reciprocalSum a b (succ N))))) ⋏
      (rationalLE (fstT (qsub (ap2 logF p N) (reciprocalSum a b (succ N))))
        (fstT (qsub (qsub (ap2 logF p N) (sample p (index a b N) a)) (halfReciprocal a b)))) := by
  let A := index a b N
  let Q := mesh p
  let L := horizon A a Q
  let M := sample p A a
  let R := reciprocalSum a b (succ N)
  let V := ap2 logF p N
  let h := halfReciprocal a b
  let r := fraction b a
  have hQ : Γ ⊢[PRAAx] le one Q := le_trans (unit_positive p) (mesh_later p)
  have bounds := (prefix_bounds a b Q L N hs hQ).impE (left_horizon A a Q)
  have eM : Γ ⊢[PRAAx] prefixCell a b Q L N ≐ M := (sample_at p A a).eqSymm
  have hl := rationalLE_congr (congrFst (qadd_congr eM (.eqRefl _))) (.eqRefl _) bounds.andE₁
  have hr := rationalLE_congr (.eqRefl _) (congrFst (qadd_congr eM (.eqRefl _))) bounds.andE₂
  have ht := RationalArgmin.transitive (point_add_order M M h (endpointPair a b N) (RationalArgmin.reflexive _)
    (half_le_endpoints a b N hs.andE₁)) hl
  exact .andI
    (rationalLE_congr (congrFst (subtract_sum V M r).eqSymm) (.eqRefl _) (sub_antitone V R (qadd M r) hr))
    (rationalLE_congr (.eqRefl _) (congrFst (subtract_sum V M h).eqSymm) (sub_antitone V (qadd M h) R ht))

private theorem cutoff_distance (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd a b))
      (qsub (ap2 logF p (unit p)) (reciprocalSum a b (succ (unit p)))) (a+num 10) (unit p) := by
  let N := unit p
  let R := reciprocalSum a b (succ N)
  have hp := unit_positive (Γ := Γ) p
  have actual := GaussianGammaDigammaEulerDerivative.original_rate a b N hs hp
  have diag := GaussianNamedInverseRate.diagonal_rate DF EF _ _ _ N p hp actual
  have smaller := distance_radius_mono _ _ _ _ (a+num 4) N (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by
      unfold N GaussianGammaDigammaEulerDerivative.rateCoefficient
      ipra_ring)) diag
  have raw := distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p R)) (.eqRefl _) (.eqRefl _)
    (sample_error logF constantF N R p (log_regular N hp) (constant_regular R))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ N hp smaller raw)

private theorem endpoint_distance (p a b c : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (GaussianNamedDifference.data (hd a b) c))
      (qsub (qsub (ap2 logF p (unit p)) (sample p (index a b (unit p)) a)) c) (a+num 16) (unit p) := by
  let N := unit p
  have hp := unit_positive (Γ := Γ) p
  have error := distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p c)) (.eqRefl _) (.eqRefl _)
    (sample_error HF constantF (hd a b) c p (GaussianHarmonicLogarithmName.name_regular a b hs) (constant_regular c))
  have logBalance := GaussianGammaDigammaHarmonicLogBalance.cutoff_balance p a b hs
  have shift := difference_distance _ _ c c _ zero N hp
    (distance_symmetric _ _ _ _ hp logBalance) (distance_refl_zero c N hp)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ N hp error shift)

private theorem order_with_errors (x x' y y' A B N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hx : Γ ⊢[PRAAx] distanceBounded x x' A N) (hy : Γ ⊢[PRAAx] distanceBounded y y' B N)
    (h : Γ ⊢[PRAAx] rationalLE (fstT x') (fstT y')) :
    Γ ⊢[PRAAx] upper (fstT x) (fstT y) (A+B) N := by
  have left := upper_order_right _ _ _ _ _ (upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hN hx)) h
  have right := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hN (distance_symmetric _ _ _ _ hN hy))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hN hN)
    (upper_triangle _ _ _ _ _ _ _ left right) (le_of_eq_add (d := zero) (by ipra_ring))

theorem sample_envelope (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx]
      (upper (fstT (ap2 nameF p (lowerData a b))) (fstT (ap2 DF p (dd a b))) (two*a+num 26) (unit p)) ⋏
      (upper (fstT (ap2 DF p (dd a b))) (fstT (ap2 nameF p (upperData a b))) (two*a+num 26) (unit p)) := by
  have hp := unit_positive (Γ := Γ) p
  have h := cutoff_order p a b (unit p) hs
  have e := cutoff_distance p a b hs
  exact .andI
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (order_with_errors _ _ _ _ _ _ _ hp (endpoint_distance p a b (fraction b a) hs) e h.andE₁))
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (order_with_errors _ _ _ _ _ _ _ hp e (endpoint_distance p a b (halfReciprocal a b) hs) h.andE₂))

theorem elementary_bounds (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] (realOrder nameF DF (lowerData a b) (dd a b) ⋏ realOrder DF nameF (dd a b) (upperData a b)) := by
  let K := two*a+num 26
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using hs.shift
  have h := sample_envelope (var 0) (Syn.shift a) (Syn.shift b) hs'
  have l : Γ ⊢[PRAAx] envelope nameF DF (lowerData a b) (dd a b) K :=
    .allI (by simpa [envelope,K,Syn.shift,two] using h.andE₁)
  have u : Γ ⊢[PRAAx] envelope DF nameF (dd a b) (upperData a b) K :=
    .allI (by simpa [envelope,K,Syn.shift,two] using h.andE₂)
  have reg := GaussianGammaDigammaNative.name_regular a b hs
  exact .andI (order_from_envelope _ _ _ _ _ (endpoint_regular a b _ hs) reg l)
    (order_from_envelope _ _ _ _ _ reg (endpoint_regular a b _ hs) u)

theorem actual_original_positive_rational_digamma_elementary_bounds_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶
        (realOrder nameF DF (lowerData (var 0) (var 1)) (dd (var 0) (var 1)) ⋏
         realOrder DF nameF (dd (var 0) (var 1)) (upperData (var 0) (var 1)))) :=
  closeUniv 2 (.impI (elementary_bounds _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaElementaryBounds
