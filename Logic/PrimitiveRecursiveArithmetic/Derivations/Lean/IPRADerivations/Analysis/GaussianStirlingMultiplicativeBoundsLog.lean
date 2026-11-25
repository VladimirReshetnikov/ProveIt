import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsOrder
import IPRADerivations.Analysis.GaussianHarmonicIntervalLinearRemainder

/-!
# Exact logarithm comparison for the Stirling ratio

Rational endpoint rectangles on the original harmonic mesh give
c/(a+c) <= log((a+c)/a) <= c/a as independent-clock named orders.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsLog

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction logF data source)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalGaussianEmbedding (embed)
open RationalHarmonicInterval (horizon common numerator interval left_horizon)
open RationalValueBounds (upper upper_congr upper_of_order upper_of_radius upper_order_left upper_order_right radius_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem constant_order (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE (fstT a) (fstT b)) :
    Γ ⊢[PRAAx] realOrder constantF constantF a b := by
  refine order_from_envelope _ _ _ _ zero (constant_regular a) (constant_regular b) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (fstT (Syn.shift a)) (fstT (Syn.shift b)) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have ready := upper_of_order _ _ (zero : PTm (n+1)) (unit (var 0))
    (rationalLE_congr (congrFst (constant_at (var 0) (Syn.shift a))).eqSymm
      (congrFst (constant_at (var 0) (Syn.shift b))).eqSymm hs)
  simpa [envelope,Syn.shift] using ready

theorem fractions_order (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (ho : Γ ⊢[PRAAx] le (d*a) (c*b)) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction a b)) (fstT (fraction c d)) :=
  rationalLE_congr (fraction_real_part a b hb).eqSymm (fraction_real_part c d hd).eqSymm
    (GaussianEuclideanDistanceName.fraction_order a b c d hb hd ho)

set_option maxHeartbeats 450000 in
private theorem finite_rectangles (a c Q : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hq : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction c (a+c))) (fstT (embed (interval (a+c) a Q))) ⋏
      rationalLE (fstT (embed (interval (a+c) a Q))) (fstT (fraction c a)) := by
  let L := horizon (a+c) a Q
  let F := Products.fact L
  let U := S (Q*(a+c)) F
  let V := S (Q*a) F
  let D := monus U V
  let J := common (a+c) a Q L
  let N := numerator (a+c) a Q L
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have hA := le_trans ha (le_add_right a c)
  have mono : Γ ⊢[PRAAx] le V U :=
    AnalyticNumberTheory.HarmonicChebyshev.S_mono F
      (le_congr (mul_comm a Q) (mul_comm (a+c) Q) (mul_le_mul_right Q (le_add_right a c)))
  have e : Γ ⊢[PRAAx] U ≐ V+D := eq_add_of_le mono
  have eqN : Γ ⊢[PRAAx] N.eq (ZT.ofNat D) := by
    apply ZT.derive
    have E := natEq e
    simp only [N,numerator,ZT.toZ_ofNat]
    change ZT.toZ Γ (⟨U,V⟩ : ZT n) = 𝔞 D
    simp only [ZT.toZ]
    ipra_simps
    linear_combination E
  have rep := RationalGaussianEmbedding.scalar_recode_represents J N F
    (RationalHarmonicInterval.common_value (Γ := Γ) (a+c) a Q L)
  have read := (congrFst (RationalGaussianEmbedding.embed_at (Γ := Γ) J)).eqSymm.eqTrans
    (RationalGaussianEmbedding.embed_real_part J)
  have value := GaussianRationalHorner.scalar_congr read.eqSymm eqN (.eqRefl _) rep
  have rect := GaussianHarmonicIntervalLinearRemainder.rectangles a c Q L ha hq (left_horizon _ _ _)
  have lo := le_congr (.eqRefl _) (congrMul (.eqRefl (a+c)) e) rect.andE₁
  have hi := le_congr (congrMul (.eqRefl a) e) (.eqRefl _) rect.andE₂
  have l : Γ ⊢[PRAAx] le (F*c) (D*(a+c)) := by ipra_le sl lo
  have h : Γ ⊢[PRAAx] le (a*D) (c*F) := by ipra_le sl hi
  exact .andI
    (rationalLE_congr (fraction_real_part c (a+c) hA).eqSymm (.eqRefl _)
      (GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hA hF
        (GaussianEuclideanDistanceName.fraction_represents c (a+c) hA) value l))
    (rationalLE_congr (.eqRefl _) (fraction_real_part c a ha).eqSymm
      (GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hF ha value
        (GaussianEuclideanDistanceName.fraction_represents c a ha) h))

private theorem observed_rectangles (p a c : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (fraction c (a+c)))) (fstT (ap2 logF p (data (a+c) a))) (num 8) (unit p) ⋏
      upper (fstT (ap2 logF p (data (a+c) a))) (fstT (ap2 constantF p (fraction c a))) (num 8) (unit p) := by
  let Q := GammaEulerConstantName.mesh p
  let Y := embed (interval (a+c) a Q)
  let Z := ap2 logF p (data (a+c) a)
  have hf := unit_positive (Γ := Γ) p
  have rect := finite_rectangles a c Q ha (GammaEulerConstantName.mesh_positive p)
  have error := GaussianPositiveRationalLogarithmProperness.sample_interval_error p (a+c) a
    (.andI (le_trans ha (le_add_right a c)) ha)
  have both := scalar_coordinate_distance Z Y (num 8) (unit p) hf error
  exact .andI
    (upper_congr (congrFst (constant_at p (fraction c (a+c)))).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (upper_order_left _ _ _ _ _ rect.andE₁ (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ both))))
    (upper_congr (.eqRefl _) (congrFst (constant_at p (fraction c a))).eqSymm (.eqRefl _) (.eqRefl _)
      (upper_order_right _ _ _ _ _ (upper_of_radius _ _ _ _ both) rect.andE₂))

theorem logarithm_rectangles (a c : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] realOrder constantF logF (fraction c (a+c)) (data (a+c) a) ⋏
      realOrder logF constantF (data (a+c) a) (fraction c a) := by
  have hr := GaussianPositiveRationalLogarithm.name_regular (a+c) a (.andI (le_trans ha (le_add_right a c)) ha)
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift,one] using ha.shift
  refine .andI
    (order_from_envelope _ _ _ _ (num 8) (constant_regular _) hr (.allI ?_))
    (order_from_envelope _ _ _ _ (num 8) hr (constant_regular _) (.allI ?_))
  · simpa [envelope,Syn.shift,one] using (observed_rectangles (var 0) (Syn.shift a) (Syn.shift c) hs).andE₁
  · simpa [envelope,Syn.shift,one] using (observed_rectangles (var 0) (Syn.shift a) (Syn.shift c) hs).andE₂

end LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsLog
