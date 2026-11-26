import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentNamedSlope
import IPRADerivations.Analysis.Names.Arithmetic.RationalReciprocalPowerName

/-!
# Forward Lipschitz bound for the actual partial arctangent

The two named slope bounds and the two-sided bound on the endpoint
distance give a two-sided bound on the original imaginary ordinates.
The original prefix observations are purely imaginary, so no norm loss
is needed to turn this bound into a Gaussian distance.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentForwardLipschitz

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (scale normSq normSq_eval eval_re_code eval_im_code)
open GaussianRootAlgebra (re_sub im_sub re_scale im_scale)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentExponentialPrefix (total prefixValue)
open GaussianArctangentNamedSlope (ordinate gapNumerator named_slope_at)
open GaussianArctangentPartialQuadrature (mesh clearing observation nameF data sample_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian_represents represents_rescale positive_product)
open GaussianRationalMetric (distanceBounded bounded_difference_iff)
open Products (fact)
open RationalArithmetic (add)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalSupMetric (denominatorOf numeratorOf)
open RationalValueBounds (upper upper_of_order upper_of_radius upper_mono upper_triangle
  radius radius_of_upper radius_congr radius_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem gap_budget (A B C D H K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hord : Γ ⊢[PRAAx] le (A*D) (C*B))
    (h : Γ ⊢[PRAAx] radius (fraction A B) (fraction C D) H K) :
    Γ ⊢[PRAAx] le (K*gapNumerator A B C D) (H*(B*D)) := by
  let u := RationalRepresentedUpper.left (ZT.ofNat C) B K
  let v := RationalRepresentedUpper.right (ZT.ofNat A) D B H K
  have sign : Γ ⊢[PRAAx] zle u v :=
    RationalRepresentedUpper.to_signed _ _ _ _ _ _ H K (fraction_represents C D hD) (fraction_represents A B hB)
      (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ h))
  have order := zle_toZ sign
  have e := natEq (eq_add_of_le hord)
  apply le_of_eq_add (d := PolynomialBisection.slack u v)
  apply deriveNat
  change ZT.toZ Γ u + 𝔟(PolynomialBisection.slack u v) = ZT.toZ Γ v at order
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,
    ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,u,v] at order ⊢
  unfold gapNumerator
  ipra_simps
  linear_combination -order+𝔟 K*e

private theorem below_added_fraction (a G E : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] upper a (add a (fraction G E)) zero one := by
  let U := denominatorOf a
  let x := numeratorOf a
  have hU := RationalArgmin.denominator_positive (Γ := Γ) a
  have src := RationalRepresentations.represents_self (Γ := Γ) a
  have sum := RationalRepresentations.represents_add _ _ _ _ _ _ src (fraction_represents G E hE)
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ hU
    (positive_product U E hU hE) src sum
  apply zle_of_toZ (G*(U*U))
  simp only [ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,U,x]
  ipra_simps
  ring

private theorem ordered_ordinate_radius (p q A B C D H K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (hord : Γ ⊢[PRAAx] le (A*D) (C*B))
    (h : Γ ⊢[PRAAx] radius (fraction A B) (fraction C D) H K) :
    Γ ⊢[PRAAx] radius (ordinate p A B) (ordinate q C D)
      ((unit p+unit q)*K+two*H*(unit p*unit q)) ((unit p*unit q)*K) := by
  let x := ordinate p A B
  let y := ordinate q C D
  let E := B*D
  let G := gapNumerator A B C D
  let S := unit p+unit q
  let T := unit p*unit q
  have hE := positive_product B D hB hD
  have slopes := named_slope_at p q A B C D hB hD hA hC hord
  have raw : Γ ⊢[PRAAx] le (K*G) (H*E) := gap_budget A B C D H K hB hD hord h
  have twice : Γ ⊢[PRAAx] le ((two*G)*K) ((two*H)*E) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl two) raw)
  have pay := upper_mono (add x (fraction (two*G) E)) x (two*G) E (two*H) K hE
    (RationalReciprocalPowerName.fraction_add_upper x (two*G) E hE) twice
  have right := upper_triangle y (add x (fraction (two*G) E)) x S T (two*H) K slopes.andE₂ pay
  have before := upper_triangle x (add x (fraction G E)) y zero one S T (below_added_fraction x G E hE) slopes.andE₁
  have forward : Γ ⊢[PRAAx] upper x y S T :=
    RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (one_mul T) before
  have nonneg := upper_of_order y y (two*H) K (RationalArgmin.reflexive (Γ := Γ) y)
  exact radius_of_upper _ _ _ _ (upper_triangle x y y S T (two*H) K forward nonneg) right

theorem ordinate_radius (p q A B C D H K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (h : Γ ⊢[PRAAx] radius (fraction A B) (fraction C D) H K) :
    Γ ⊢[PRAAx] radius (ordinate p A B) (ordinate q C D)
      ((unit p+unit q)*K+two*H*(unit p*unit q)) ((unit p*unit q)*K) := by
  refine .orE (le_total (A*D) (C*B)) ?_ ?_
  · exact ordered_ordinate_radius p q A B C D H K hB.wk hD.wk hA.wk hC.wk Prf.hyp0 h.wk
  · have swap := ordered_ordinate_radius q p C D A B H K hD.wk hB.wk hC.wk hA.wk Prf.hyp0
      (radius_symmetric _ _ _ _ h.wk)
    exact radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (radius_symmetric _ _ _ _ swap)

private theorem fact_positive (L : PTm n) : Γ ⊢[PRAAx] le one (fact L) :=
  le_congr (.eqRefl _) (AnalyticNumberTheory.Primes.fact_pos L).eqSymm (zero_lt_succ _)

private theorem prefix_distance (j M L k S T H K : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] radius (sndT (prefixValue j M L)) (sndT (prefixValue k S T)) H K) :
    Γ ⊢[PRAAx] distanceBounded (prefixValue j M L) (prefixValue k S T) H K := by
  let u := prefixValue j M L
  let v := prefixValue k S T
  let a := scale (two*total j M L) imaginaryCode
  let b := scale (two*total k S T) imaginaryCode
  let E := fact L*fact T
  let c := scale (fact T) a
  let d := scale (fact L) b
  have hL := fact_positive (Γ := Γ) L
  have hT := fact_positive (Γ := Γ) T
  have hE := positive_product (fact L) (fact T) hL hT
  have hc := represents_rescale u a (fact L) (fact T) (ofGaussian_represents _ _ hL)
  have hd := GaussianRationalSyntheticDivision.rescale_to v b (fact T) (fact L) E
    (ofGaussian_represents _ _ hT) (mul_comm _ _)
  have realNear := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hK h
  have realClear := (bounded_difference_iff _ _ _ _ E H K hE hK
    (RationalGaussianEmbedding.embed_from_representation _ _ _ hc.andE₂)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ hd.andE₂)).iffMp realNear
  have norm : Γ ⊢[PRAAx] normSq (GaussianRootAlgebra.sub c d) ≐
      normSq (GaussianRootAlgebra.sub (RationalGaussianEmbedding.native (ComplexLogarithmRemainder.im c))
        (RationalGaussianEmbedding.native (ComplexLogarithmRemainder.im d))) := by
    apply deriveNat
    simp only [normSq_eval,re_sub,im_sub,RationalGaussianEmbedding.native,c,d,a,b,re_scale,im_scale,
      imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact (bounded_difference_iff u v c d E H K hE hK hc hd).iffMpr
    (le_congr (congrMul (.eqRefl _) norm).eqSymm (.eqRefl _) realClear)

theorem forward_distance (p q A B C D H K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] radius (fraction A B) (fraction C D) H K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B)) (ap2 nameF q (data C D))
      ((unit p+unit q)*K+two*H*(unit p*unit q)) ((unit p*unit q)*K) := by
  have pos := positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) hK
  have ord := ordinate_radius p q A B C D H K hB hD hA hC h
  have raw := radius_congr (congrSnd (sample_at p A B)) (congrSnd (sample_at q C D))
    (.eqRefl _) (.eqRefl _) ord
  exact distance_congr (sample_at p A B).eqSymm (sample_at q C D).eqSymm (.eqRefl _) (.eqRefl _)
    (prefix_distance (A*mesh p) (B*mesh p) (clearing (B*mesh p))
      (C*mesh q) (D*mesh q) (clearing (D*mesh q)) _ _ pos raw)

end LeanProofs.IPRA.Analysis.GaussianArctangentForwardLipschitz
