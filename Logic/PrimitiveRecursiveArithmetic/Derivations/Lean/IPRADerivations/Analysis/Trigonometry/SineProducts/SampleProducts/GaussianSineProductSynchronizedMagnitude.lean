import IPRADerivations.Analysis.Trigonometry.SineProducts.SampleProducts.GaussianSineProductSynchronizedRow
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Uniform inverse-square bound for the actual synchronized Cayley row

At one later clock, the literal numerator sine has modulus at most
(6R/m) and every literal divided Cayley sine for (1le kle J)
has modulus at least (3k/(2m)). The quotient squared is therefore
bounded by (16R^2/k^2).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductSynchronizedMagnitude

open_ipra
open GaussianSineProductSynchronizedRow (angleData angleSineF angleSineData FactorBudget sincValue sampledRoot actualFactor
  modulus_eq argument_input sine_factor_error)
open GaussianSineProductT4Budget (halfIndex multiple)
open GaussianSineProductScaledArguments (observation_bound_at)
open GaussianNamedSincQuadraticBounds (quadratic_bound)
open GaussianSineRawRootBinding (raw_root_error_later)
open GaussianArctangentDivisionAngles (modulus coefficient odd_source)
open GaussianArctangentDivisionAngleResidual (sineSample mesh index mesh_positive)
open GaussianArctangentDivisionSinePositive (exactSineData sine_lower)
open GaussianArctangentCayleyTrig (sineCode sinePoint)
open GaussianNamedSineFromExponential (sineF)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedPositiveExponentialOrder (real_order_at scalar_coordinate_distance)
open RationalValueBounds (upper upper_mono upper_congr upper_of_radius upper_triangle positive_cancel)
open RationalRepresentedUpper (to_signed left right)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (ofGaussian_represents scalar_congr positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical)
open GaussianRationalReciprocal (qone qone_bounded reciprocal bounded_product bounded_negative bound_congr)
open GaussianRationalSyntheticDivision (qadd_sub_cancel)
open GaussianRationalLowerBounds (lower lower_from_representation product_lower inverse_bound)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianSineRootNormalization (normalizedFactor)
open ComplexLogarithmRemainder (normSq normSq_code)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def reserve (z R B K x : PTm n) : PTm n :=
  (FactorBudget (angleData z R B K x)+num 22)*modulus (halfIndex R K)
def clock (z R B K x p : PTm n) : PTm n := p+reserve z R B K x
def fine (z R B K x p : PTm n) : Fm PTm n := le (reserve z R B K x) (unit p)

ipra_subst reserve [FactorBudget]
ipra_subst clock
ipra_subst fine

theorem clock_later (z R B K x p : PTm n) : Γ ⊢[PRAAx] le p (clock z R B K x p) :=
  le_add_right _ _
theorem clock_fine (z R B K x p : PTm n) : Γ ⊢[PRAAx] fine z R B K x (clock z R B K x p) :=
  le_trans (le_add_left _ _) (le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow _))

private theorem cutoff_room (R K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le (num 8*R) (modulus (halfIndex R K)) := by
  have base := le_mul_mono (positive_product K K hK hK) (le_mul_mono (le_refl R) hR)
  have lower : Γ ⊢[PRAAx] le R ((K*K)*(R*R)) := le_congr (by ipra_ring) (.eqRefl _) base
  have e := modulus_eq (Γ := Γ) R K
  apply le_congr (.eqRefl _) e.eqSymm
  unfold multiple
  ipra_le 8*sl lower+1

theorem numerator_bound (z R B K x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hp : Γ ⊢[PRAAx] fine z R B K x p) :
    Γ ⊢[PRAAx] bounded (ap2 angleSineF p (angleSineData z R B K x)) (num 6*R) (modulus (halfIndex R K)) := by
  let m := modulus (halfIndex R K)
  let U := unit p
  let A := num 4*R
  let d := angleData z R B K x
  let F := FactorBudget d
  let s := sincValue p d
  let u := ap2 angleSineF p (angleSineData z R B K x)
  let a := ap2 GaussianSineProductScaledArguments.nameF p d
  let D := two*(m*m)
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (le_succ_self one) (positive_product _ _ hm hm)
  have room : Γ ⊢[PRAAx] le (num 8*R) m := cutoff_room R K hR hK
  have am : Γ ⊢[PRAAx] le A m :=
    le_trans (by dsimp only [A]; ipra_le 4*𝔞 R) room
  have input := argument_input z R B K x hR hK hB hz
  have e : Γ ⊢[PRAAx] distanceBounded s qone (A*A) D :=
    quadratic_bound GaussianSineProductScaledArguments.nameF one d A m p hm am input.andE₂
  have sNorm := norm_from_distance s qone (A*A) D one one hD (le_refl one) e qone_bounded
  have prefactor : Γ ⊢[PRAAx] bounded s (num 5) (num 4) := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD (le_refl one)) h4 _ sNorm
    have square := le_mul_mono room room
    dsimp only [A,D]
    ipra_le sl square+𝔞 m*𝔞 m
  have ha : Γ ⊢[PRAAx] bounded a A m := observation_bound_at z R B m x p hB hm hz
  have product := bounded_product a s A m (num 5) (num 4) hm h4 ha prefactor
  have as : Γ ⊢[PRAAx] bounded (qmul a s) (num 5*R) m :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hm h4) hm
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [A]; ipra_ring)) product
  have sample := sine_factor_error d p input.andE₁
  have analytic : Γ ⊢[PRAAx] bounded u (F*m+(num 5*R)*U) (U*m) :=
    norm_from_distance u (qmul a s) F U (num 5*R) m hu hm sample as
  have budget : Γ ⊢[PRAAx] le (F*m) U :=
    le_trans (le_mul_mono (le_add_right F (num 22)) (le_refl m)) hp
  have spend : Γ ⊢[PRAAx] le (F*m) (R*U) :=
    le_trans budget (le_congr (one_mul U) (.eqRefl _) (le_mul_mono hR (le_refl U)))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hu hm) hm (by ipra_le 𝔞 m*sl spend) analytic

private theorem same_denominator_upper (a b c A C B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] upper a b A B) (hb : Γ ⊢[PRAAx] upper b c C B) :
    Γ ⊢[PRAAx] upper a c (A+C) B :=
  upper_mono _ _ _ _ _ _ (positive_product _ _ hB hB) (upper_triangle _ _ _ _ _ _ _ ha hb)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl ((A+C)*(B*B))))

private theorem sampled_root_upper (p k J x : PTm n) (hk : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] upper (fstT (coefficient k (modulus J)))
      (fstT (sineSample (GaussianSineSampleRootGuards.clock p J) k J x)) (num 11) (unit p) := by
  let f := sineF GaussianArctangentDivisionAngles.nameF
  let m := modulus J
  let c := coefficient k m
  let d := exactSineData k m x
  let u := ap2 f p d
  let v := sineSample (GaussianSineSampleRootGuards.clock p J) k J x
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have s := sine_lower k m x (odd_source k J hk)
  have first := upper_congr (congrFst (constant_at p c)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (real_order_at constantF f c d p p s)
  have left : Γ ⊢[PRAAx] upper (fstT c) (fstT u) two U :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hU hU) first
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))
  have raw := raw_root_error_later p (GaussianSineSampleRootGuards.clock p J) k J x hk
    (GaussianSineSampleRootGuards.clock_later p J)
  have right : Γ ⊢[PRAAx] upper (fstT u) (fstT v) (num 9) U :=
    upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hU raw)
  exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (same_denominator_upper _ _ _ _ _ _ hU left right)

theorem denominator_bound (p k J x : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hJ : Γ ⊢[PRAAx] le k J)
    (hp : Γ ⊢[PRAAx] le (num 22*modulus J) (unit p)) :
    Γ ⊢[PRAAx] lower (sineSample (GaussianSineSampleRootGuards.clock p J) k J x)
      (num 3*k) (two*modulus J) := by
  let q := GaussianSineSampleRootGuards.clock p J
  let a := mesh q k J x
  let j := index q k J x
  let N := two*a*j
  let E := GaussianArctangentCayleyValues.denominator a j
  let m := modulus J
  let U := unit p
  let c := coefficient k m
  let v := sineSample q k J x
  let L := left (ZT.ofNat (two*k)) E U
  let H := right (ZT.ofNat N) m E (num 11) U
  have hE : Γ ⊢[PRAAx] le one E := GaussianArctangentCayleyValues.denominator_positive a j (mesh_positive q k J x)
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hU := unit_positive (Γ := Γ) p
  have cRep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT c) (ZT.ofNat (two*k)) m := by
    apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ hm).andE₁
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat,mul_one]
  have vRep := ofGaussian_represents (sineCode a j) E hE
  have vReal : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT v) (ZT.ofNat N) E := by
    apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) vRep.andE₁
    apply ZT.derive
    dsimp only [N]
    simp only [sineCode,ComplexLogarithmRemainder.eval_re_code]
  have signed : Γ ⊢[PRAAx] zle L H :=
    to_signed _ _ _ _ m E (num 11) U cRep vReal (sampled_root_upper p k J x hJ)
  have cost : Γ ⊢[PRAAx] le ((num 22*m)*E) (k*U*E) :=
    le_mul_mono (le_trans hp (le_congr (one_mul U) (.eqRefl _) (le_mul_mono hk (le_refl U)))) (le_refl E)
  have ray : Γ ⊢[PRAAx] le ((num 3*k)*E) ((two*m)*N) := by
    apply positive_cancel hU
    let D := monus (H.pos+L.neg) (L.pos+H.neg)
    let A := monus (k*U*E) ((num 22*m)*E)
    refine le_of_eq_add (d := two*D+A) ?_
    have lin := zle_toZ signed
    have cap := natEq (eq_add_of_le cost)
    apply deriveNat
    dsimp only [L,H,D,A] at lin ⊢
    simp only [left,right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at lin ⊢
    ipra_simps
    linear_combination -2*lin+cap
  have norm : Γ ⊢[PRAAx] normSq (sineCode a j) ≐ N*N := by
    apply deriveNat
    unfold sineCode
    rw [normSq_code]
    simp only [ZT.toZ_ofNat]
    dsimp only [N]
    ipra_simps
    ring
  exact lower_from_representation _ _ E _ _ hE (positive_product _ _ (le_succ_self _) hm) vRep
    (le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] ((two*m)*N)*((two*m)*N) ≐ (two*m)*(two*m)*(N*N)).eqTrans
      (congrMul (.eqRefl _) norm.eqSymm)) (le_mul_mono ray ray))

theorem factor_bound_at (z R B K i x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i (halfIndex R K)) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hp : Γ ⊢[PRAAx] fine z R B K x p) :
    Γ ⊢[PRAAx] distanceBounded (actualFactor z R B K i x p) qone (num 16*(R*R)) (succ i*succ i) := by
  let J := halfIndex R K
  let m := modulus J
  let k := succ i
  let u := ap2 angleSineF p (angleSineData z R B K x)
  let v := sampledRoot R K i x p
  let A := num 3*k
  let C := two*m
  let vSq := qmul v v
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hA : Γ ⊢[PRAAx] le one A :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (by ipra_le 2 : Γ ⊢[PRAAx] le one (num 3)) hk)
  have hC : Γ ⊢[PRAAx] le one C := positive_product _ _ (le_succ_self _) hm
  have guard : Γ ⊢[PRAAx] le (num 22*m) (unit p) :=
    le_trans (le_mul_mono (le_add_left _ _) (le_refl m)) hp
  have hv : Γ ⊢[PRAAx] lower v A C := denominator_bound p k J x hk hi guard
  have square : Γ ⊢[PRAAx] lower vSq (A*A) (C*C) := product_lower _ _ _ _ _ _ hC hC hv hv
  have hAA := positive_product A A hA hA
  have hCC := positive_product C C hC hC
  have hInv : Γ ⊢[PRAAx] bounded (reciprocal vSq) (C*C) (A*A) :=
    inverse_bound vSq (A*A) (C*C) hAA hCC square
  have hu := numerator_bound z R B K x p hR hK hB hz hp
  have hUU := bounded_product u u (num 6*R) m (num 6*R) m hm hm hu hu
  have hRaw := bounded_product _ _ _ _ _ _ (positive_product _ _ hm hm) hAA hUU hInv
  have hprod : Γ ⊢[PRAAx] bounded (qmul (qmul u u) (reciprocal vSq)) (num 16*(R*R)) (k*k) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hm hm) hAA)
      (positive_product _ _ hk hk)
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by dsimp only [A,C]; ipra_ring)) hRaw
  exact bound_congr (qadd_sub_cancel qone _ (qnegative_canonical _)).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative _ _ _ (positive_product _ _ hk hk) hprod)

theorem factor_bound (z R B K i x p : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i (halfIndex R K)) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (actualFactor z R B K i x (clock z R B K x p)) qone (num 16*(R*R)) (succ i*succ i) :=
  factor_bound_at z R B K i x _ hR hK hB hi hz (clock_fine z R B K x p)

theorem actual_synchronized_inverse_square_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (((le one (var 5) ⋏ le one (var 3)) ⋏ le one (var 4)) ⟶ lt (var 2) (halfIndex (var 5) (var 3)) ⟶
      ComplexLogarithmRemainder.bounded (var 6) (var 5*var 4) ⟶
      distanceBounded (actualFactor (var 6) (var 5) (var 4) (var 3) (var 2) (var 1)
        (clock (var 6) (var 5) (var 4) (var 3) (var 1) (var 0))) qone (num 16*(var 5*var 5)) (succ (var 2)*succ (var 2))) :=
  closeUniv 7 (.impI (.impI (.impI (factor_bound _ _ _ _ _ _ _ hyp2.andE₁.andE₁ hyp2.andE₁.andE₂ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSineProductSynchronizedMagnitude
