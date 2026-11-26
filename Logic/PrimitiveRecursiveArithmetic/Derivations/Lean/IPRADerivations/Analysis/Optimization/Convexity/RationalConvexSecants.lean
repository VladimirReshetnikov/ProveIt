import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexSecantWeights
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSyntheticBounds

/-!
# The secant estimate on the original rational samples

Sample codes have independent positive denominators. A common scale
reflects the two convexity comparisons into finite natural arithmetic.
The affine sample bounds are then transported back to the same codes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexSecants

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)
open RationalArgmin (rationalLE denominator_positive)
open RationalArithmetic (represents add multiply)
open RationalSupMetric (denominatorOf numeratorOf)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_nonnegative)
open GaussianRationalHorner (scalar_congr scalar_rescale scalar_add_same)
open GaussianRationalMetric (comparison_to_cleared comparison_of_cleared)
open RationalConvexSecantWeights (secant_with_error)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scale (a q : PTm n) : PTm n := multiply (natCode a) q
def nonnegative (q : PTm n) : Fm PTm n := rationalLE (natCode zero) q

def affine (a b c U V E : PTm n) : PTm n :=
  add (add (scale a U) (scale b V)) (scale c E)

def within (w t u U V B E : PTm n) : Fm PTm n :=
  rationalLE (scale w V) (affine u t w U B E)

def bound (δ t U V M E : PTm n) : Fm PTm n :=
  rationalLE (scale δ V) (affine δ t δ U M E)

def naturalNumerator (q : PTm n) : PTm n := monus (numeratorOf q).pos (numeratorOf q).neg

theorem nonnegative_representation (q : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) :
    Γ ⊢[PRAAx] represents q (ZT.ofNat (naturalNumerator q)) (denominatorOf q) := by
  have h := GaussianRationalL1.nonnegative_of_lower _ _ (natCode_nonnegative zero) hq
  have e := natEq (eq_add_of_le h)
  apply ZT.derive
  rw [ZT.toZ_mul,ZT.toZ_mul]
  simp only [ZT.toZ_ofNat]
  simp only [ZT.toZ,naturalNumerator]
  ipra_simps
  linear_combination -Groth.ι (Q.mk Γ (denominatorOf q))*e

theorem multiply_natural_representation (a q u D : PTm n)
    (hq : Γ ⊢[PRAAx] represents q (ZT.ofNat u) D) :
    Γ ⊢[PRAAx] represents (scale a q) (ZT.ofNat (a*u)) D := by
  have h := RationalRepresentations.represents_multiply (natCode a) q _ _ one D (natCode_represents a) hq
  refine scalar_congr (.eqRefl _) ?_ (one_mul D) h
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]

theorem add_natural_representation (a b u v D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (ha : Γ ⊢[PRAAx] represents a (ZT.ofNat u) D) (hb : Γ ⊢[PRAAx] represents b (ZT.ofNat v) D) :
    Γ ⊢[PRAAx] represents (add a b) (ZT.ofNat (u+v)) D := by
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl D) (scalar_add_same _ _ _ _ _ hD ha hb)
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_ofNat,Q.mk_add,map_add]

theorem affine_representation (a b c U V E u v e D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hu : Γ ⊢[PRAAx] represents U (ZT.ofNat u) D) (hv : Γ ⊢[PRAAx] represents V (ZT.ofNat v) D)
    (he : Γ ⊢[PRAAx] represents E (ZT.ofNat e) D) : Γ ⊢[PRAAx]
    represents (affine a b c U V E) (ZT.ofNat (a*u+b*v+c*e)) D :=
  add_natural_representation _ _ _ _ D hD
    (add_natural_representation _ _ _ _ D hD
      (multiply_natural_representation a U u D hu) (multiply_natural_representation b V v D hv))
    (multiply_natural_representation c E e D he)

theorem rescaled_representation (q t D : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q)
    (hD : Γ ⊢[PRAAx] denominatorOf q*t ≐ D) :
    Γ ⊢[PRAAx] represents q (ZT.ofNat (naturalNumerator q*t)) D := by
  have h := scalar_rescale q (ZT.ofNat (naturalNumerator q)) (denominatorOf q) t
    (nonnegative_representation q hq)
  refine scalar_congr (.eqRefl _) ?_ hD h
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]

theorem compare_same_to_natural (a b u v D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (ha : Γ ⊢[PRAAx] represents a (ZT.ofNat u) D) (hb : Γ ⊢[PRAAx] represents b (ZT.ofNat v) D)
    (h : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx] le u v :=
  RationalValueBounds.positive_cancel hD
    (le_congr (.eqRefl _) (mul_comm _ _) (comparison_to_cleared a b u v D D ha hb h))

theorem compare_same_from_natural (a b u v D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (ha : Γ ⊢[PRAAx] represents a (ZT.ofNat u) D) (hb : Γ ⊢[PRAAx] represents b (ZT.ofNat v) D)
    (h : Γ ⊢[PRAAx] le u v) : Γ ⊢[PRAAx] rationalLE a b :=
  comparison_of_cleared a b u v D D hD hD ha hb
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right D h))

theorem rational_secant_with_error (w t u δ U V B M E : PTm n)
    (hw : Γ ⊢[PRAAx] w ≐ t+u) (hδ : Γ ⊢[PRAAx] le δ w)
    (hU : Γ ⊢[PRAAx] nonnegative U) (hV : Γ ⊢[PRAAx] nonnegative V)
    (hB : Γ ⊢[PRAAx] nonnegative B) (hM : Γ ⊢[PRAAx] nonnegative M)
    (hE : Γ ⊢[PRAAx] nonnegative E) (hBM : Γ ⊢[PRAAx] rationalLE B M)
    (h : Γ ⊢[PRAAx] within w t u U V B E) : Γ ⊢[PRAAx] bound δ t U V M E := by
  let au := denominatorOf U
  let av := denominatorOf V
  let ab := denominatorOf B
  let am := denominatorOf M
  let ae := denominatorOf E
  let D := au*av*ab*am*ae
  have hD : Γ ⊢[PRAAx] le one D := RationalAlgebra.positive_product
    (RationalAlgebra.positive_product (RationalAlgebra.positive_product
      (RationalAlgebra.positive_product (denominator_positive U) (denominator_positive V))
      (denominator_positive B)) (denominator_positive M)) (denominator_positive E)
  have ru := rescaled_representation U (av*ab*am*ae) D hU (by dsimp [D,au,av,ab,am,ae]; ipra_ring)
  have rv := rescaled_representation V (au*ab*am*ae) D hV (by dsimp [D,au,av,ab,am,ae]; ipra_ring)
  have rb := rescaled_representation B (au*av*am*ae) D hB (by dsimp [D,au,av,ab,am,ae]; ipra_ring)
  have rm := rescaled_representation M (au*av*ab*ae) D hM (by dsimp [D,au,av,ab,am,ae]; ipra_ring)
  have re := rescaled_representation E (au*av*ab*am) D hE (by dsimp [D,au,av,ab,am,ae]; ipra_ring)
  have h₁ := compare_same_to_natural _ _ _ _ D hD
    (multiply_natural_representation w V _ D rv) (affine_representation u t w U B E _ _ _ D hD ru rb re) h
  have h₂ := compare_same_to_natural B M _ _ D hD rb rm hBM
  exact compare_same_from_natural _ _ _ _ D hD
    (multiply_natural_representation δ V _ D rv) (affine_representation δ t δ U M E _ _ _ D hD ru rm re)
    (le_congr (.eqRefl _) (by ipra_ring) (secant_with_error w t u δ _ _ _ _ _ hw h₁ h₂ hδ))

def nonnegativeSamples (a x y b m e : PTm n) : Fm PTm n :=
  nonnegative a ⋏ (nonnegative x ⋏ (nonnegative y ⋏ (nonnegative b ⋏ (nonnegative m ⋏ nonnegative e))))

/-- Both directions use the same endpoints, budget and sample tolerance. -/
theorem rational_two_endpoints (D P Q X Y a x y b m e : PTm n)
    (hPX : Γ ⊢[PRAAx] le P X) (hXY : Γ ⊢[PRAAx] le X Y) (hYQ : Γ ⊢[PRAAx] le Y Q)
    (hn : Γ ⊢[PRAAx] nonnegativeSamples a x y b m e)
    (ha : Γ ⊢[PRAAx] rationalLE a m) (hb : Γ ⊢[PRAAx] rationalLE b m)
    (hLeft : Γ ⊢[PRAAx] within (RationalConvexSecantWeights.leftWidth P Y)
      (RationalConvexSecantWeights.displacement X Y) (RationalConvexSecantWeights.leftRemainder P X) y x a e)
    (hRight : Γ ⊢[PRAAx] within (RationalConvexSecantWeights.rightWidth D Q X)
      (RationalConvexSecantWeights.displacement X Y) (RationalConvexSecantWeights.rightRemainder D Q Y) x y b e) :
    Γ ⊢[PRAAx] bound (RationalConvexSecantWeights.margin D P) (RationalConvexSecantWeights.displacement X Y) y x m e ⋏
      bound (RationalConvexSecantWeights.margin D P) (RationalConvexSecantWeights.displacement X Y) x y m e := by
  open RationalConvexSecantWeights in
  exact .andI
    (rational_secant_with_error _ _ _ _ _ _ _ _ _
      (left_width P X Y hPX hXY) (left_margin D P Y (le_trans hPX hXY))
      hn.andE₂.andE₂.andE₁ hn.andE₂.andE₁ hn.andE₁ hn.andE₂.andE₂.andE₂.andE₂.andE₁
      hn.andE₂.andE₂.andE₂.andE₂.andE₂ ha hLeft)
    (rational_secant_with_error _ _ _ _ _ _ _ _ _
      (right_width D Q X Y hXY hYQ) (right_margin D P Q X (le_trans hXY hYQ))
      hn.andE₂.andE₁ hn.andE₂.andE₂.andE₁ hn.andE₂.andE₂.andE₂.andE₁ hn.andE₂.andE₂.andE₂.andE₂.andE₁
      hn.andE₂.andE₂.andE₂.andE₂.andE₂ hb hRight)

theorem actual_rational_secant_with_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((var 0 ≐ var 1+var 2 ⋏ le (var 3) (var 0)) ⟶
      (nonnegative (var 4) ⋏ (nonnegative (var 5) ⋏ (nonnegative (var 6) ⋏
        (nonnegative (var 7) ⋏ (nonnegative (var 8) ⋏ rationalLE (var 6) (var 7)))))) ⟶
      within (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 8) ⟶
      bound (var 3) (var 1) (var 4) (var 5) (var 7) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (rational_secant_with_error _ _ _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂.andE₂.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalConvexSecants
