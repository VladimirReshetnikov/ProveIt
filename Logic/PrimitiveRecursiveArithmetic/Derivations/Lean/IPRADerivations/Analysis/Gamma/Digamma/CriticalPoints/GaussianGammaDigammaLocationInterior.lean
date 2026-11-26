import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaDyadicLocation
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaRescale
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference

/-!
# Fixed interior margins at the primitive recursive digamma location

The two quarter-unit endpoint bounds, the upper digamma slope, and
the signs of the selected cell force every location sample into
[17/16, 31/16]. The regular location name therefore lies strictly
between one and two.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationInterior

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaCriticalSigns (quarter negativeQuarter one_upper two_lower)
open GaussianGammaDigammaDyadicCrossing (sample)
open GaussianGammaDigammaDyadicLocation (index lower locationF location_at selected_cell)
open GaussianGammaDigammaDyadicMesh (clock grid grid_positive grid_scale)
open GaussianGammaDigammaGridSign (zero_le_of_sign le_zero_of_negative)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedStrictOrderDifference (trans_weak weak_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product scalar_congr)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open RationalArithmetic (represents)
open RationalArgmin (rationalLE_congr)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalUpperRepresentation (upper_from_representations)
open RationalValueBounds (upper upper_congr upper_mono upper_of_order upper_order_left upper_order_right upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

private theorem quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (quarter : PTm n)) (ZT.ofNat one) (num 4) :=
  GaussianGammaDigammaHarmonicCells.point_fraction_represents one (num 4) (by ipra_le 3)

private theorem negative_quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (negativeQuarter : PTm n)) (-ZT.ofNat one) (num 4) := by
  let x : PTm n := quarter
  have h := RationalRepresentations.represents_negative (fstT x) (ZT.ofNat one) (num 4)
    (quarter_represents (Γ := Γ))
  have e := (congrFst (qzero_add (Γ := Γ) (qnegative x) (qnegative_canonical x))).eqTrans
    (fst_pair (RationalArithmetic.negative (fstT x)) (RationalArithmetic.negative (sndT x)))
  exact scalar_congr e.eqSymm (.eqRefl _) (.eqRefl _) h

private theorem endpoint_rescale (a i N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hN : Γ ⊢[PRAAx] le one N) (e : Γ ⊢[PRAAx] N*a ≐ N+i) :
    Γ ⊢[PRAAx] crossEquivalent DF DF (dd (N+i) N) (dd a one) :=
  GaussianGammaCompactCutoffAlignment.cross_data_congr DF DF (dd (N*a) N) (dd (N+i) N) (dd a one) (dd a one)
    (GaussianGammaDigammaRescale.datum_congr e (.eqRefl _)) (.eqRefl _)
    (GaussianGammaDigammaRescale.integer_rescale a N ha hN)

private theorem endpoint_left_upper (p : PTm n) : Γ ⊢[PRAAx]
    upper (sample (clock p) (grid p) zero) (fstT negativeQuarter) two (grid p) := by
  let N := grid p
  let t := clock p
  let c : PTm n := negativeQuarter
  let x := dd (N+zero) N
  have reg := grid_positive (Γ := Γ) p
  have hx := endpoint_rescale one zero N (le_refl one) reg (by ipra_ring)
  have ord := GaussianNamedRealOrderTransport.transport DF DF constantF constantF x (dd one one) c c
    hx (cross_refl _ _ (constant_regular c)) (one_upper (Γ := Γ)).andE₁
  have h : Γ ⊢[PRAAx] upper (sample t N zero) (fstT c) (N+N) (N*N) :=
    upper_congr (.eqRefl _) (congrFst (constant_at t c)) (.eqRefl _) (.eqRefl _)
      (real_order_at DF constantF x c t t ord)
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ reg reg) h (by ipra_le 0)

private theorem endpoint_right_lower (p : PTm n) : Γ ⊢[PRAAx]
    upper (fstT quarter) (sample (clock p) (grid p) (grid p)) two (grid p) := by
  let N := grid p
  let t := clock p
  let c : PTm n := quarter
  let x := dd (N+N) N
  have reg := grid_positive (Γ := Γ) p
  have hx := endpoint_rescale two N N (by ipra_le 1) reg (by ipra_ring)
  have ord := GaussianNamedRealOrderTransport.transport constantF constantF DF DF c c (dd two one) x
    (cross_refl _ _ (constant_regular c)) (cross_symm _ _ _ _ hx) (two_lower (Γ := Γ)).andE₁
  have h : Γ ⊢[PRAAx] upper (fstT c) (sample t N N) (N+N) (N*N) :=
    upper_congr (congrFst (constant_at t c)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (real_order_at constantF DF c x t t ord)
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ reg reg) h (by ipra_le 0)

private theorem grid_upper (p i j : PTm n) (h : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    upper (sample (clock p) (grid p) j) (sample (clock p) (grid p) i)
      (two*monus j i+two) (grid p) := by
  let N := grid p
  let t := clock p
  have hN := grid_positive (Γ := Γ) p
  have ordered : Γ ⊢[PRAAx] le (N+i) (N+j) :=
    add_le_add_left N h
  have direct := GaussianGammaDigammaLipschitz.unit_upper_at t t (N+i) (N+j) N hN (le_add_right _ _) ordered
  have e := natEq (((congrMonus (add_comm N j) (add_comm N i)).eqTrans (monus_add_add j i N)) :
    Γ ⊢[PRAAx] monus (N+j) (N+i) ≐ monus j i)
  refine upper_mono _ _ _ _ _ _ (denominator_positive N t t hN) direct ?_
  dsimp only [rateNumerator,rateDenominator]
  change Γ ⊢[PRAAx] le ((two*monus (N+j) (N+i)*N*N+N*(N+N))*N)
    ((two*monus j i+two)*(N*N*N))
  ipra_le 0 with (-2*𝔞(N)^3)*e

private theorem triangle_grid (a b c A C N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] upper a b A N) (j : Γ ⊢[PRAAx] upper b c C N) :
    Γ ⊢[PRAAx] upper a c (A+C) N :=
  upper_mono _ _ _ _ _ _ (positive_product _ _ hN hN) (upper_triangle _ _ _ _ _ _ _ h j) (by ipra_le 0)

private theorem negative_quarter_cost (A N : PTm n)
    (h : Γ ⊢[PRAAx] upper scalarZero (fstT negativeQuarter) A N) :
    Γ ⊢[PRAAx] le N (num 4*A) := by
  let u := ZT.ofNat (N*num 4)*ZT.ofNat zero
  let v := ZT.ofNat (N*one)*(-ZT.ofNat one)+ZT.ofNat (A*one*num 4)
  have e := zle_toZ (upper_from_representations scalarZero (fstT negativeQuarter) one (num 4) A N
    (ZT.ofNat zero) (-ZT.ofNat one) (scalar_zero_represents one) negative_quarter_represents h)
  apply le_of_eq_add (d := PolynomialBisection.slack u v)
  apply deriveNat
  change ZT.toZ Γ (ZT.ofNat (N*num 4)*ZT.ofNat zero)+𝔞(PolynomialBisection.slack u v) =
    ZT.toZ Γ (ZT.ofNat (N*one)*(-ZT.ofNat one)+ZT.ofNat (A*one*num 4)) at e
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat] at e
  ipra_simps
  linear_combination -e

private theorem quarter_cost (A N : PTm n)
    (h : Γ ⊢[PRAAx] upper (fstT quarter) scalarZero A N) :
    Γ ⊢[PRAAx] le N (num 4*A) := by
  let u := ZT.ofNat (N*one)*ZT.ofNat one
  let v := ZT.ofNat (N*num 4)*ZT.ofNat zero+ZT.ofNat (A*num 4*one)
  have e := zle_toZ (upper_from_representations (fstT quarter) scalarZero (num 4) one A N
    (ZT.ofNat one) (ZT.ofNat zero) quarter_represents (scalar_zero_represents one) h)
  apply le_of_eq_add (d := PolynomialBisection.slack u v)
  apply deriveNat
  change ZT.toZ Γ (ZT.ofNat (N*one)*ZT.ofNat one)+𝔞(PolynomialBisection.slack u v) =
    ZT.toZ Γ (ZT.ofNat (N*num 4)*ZT.ofNat zero+ZT.ofNat (A*num 4*one)) at e
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
  ipra_simps
  linear_combination -e

private theorem left_cell_cost (p : PTm n) : Γ ⊢[PRAAx] le (grid p) (num 8*index p+num 24) := by
  let i := index p
  let N := grid p
  let t := clock p
  have upperGrid := grid_upper (Γ := Γ) p zero (succ i) (zero_le (succ i))
  have sign := zero_le_of_sign _ (selected_cell (Γ := Γ) p).andE₂.andE₂
  have total := triangle_grid (sample t N (succ i)) (sample t N zero) (fstT negativeQuarter) _ _ N (grid_positive p)
    upperGrid (endpoint_left_upper p)
  have h := negative_quarter_cost _ N (upper_order_left _ _ _ _ _ sign total)
  have e := natEq (monus_zero (Γ := Γ) (succ i))
  ipra_le sl h with -8*e

private theorem right_cell_cost (p : PTm n) : Γ ⊢[PRAAx] le (grid p) (num 8*monus (grid p) (index p)+num 16) := by
  let i := index p
  let N := grid p
  let t := clock p
  have cell := selected_cell (Γ := Γ) p
  have upperGrid := grid_upper p i N (le_of_lt cell.andE₁)
  have sign := le_zero_of_negative _ cell.andE₂.andE₁
  have total := triangle_grid (fstT quarter) (sample t N N) (sample t N i) _ _ N (grid_positive p)
    (endpoint_right_lower p) upperGrid
  have h := quarter_cost _ N (upper_order_right _ _ _ _ _ total sign)
  ipra_le sl h

private theorem grid_minimum (p : PTm n) : Γ ⊢[PRAAx] le (num 64) (grid p) :=
  le_congr (.eqRefl _) (grid_scale p).eqSymm (by ipra_le 64*sl (GaussianCoefficientNameBounds.unit_positive p))

theorem location_lower_margin (p : PTm n) : Γ ⊢[PRAAx] le (num 17*grid p) (num 16*lower p) := by
  unfold lower
  ipra_le 2*sl (left_cell_cost p)+sl (grid_minimum p)+16

theorem location_upper_margin (p : PTm n) : Γ ⊢[PRAAx] le (num 16*lower p) (num 31*grid p) := by
  have e := natEq (eq_add_of_le (le_of_lt (selected_cell (Γ := Γ) p).andE₁))
  unfold lower
  ipra_le 2*sl (right_cell_cost p)+sl (grid_minimum p)+32 with 16*e

theorem location_lower_named (x : PTm n) :
    Γ ⊢[PRAAx] realOrder constantF locationF (fraction (num 17) (num 16)) x := by
  refine .allI (.allI ?_)
  have h := location_lower_margin (Γ := (Γ.map Fm.shift).map Fm.shift) (var 0)
  have r := fractions_order (num 17) (num 16) (lower (var 0)) (grid (var 0))
    (by ipra_le 15) (grid_positive _) (le_congr (mul_comm _ _) (mul_comm _ _) h)
  simp only [Syn.shift, GaussianPositiveRationalLogarithm.subst_fraction, PTm.subst_num]
  exact upper_of_order _ _ _ _
    (rationalLE_congr (congrFst (constant_at (var 1) _)).eqSymm
      (congrFst (location_at (var 0) (Syn.shift (Syn.shift x)))).eqSymm r)

theorem location_upper_named (x : PTm n) :
    Γ ⊢[PRAAx] realOrder locationF constantF x (fraction (num 31) (num 16)) := by
  refine .allI (.allI ?_)
  have h := location_upper_margin (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1)
  have r := fractions_order (lower (var 1)) (grid (var 1)) (num 31) (num 16)
    (grid_positive _) (by ipra_le 15) h
  simp only [Syn.shift, GaussianPositiveRationalLogarithm.subst_fraction, PTm.subst_num]
  exact upper_of_order _ _ _ _
    (rationalLE_congr (congrFst (location_at (var 1) (Syn.shift (Syn.shift x)))).eqSymm
      (congrFst (constant_at (var 0) _)).eqSymm r)

private theorem fraction_strict (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] lt (d*a) (c*b)) :
    Γ ⊢[PRAAx] strictOrder constantF constantF (fraction a b) (fraction c d) :=
  .andI (constant_order _ _ (fractions_order a b c d hb hd (le_of_lt h))) (strict_fractions a b c d hb hd h)

theorem strict_interior (x : PTm n) : Γ ⊢[PRAAx]
    strictOrder constantF locationF (fraction one one) x ⋏ strictOrder locationF constantF x (fraction two one) := by
  have h16 : Γ ⊢[PRAAx] le one (num 16) := by ipra_le 15
  exact .andI
    (trans_weak _ _ _ _ _ _ (fraction_strict one one (num 17) (num 16) (le_refl _) h16 (by unfold lt; ipra_le 0))
      (location_lower_named x))
    (weak_trans _ _ _ _ _ _ (location_upper_named x)
      (fraction_strict (num 31) (num 16) two one h16 (le_refl _) (by unfold lt; ipra_le 0)))

theorem actual_original_digamma_dyadic_location_interior_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (strictOrder constantF locationF (fraction one one) (var 0) ⋏
      strictOrder locationF constantF (var 0) (fraction two one)) :=
  closeUniv 1 (strict_interior (var 0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationInterior
