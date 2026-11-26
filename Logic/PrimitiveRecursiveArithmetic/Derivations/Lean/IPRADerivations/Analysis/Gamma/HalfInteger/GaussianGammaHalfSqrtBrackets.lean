import IPRADerivations.Analysis.Stirling.Wallis.GaussianGammaHalfWallisRate
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianNamedPositiveExponentialOrder
import IPRADerivations.Foundations.SquareRootRelationalCandidates

/-!
# Stability of bounded rational square-root selection

The returned lower candidate from bounded search has error at most
(K+1)/2^p with respect to a nonnegative rational whose square matches
the search input within K^2/2^(2p). Both square bracket edges are used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfSqrtBrackets

open_ipra
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product scalar_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Foundations.SquareRootRelationalCandidates (candidate)
open RationalUpperRepresentation (upper_from_representations)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem fraction_first_represents (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction a b)) (ZT.ofNat a) b := by
  let x := RationalCubeMidpoint.fraction a b
  have e : Γ ⊢[PRAAx] RationalArithmetic.recode x ≐ fstT (fraction a b) :=
    (fst_pair _ _).eqSymm.eqTrans (congrFst (GaussianEulerDecayOrder.fraction_embedding a b hb))
  exact scalar_congr e (.eqRefl _) (.eqRefl _)
    (RationalGaussianEmbedding.scalar_recode_represents _ _ _ (RationalCubeMidpoint.fraction_represents a b hb))

private theorem native_upper (a b c d K D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] RationalValueBounds.upper (fstT (fraction a b)) (fstT (fraction c d)) K D) :
    Γ ⊢[PRAAx] le (D*(a*d)) (D*(c*b)+K*b*d) := by
  let l := ZT.ofNat (D*d)*ZT.ofNat a
  let r := ZT.ofNat (D*b)*ZT.ofNat c+ZT.ofNat (K*b*d)
  have e := zle_toZ (upper_from_representations _ _ b d K D _ _
    (fraction_first_represents a b hb) (fraction_first_represents c d hd) h)
  apply le_of_eq_add (d := PolynomialBisection.slack l r)
  apply deriveNat
  dsimp only [l,r]
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
  unfold PolynomialBisection.slack
  ipra_simps
  linear_combination -e

theorem fraction_gap (a b c d K D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) K D) :
    Γ ⊢[PRAAx] le (D*(a*d)) (D*(c*b)+K*b*d) ⋏
      le (D*(c*b)) (D*(a*d)+K*d*b) := by
  have left := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hD h
  have right := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hD
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hD h)
  exact .andI (native_upper a b c d K D hb hd (RationalValueBounds.upper_of_radius _ _ _ _ left))
    (native_upper c d a b K D hd hb (RationalValueBounds.upper_of_radius _ _ _ _ right))

theorem square_budget (x y K : PTm n)
    (h : Γ ⊢[PRAAx] le (x*x) (y*y+K*K)) :
    Γ ⊢[PRAAx] le x (y+K) := by
  refine .orE (le_total x y) ?_ ?_
  · exact le_trans Prf.hyp0 (le_add_right _ _)
  · let E := monus x y
    let Δ := le y x :: Γ
    have lhs : Δ ⊢[PRAAx] le (y*y+E*E) (x*x) := by
      ipra_le 2 * 𝔞 y * 𝔞 E with (𝔞 x + 𝔞 y + 𝔞 E) * natEq (eq_add_of_le (Γ := Δ) (Prf.hyp0 : Δ ⊢[PRAAx] le y x))
    have small : Δ ⊢[PRAAx] le (E*E) (K*K) :=
      le_of_add_le_add_right (c := y*y)
        (le_congr (add_comm (y*y) (E*E)) (add_comm (y*y) (K*K)) (le_trans lhs h.wk))
    exact le_congr ((add_comm E y).eqTrans (eq_add_of_le Prf.hyp0).eqSymm) (add_comm K y)
      (add_le_add_right y (nat_sqrt_mono small))

theorem bounded_root_close (a b A B p K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) (fraction A B) (K*K) (unit p*unit p)) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction (candidate A B p) (unit p)) (K+one) (unit p) := by
  let H := unit p
  let j := candidate A B p
  let x := a*H
  let y := j*b
  let z := succ j*b
  let w := K*b
  have hH : Γ ⊢[PRAAx] le one H := unit_positive p
  have bounds := fraction_gap (a*a) (b*b) A B (K*K) (H*H) (positive_product _ _ hb hb) hB
    (positive_product _ _ hH hH) h
  have lo : Γ ⊢[PRAAx] le (B*j*j) (A*(H*H)) :=
    LeanProofs.IPRA.Foundations.SquareRootRelationalCandidates.candidate_lower A B p hB
  have hi : Γ ⊢[PRAAx] le (A*(H*H)) (B*succ j*succ j) :=
    LeanProofs.IPRA.Foundations.SquareRootRelationalCandidates.candidate_upper A B p hB
  have above : Γ ⊢[PRAAx] le (B*(x*x)) (B*(z*z+w*w)) := by
    dsimp only [x,z,w]
    ipra_le sl bounds.andE₁ + 𝔞 (b*b) * sl hi
  have below : Γ ⊢[PRAAx] le (B*(y*y)) (B*(x*x+w*w)) := by
    dsimp only [x,y,w]
    ipra_le 𝔞 (b*b) * sl lo + sl bounds.andE₂
  have left := square_budget x z w (RationalValueBounds.positive_cancel hB above)
  have right := square_budget y x w (RationalValueBounds.positive_cancel hB below)
  have less : Γ ⊢[PRAAx] le x (y+(K+one)*b) :=
    le_congr (.eqRefl _) (by dsimp only [z,y,w]; ipra_ring) left
  have more : Γ ⊢[PRAAx] le y (x+(K+one)*b) :=
    le_trans right (by dsimp only [w]; ipra_le 𝔞 b)
  have east : Γ ⊢[PRAAx] le (H*(a*H)) (H*(j*b)+(K+one)*b*H) :=
    le_congr (mul_comm x H) (by dsimp only [y]; ipra_ring) (mul_le_mul_right H less)
  have west : Γ ⊢[PRAAx] le (H*(j*b)) (H*(a*H)+(K+one)*H*b) :=
    le_congr (mul_comm y H) (by dsimp only [x]; ipra_ring) (mul_le_mul_right H more)
  exact GaussianGammaHalfWallisRate.fraction_distance _ _ _ _ _ _ hb hH hH east west

theorem actual_bounded_sqrt_selection_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((le one (var 1) ⋏ le one (var 3)) ⟶
        distanceBounded (fraction (var 0*var 0) (var 1*var 1)) (fraction (var 2) (var 3))
          (var 5*var 5) (unit (var 4)*unit (var 4)) ⟶
        distanceBounded (fraction (var 0) (var 1)) (fraction (candidate (var 2) (var 3) (var 4)) (unit (var 4)))
          (var 5+one) (unit (var 4))) :=
  closeUniv 6 (.impI (.impI (bounded_root_close _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfSqrtBrackets
