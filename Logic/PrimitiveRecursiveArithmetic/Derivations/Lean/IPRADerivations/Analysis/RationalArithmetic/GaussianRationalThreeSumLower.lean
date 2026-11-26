import IPRADerivations.Analysis.Exponential.GaussianNamedPositiveExponentialOrder
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart
import IPRADerivations.Analysis.RationalArithmetic.RationalRepresentedUpper

/-!
# One-sided order from the actual three-piece observation sum

The raw split is left + (middle + right). Independent signed lower
allowances for both tails bound the middle above by the whole split.
An actual Gaussian observation error then transfers that upper order
to the original whole observation. All point codes may be arbitrary.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalThreeSumLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd positive_product scalar_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open ComplexLogarithmRemainder (re)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents)
open RationalValueBounds (upper upper_triangle upper_of_radius upper_mono upper_congr)
open RationalRepresentedUpper (to_signed from_signed)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def split (l m r : PTm n) : PTm n := qadd l (qadd m r)
def numerator (A B C D E F : PTm n) : PTm n := (C*F+E*D)*B+A*(D*F)
def denominator (B D F : PTm n) : PTm n := (D*F)*B

@[simp] theorem subst_split {s : ℕ} (σ : Fin n → PTm s) (l m r : PTm n) :
    Syn.subst σ (split l m r) = split (Syn.subst σ l) (Syn.subst σ m) (Syn.subst σ r) := by simp [split]

/-- Signed represented arithmetic proves the lower-tail step before any
Gaussian distance estimate is used. No raw canonicality is required. -/
theorem middle_split_upper (l m r C D E F : PTm n)
    (hl : Γ ⊢[PRAAx] upper scalarZero (fstT l) C D)
    (hr : Γ ⊢[PRAAx] upper scalarZero (fstT r) E F) : Γ ⊢[PRAAx]
    upper (fstT m) (fstT (split l m r)) (C*F+E*D) (D*F) := by
  let P := rawDen l
  let Qr := rawDen m
  let S := rawDen r
  let X := re (rawGaussian l)
  let Y := re (rawGaussian m)
  let Z := re (rawGaussian r)
  let W := X*ZT.ofNat (Qr*S)+(Y*ZT.ofNat S+Z*ZT.ofNat Qr)*ZT.ofNat P
  have inner : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qadd m r)) (Y*ZT.ofNat S+Z*ZT.ofNat Qr) (Qr*S) := scalar_congr (RationalGaussianRealPart.real_add m r).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalRepresentations.represents_add (fstT m) (fstT r) Y Z Qr S (raw_represents m).andE₁ (raw_represents r).andE₁)
  have outer : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (split l m r)) W (P*(Qr*S)) := scalar_congr (RationalGaussianRealPart.real_add l (qadd m r)).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalRepresentations.represents_add (fstT l) (fstT (qadd m r)) X (Y*ZT.ofNat S+Z*ZT.ofNat Qr) P (Qr*S)
      (raw_represents l).andE₁ inner)
  have left := to_signed scalarZero (fstT l) (ZT.ofNat zero) X one P C D (scalar_zero_represents one) (raw_represents l).andE₁ hl
  have right := to_signed scalarZero (fstT r) (ZT.ofNat zero) Z one S E F (scalar_zero_represents one) (raw_represents r).andE₁ hr
  let Ll := RationalRepresentedUpper.left (ZT.ofNat zero) P D
  let Ul := RationalRepresentedUpper.right X one P C D
  let Lr := RationalRepresentedUpper.left (ZT.ofNat zero) S F
  let Ur := RationalRepresentedUpper.right Z one S E F
  have vl := zle_toZ left
  have vr := zle_toZ right
  apply from_signed (fstT m) (fstT (split l m r)) Y W Qr (P*(Qr*S)) (C*F+E*D) (D*F)
    (raw_den_positive m) (positive_product _ _ (raw_den_positive l) (positive_product _ _ (raw_den_positive m) (raw_den_positive r)))
    (raw_represents m).andE₁ outer
  apply zle_of_toZ (F*Qr*Qr*S*PolynomialBisection.slack Ll Ul+D*P*Qr*Qr*PolynomialBisection.slack Lr Ur)
  dsimp only [Ll,Ul,Lr,Ur,W,PolynomialBisection.slack,RationalRepresentedUpper.left,RationalRepresentedUpper.right] at vl vr ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_mul,map_mul,Q.mk_add,map_add] at vl vr ⊢
  ipra_simps
  linear_combination (𝔞 F*𝔞 Qr*𝔞 Qr*𝔞 S)*vl+(𝔞 D*𝔞 P*𝔞 Qr*𝔞 Qr)*vr

theorem original_middle_upper (w l m r A B C D E F : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hSplit : Γ ⊢[PRAAx] distanceBounded w (split l m r) A B)
    (hl : Γ ⊢[PRAAx] upper scalarZero (fstT l) C D)
    (hr : Γ ⊢[PRAAx] upper scalarZero (fstT r) E F) : Γ ⊢[PRAAx]
    upper (fstT m) (fstT w) (numerator A B C D E F) (denominator B D F) := by
  have near := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hB
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hB hSplit)
  exact upper_triangle _ _ _ _ _ _ _ (middle_split_upper l m r C D E F hl hr) (upper_of_radius _ _ _ _ near)

/-- The actual independent split error eps_p+3eps_q and two tail
lower envelopes cost exactly eps_p+5eps_q. -/
theorem original_dyadic_middle_upper (p q w l m r : PTm n)
    (hSplit : Γ ⊢[PRAAx] distanceBounded w (split l m r) (unit q+num 3*unit p) (unit p*unit q))
    (hl : Γ ⊢[PRAAx] upper scalarZero (fstT l) one (unit q))
    (hr : Γ ⊢[PRAAx] upper scalarZero (fstT r) one (unit q)) : Γ ⊢[PRAAx]
    upper (fstT m) (fstT w) (unit q+num 5*unit p) (unit p*unit q) := by
  have raw := original_middle_upper w l m r _ _ one (unit q) one (unit q)
    (positive_product _ _ (unit_positive p) (unit_positive q)) hSplit hl hr
  exact upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive q) (unit_positive q))
      (positive_product _ _ (unit_positive p) (unit_positive q))) raw
    (le_of_eq_add (d := zero) (by dsimp only [numerator,denominator]; ipra_ring))

theorem actual_original_three_piece_signed_monotonicity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((distanceBounded (var 2) (split (var 3) (var 4) (var 5)) (unit (var 1)+num 3*unit (var 0)) (unit (var 0)*unit (var 1)) ⋏
      (upper scalarZero (fstT (var 3)) one (unit (var 1)) ⋏ upper scalarZero (fstT (var 5)) one (unit (var 1)))) ⟶
      upper (fstT (var 4)) (fstT (var 2)) (unit (var 1)+num 5*unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (original_dyadic_middle_upper _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalThreeSumLower
