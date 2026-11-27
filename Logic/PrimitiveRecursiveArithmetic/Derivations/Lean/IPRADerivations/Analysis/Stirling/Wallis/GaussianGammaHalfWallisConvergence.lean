import IPRADerivations.Analysis.Gamma.HalfInteger.SquareRoots.GaussianGammaHalfPiName
import IPRADerivations.Analysis.Gamma.HalfInteger.SquareRoots.GaussianGammaHalfSqrtBrackets
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# One-sided convergence of the actual finite Wallis product

The ratio of the literal double factorials is W_N. The finite quadrature
squeeze and a cofinal mesh give the exact inequalities
2 W_N <= π <= 2 W_N + 2/N for N >= 1, with only the requested π
observation tolerance. In particular the stated 2/N bound for π/2-W_N
holds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfWallisConvergence

open_ipra
open GaussianGammaHalfWallisRate (evenSquare pairOdd piGrid gridSource odd df_positive)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianGammaHalfPiName (nameF unit_mono orderAt meshAt meshIndex clearing Dm_mono)
open GaussianRationalHorner (positive_product)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianNameEquivalence (point_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_mono upper_congr upper_of_radius upper_triangle)
open WallisFinite (Dm finite_wallis J_zero_eq wallis_le_two)
open WallisRecurrence (J)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def twiceWallis (N : PTm n) : PTm n := fraction (two*evenSquare N) (pairOdd N)
def lowerSlack (N : PTm n) : PTm n := two*Dm N
def upperNumerator (N p : PTm n) : PTm n := two*unit p+N
def upperDenominator (N p : PTm n) : PTm n := N*unit p

def enclosure (r p x : PTm n) : Fm PTm n :=
  let N := succ r
  let a := fstT (twiceWallis N)
  let b := fstT (ap2 nameF p x)
  upper a b one (unit p) ⋏ upper b a (upperNumerator N p) (upperDenominator N p)

private theorem denom_pos (N : PTm n) : Γ ⊢[PRAAx] le one (pairOdd N) :=
  positive_product _ _ (df_positive N) (df_positive (succ N))

private theorem fraction_upper (a b c d A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le (D*(a*d)) (D*(c*b)+A*b*d)) :
    Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT (fraction c d)) A D := by
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat a) (ZT.ofNat c) b d A D hb hd
    (fraction_first_represents a b hb) (fraction_first_represents c d hd)
  have e := natEq (eq_add_of_le h)
  apply zle_of_toZ (monus (D*(c*b)+A*b*d) (D*(a*d)))
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -e

theorem finite_enclosure (r m L : PTm n) (h : Γ ⊢[PRAAx] gridSource m L) : Γ ⊢[PRAAx]
    upper (fstT (twiceWallis (succ r))) (fstT (piGrid (succ m) L)) (lowerSlack (succ r)) (succ m) ⋏
    upper (fstT (piGrid (succ m) L)) (fstT (twiceWallis (succ r)))
      (two*succ m+succ r*lowerSlack (succ r)) (succ r*succ m) := by
  let N := succ r
  let M := succ m
  let B := pairOdd N
  let P := evenSquare N
  let F := fact L
  let K := BaselQuadrature.Q M L
  let D := Dm N
  have hB : Γ ⊢[PRAAx] le one B := denom_pos N
  have hF : Γ ⊢[PRAAx] le one F := GaussianGammaHalfRisingFactorial.factorial_positive L
  have lo : Γ ⊢[PRAAx] le (M*F*P) (B*(J zero M L+D*F)) := (finite_wallis h r).andE₁
  have hi : Γ ⊢[PRAAx] le (two*N*B*J zero M L) (odd N*P*(M*F)+two*N*B*(D*F)) := (finite_wallis h r).andE₂
  have readJ : Γ ⊢[PRAAx] J zero M L ≐ two*M*K := J_zero_eq M L
  have ej := natEq readJ
  have bounds : Γ ⊢[PRAAx] le P (two*B) := wallis_le_two N
  refine .andI (fraction_upper (two*P) B (num 4*K) F _ _ hB hF ?_)
    (fraction_upper (num 4*K) F (two*P) B _ _ hF hB ?_)
  · change Γ ⊢[PRAAx] le (M*(two*P*F)) (M*(num 4*K*B)+two*D*B*F)
    ipra_le 2*sl lo using
      rw [ej]
      try ipra_simps
      ring
  · change Γ ⊢[PRAAx] le (N*M*(num 4*K*B)) (N*M*(two*P*F)+(two*M+N*(two*D))*F*B)
    ipra_le sl hi+𝔞 (M*F)*sl bounds using
      rw [ej]
      unfold odd
      try ipra_simps
      ring

private theorem grid_later (s N : PTm n) :
    Γ ⊢[PRAAx] le (lowerSlack N*unit s) (meshAt (s+N)) := by
  let t := s+N
  let U := unit t
  let D := Dm (orderAt t)
  have later : Γ ⊢[PRAAx] le (unit s) U := unit_mono _ _ (le_add_right s N)
  have large : Γ ⊢[PRAAx] le U (orderAt t) := by
    unfold orderAt GaussianGammaHalfPiName.orderIndex
    ipra_le 15*𝔞 U+1
  have nlarge : Γ ⊢[PRAAx] le N (orderAt t) :=
    le_trans (le_add_left N s) (le_trans (LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract.le_pow_self t) large)
  have dlarge : Γ ⊢[PRAAx] le (Dm N) D := Dm_mono _ _ nlarge
  have bound : Γ ⊢[PRAAx] le (Dm N*unit s) (D*U) :=
    LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono dlarge later
  change Γ ⊢[PRAAx] le (two*Dm N*unit s) (succ (num 8*D*U))
  ipra_le 2*sl bound+6*𝔞 D*𝔞 U+1

theorem late_enclosure (r p s x : PTm n) : Γ ⊢[PRAAx]
    upperSlack (fstT (twiceWallis (succ r))) (fstT (ap2 nameF p x)) one (unit p) two s ⋏
    upperSlack (fstT (ap2 nameF p x)) (fstT (twiceWallis (succ r)))
      (upperNumerator (succ r) p) (upperDenominator (succ r) p) two s := by
  let N := succ r
  let t := s+N
  let M := meshAt t
  let W := unit p
  let U := unit s
  let T := unit t
  let C := lowerSlack N
  let A := fstT (twiceWallis N)
  let B := fstT (ap2 nameF p x)
  let P := fstT (ap2 nameF t x)
  let F := clearing t
  have hW : Γ ⊢[PRAAx] le one W := unit_positive p
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have hT : Γ ⊢[PRAAx] le one T := unit_positive t
  have hN : Γ ⊢[PRAAx] le one N := zero_lt_succ r
  have hM : Γ ⊢[PRAAx] le one M := zero_lt_succ (meshIndex t)
  have hNU : Γ ⊢[PRAAx] le one (N*U) := positive_product _ _ hN hU
  have hNM : Γ ⊢[PRAAx] le one (N*M) := positive_product _ _ hN hM
  have hWU := positive_product (Γ := Γ) _ _ hW hU
  have hWT := positive_product (Γ := Γ) _ _ hW hT
  have later : Γ ⊢[PRAAx] le U T := unit_mono _ _ (le_add_right s N)
  have gm : Γ ⊢[PRAAx] le (C*U) M := grid_later s N
  have old := finite_enclosure (Γ := Γ) r (meshIndex t) F (le_refl _)
  have read : Γ ⊢[PRAAx] P ≐ fstT (piGrid M F) := congrFst (GaussianGammaHalfPiName.sample_at t x)
  have first : Γ ⊢[PRAAx] upper A P one U :=
    RationalValueBounds.upper_mono_one hM gm (upper_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl _) old.andE₁)
  have lastRaw : Γ ⊢[PRAAx] upper P A (two*M+N*C) (N*M) :=
    upper_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) old.andE₂
  have last : Γ ⊢[PRAAx] upper P A (two*U+N) (N*U) :=
    upper_mono P A (two*M+N*C) (N*M) (two*U+N) (N*U) hNM lastRaw
      (by ipra_le 𝔞 N^2*sl gm)
  have diff : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (ap2 nameF p x) (ap2 nameF t x) (W+T) (W*T) :=
    point_at nameF x p t (GaussianGammaHalfPiName.name_regular x)
  have radial := scalar_coordinate_distance _ _ _ _ hWT diff
  have fwd : Γ ⊢[PRAAx] upper B P (W+U) (W*U) :=
    RationalValueBounds.upper_two_errors_retime hWT (le_refl W) later (upper_of_radius _ _ _ _ radial)
  have rev : Γ ⊢[PRAAx] upper P B (W+U) (W*U) :=
    RationalValueBounds.upper_two_errors_retime hWT (le_refl W) later
      (upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ radial))
  change Γ ⊢[PRAAx] upper A B (one*U+two*W) (W*U) ⋏ upper B A ((two*W+N)*U+two*(N*W)) ((N*W)*U)
  refine .andI ?_ ?_
  · exact upper_mono _ _ _ _ _ _ (positive_product _ _ hU hWU)
      (upper_triangle _ _ _ _ _ _ _ first rev) (by ipra_le 0)
  · have joined : Γ ⊢[PRAAx] upper B A ((W+U)*(N*U)+(two*U+N)*(W*U)) ((W*U)*(N*U)) :=
      upper_triangle _ _ _ _ _ _ _ fwd last
    apply upper_mono B A ((W+U)*(N*U)+(two*U+N)*(W*U)) ((W*U)*(N*U)) _ _
      (positive_product _ _ hWU hNU) joined
    ipra_le 0

theorem original_Wallis_rate (r p x : PTm n) : Γ ⊢[PRAAx] enclosure r p x := by
  let N := succ r
  let A := fstT (twiceWallis N)
  let B := fstT (ap2 nameF p x)
  exact .andI
    (remove_upper_slack A B one (unit p) two
      (late_enclosure r p (precision A B (unit p) two) x).andE₁)
    (remove_upper_slack B A (upperNumerator N p) (upperDenominator N p) two
      (late_enclosure r p (precision B A (upperDenominator N p) two) x).andE₂)

theorem actual_Wallis_pi_one_sided_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (enclosure (var 0) (var 1) (var 2)) :=
  closeUniv 3 (original_Wallis_rate _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaHalfWallisConvergence
