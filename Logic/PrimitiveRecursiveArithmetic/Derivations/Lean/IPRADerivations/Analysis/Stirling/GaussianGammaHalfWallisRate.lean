import IPRADerivations.Analysis.Stirling.WallisFinite
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayOrder
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaHalfRisingFactorial

/-!
# Finite Wallis rate for the squared half-argument Euler value

The comparison uses the existing arctangent quadrature grid verbatim.
For (Nge1), the squared Euler value (4N(2N)!!^2/(2N+1)!!^2)
differs from (4Q_M) by at most (4/N+2D_N/M).
Both denominator guards and both error inequalities are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfWallisRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open WallisFinite (da db Dm da_succ wallis_le_two finite_wallis J_zero_eq)
open WallisRecurrence (J)
open Products (fact)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def odd (N : PTm n) : PTm n := succ (two*N)
def pairOdd (N : PTm n) : PTm n := da N*da (succ N)
def evenSquare (N : PTm n) : PTm n := db N*db N
def squareNum (N : PTm n) : PTm n := num 4*N*evenSquare N
def squareDen (N : PTm n) : PTm n := odd N*pairOdd N
def wallisValue (N : PTm n) : PTm n := fraction (squareNum N) (squareDen N)
def piGrid (M L : PTm n) : PTm n := fraction (num 4*BaselQuadrature.Q M L) (fact L)
def arctanError (N M : PTm n) : PTm n := num 4*M+two*N*Dm N
def arctanDen (N M : PTm n) : PTm n := N*M
def gridSource (m L : PTm n) : Fm PTm n := le (two*(succ m*succ m)) L
def nativeGap (N M L : PTm n) : Fm PTm n :=
  le (arctanDen N M*(squareNum N*fact L))
    (arctanDen N M*(num 4*BaselQuadrature.Q M L*squareDen N)+arctanError N M*squareDen N*fact L) ⋏
  le (arctanDen N M*(num 4*BaselQuadrature.Q M L*squareDen N))
    (arctanDen N M*(squareNum N*fact L)+arctanError N M*squareDen N*fact L)

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem square_denominator (N : PTm n) : Γ ⊢[PRAAx] squareDen N ≐ da (succ N)*da (succ N) :=
  (by unfold squareDen pairOdd; ipra_ring : Γ ⊢[PRAAx] squareDen N ≐ (da N*odd N)*da (succ N)).eqTrans
    (congrMul (da_succ N).eqSymm (.eqRefl _))

theorem df_positive (N : PTm n) : Γ ⊢[PRAAx] le one (da N) :=
  le_congr (.eqRefl _) (LeanProofs.IPRA.Probability.NormalMoments.df_pos (Γ := Γ) N).eqSymm (zero_lt_succ _)

theorem square_denominator_positive (N : PTm n) : Γ ⊢[PRAAx] le one (squareDen N) :=
  le_congr (.eqRefl _) (square_denominator N).eqSymm
    (positive_product _ _ (df_positive (succ N)) (df_positive (succ N)))

theorem arctan_denominator_positive (r m : PTm n) :
    Γ ⊢[PRAAx] le one (arctanDen (succ r) (succ m)) :=
  positive_product _ _ (zero_lt_succ r) (zero_lt_succ m)

theorem finite_native_gap (r m L : PTm n) (hs : Γ ⊢[PRAAx] gridSource m L) :
    Γ ⊢[PRAAx] nativeGap (succ r) (succ m) L := by
  let N := succ r
  let M := succ m
  let A := odd N
  let B := pairOdd N
  let P := evenSquare N
  let F := fact L
  let T := BaselQuadrature.Q M L
  let D := Dm N
  have readJ : Γ ⊢[PRAAx] J zero M L ≐ two*M*T := J_zero_eq M L
  have hj := natEq readJ
  have lo0 : Γ ⊢[PRAAx] le (M*F*P) (B*(J zero M L+D*F)) := (finite_wallis hs r).andE₁
  have up0 : Γ ⊢[PRAAx] le (two*N*B*J zero M L) (A*P*(M*F)+two*N*B*(D*F)) :=
    (finite_wallis hs r).andE₂
  have pLe : Γ ⊢[PRAAx] le P (two*B) := wallis_le_two N
  refine .andI ?_ ?_
  · change Γ ⊢[PRAAx] le (N*M*(num 4*N*P*F)) (N*M*(num 4*T*(A*B))+(num 4*M+two*N*D)*(A*B)*F)
    ipra_le 2 * 𝔞 N * 𝔞 A * sl lo0 + 2 * 𝔞 N * 𝔞 (M*F*P) + 4 * 𝔞 (M*A*B*F) using
      rw [hj]
      dsimp only [A,odd]
      ipra_simps
      ring
  · change Γ ⊢[PRAAx] le (N*M*(num 4*T*(A*B))) (N*M*(num 4*N*P*F)+(num 4*M+two*N*D)*(A*B)*F)
    ipra_le 𝔞 A * sl up0 + (4 * 𝔞 N + 1) * 𝔞 (M*F) * sl pLe + 2 * 𝔞 (M*F*B) using
      rw [hj]
      dsimp only [A,odd]
      ipra_simps
      ring

theorem fraction_distance (a b c d A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hD : Γ ⊢[PRAAx] le one D)
    (left : Γ ⊢[PRAAx] le (D*(a*d)) (D*(c*b)+A*b*d))
    (right : Γ ⊢[PRAAx] le (D*(c*b)) (D*(a*d)+A*d*b)) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D := by
  let x := RationalCubeMidpoint.fraction a b
  let y := RationalCubeMidpoint.fraction c d
  have hupper (u v x₀ y₀ : PTm n) (hv : Γ ⊢[PRAAx] le one v) (hy : Γ ⊢[PRAAx] le one y₀)
      (h : Γ ⊢[PRAAx] le (D*(u*y₀)) (D*(x₀*v)+A*v*y₀)) :
      Γ ⊢[PRAAx] RationalValueBounds.upper (RationalCubeMidpoint.fraction u v)
        (RationalCubeMidpoint.fraction x₀ y₀) A D := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat u) (ZT.ofNat x₀) v y₀ A D hv hy
      (RationalCubeMidpoint.fraction_represents u v hv) (RationalCubeMidpoint.fraction_represents x₀ y₀ hy)
    let s := monus (D*(x₀*v)+A*v*y₀) (D*(u*y₀))
    have e := natEq (eq_add_of_le h)
    apply zle_of_toZ s
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    unfold s
    linear_combination -e
  have raw := RationalGaussianNameEmbedding.distance_from_radius x y A D hD
    (RationalValueBounds.radius_of_upper x y A D (hupper a b c d hb hd left) (hupper c d a b hd hb right))
  exact distance_congr (GaussianEulerDecayOrder.fraction_embedding _ _ hb)
    (GaussianEulerDecayOrder.fraction_embedding _ _ hd) (.eqRefl _) (.eqRefl _) raw

theorem finite_rate (r m L : PTm n) (hs : Γ ⊢[PRAAx] gridSource m L) :
    Γ ⊢[PRAAx] distanceBounded (wallisValue (succ r)) (piGrid (succ m) L)
      (arctanError (succ r) (succ m)) (arctanDen (succ r) (succ m)) := by
  let N := succ r
  let M := succ m
  let F := fact L
  let A := arctanError N M
  let D := arctanDen N M
  have gaps := finite_native_gap r m L hs
  exact fraction_distance _ _ _ _ A D (square_denominator_positive N) (GaussianGammaHalfRisingFactorial.factorial_positive L)
    (arctan_denominator_positive r m) gaps.andE₁
    (le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx]
      D*(squareNum N*F)+A*squareDen N*F ≐ D*(squareNum N*F)+A*F*squareDen N) gaps.andE₂)

theorem actual_half_Wallis_arctangent_finite_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (gridSource (var 1) (var 2) ⟶ distanceBounded (wallisValue (succ (var 0))) (piGrid (succ (var 1)) (var 2))
        (arctanError (succ (var 0)) (succ (var 1))) (arctanDen (succ (var 0)) (succ (var 1)))) :=
  closeUniv 3 (.impI (finite_rate _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfWallisRate
