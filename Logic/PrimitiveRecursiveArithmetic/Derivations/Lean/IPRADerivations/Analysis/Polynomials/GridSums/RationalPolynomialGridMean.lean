import IPRADerivations.Analysis.Polynomials.GridSums.RationalPolynomialGridMeanError

/-!
# A quantitative mean for literal signed polynomial samples

The normalized left grid sum has error at most the sum of absolute
polynomial coefficients divided by the mesh denominator. The exact
target uses a factorial common denominator for the monomial moments.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.RationalPolynomialGridMean

open_ipra
open BernoulliBounds (zint toZ_zint)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalArithmetic (multiply multiply_guard)
open RationalFiniteSum (sum canonical_equal)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalPolynomialGridMeanError (meanNumerator radius cleared_error)
open RationalPolynomialGridSum (body rowDen prefixNumerator fold_eq)
open RationalRepresentedUpper (from_signed)
open RationalValueBounds (upper)

variable {n d : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" x:max => Groth.ι (Q.mk Γ x)

def average (a : Fin (d+1) → ℤ) (D : ℕ) (M : PTm n) : PTm n :=
  multiply (fraction one M) (sum (body a D) M M)

def mean (a : Fin (d+1) → ℤ) (D : ℕ) : PTm n :=
  normalize (zint (meanNumerator a)) (num D*num (d+1).factorial)

private theorem power_at_succ (M : PTm n) :
    Γ ⊢[PRAAx] pw M (num (d+1)) ≐ pw M (num d)*M := by
  have e : Γ ⊢[PRAAx] (num (d+1) : PTm n) ≐ succ (num d) := by
    apply deriveNat
    simp [Q.mk_num, Q.mk_succ, Nat.cast_succ]
  exact (congrAp2 powF e (.eqRefl M)).eqTrans (pw_succ M (num d))

private theorem average_eq (a : Fin (d+1) → ℤ) (D : ℕ) (hD : 0 < D) (M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] average a D M ≐ normalize (prefixNumerator a M M) (rowDen (d+1) D M) := by
  let E := rowDen d D M
  let E' := rowDen (d+1) D M
  let N := prefixNumerator a M M
  have hE := RationalPolynomialGridSum.denominator_positive d D hD M hM
  have hE' := RationalPolynomialGridSum.denominator_positive (d+1) D hD M hM
  have eq := fold_eq a D hD M M hM
  change Γ ⊢[PRAAx] sum (body a D) M M ≐ normalize N E at eq
  refine (RationalAlgebra.multiply_congr (.eqRefl (fraction one M)) eq).eqTrans ?_
  apply canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (normalize_well_formed _ _ hE')
    (RationalRepresentations.represents_multiply _ _ _ _ _ _
      (fraction_represents one M hM) (normalize_preserves_value N E hE))
    (normalize_preserves_value N E' hE') (positive_product _ _ hM hE) hE'
  apply ZT.derive
  have hp := natEq (power_at_succ (Γ := Γ) (d := d) M)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul,E,E',rowDen,hp,Q.mk_one,map_one]
  ring

theorem average_error (a : Fin (d+1) → ℤ) (D : ℕ) (hD : 0 < D) (M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] upper (average a D M) (mean a D) (num (radius a)) (num D*M) ⋏
      upper (mean a D) (average a D M) (num (radius a)) (num D*M) := by
  let T : PTm n := num D
  let E := rowDen (d+1) D M
  let F := T*num (d+1).factorial
  let B := T*M
  let A : PTm n := num (radius a)
  let x := prefixNumerator a M M
  let y : ZT n := zint (meanNumerator a)
  have hE := RationalPolynomialGridSum.denominator_positive (d+1) D hD M hM
  have hT : Γ ⊢[PRAAx] le one T := Foundations.NumeralPrimes.num_le hD
  have hF : Γ ⊢[PRAAx] le one F := positive_product _ _ hT
    (Foundations.NumeralPrimes.num_le (Nat.factorial_pos (d+1)))
  have vx : Γ ⊢[PRAAx] RationalArithmetic.represents (average a D M) x E := by
    let c := average a D M
    let c' := normalize x E
    let N : PTm n → ZT n := RationalSupMetric.numeratorOf
    let K : PTm n → PTm n := RationalSupMetric.denominatorOf
    have e : Γ ⊢[PRAAx] c ≐ c' := average_eq a D hD M hM
    have p : 𝔞(fstT (fstT c)) = 𝔞(fstT (fstT c')) := natEq (congrFst (congrFst e))
    have q : 𝔞(sndT (fstT c)) = 𝔞(sndT (fstT c')) := natEq (congrSnd (congrFst e))
    have value : ZT.toZ Γ (N c) = ZT.toZ Γ (N c') := by
      change 𝔞(fstT (fstT c)) - 𝔞(sndT (fstT c)) = 𝔞(fstT (fstT c')) - 𝔞(sndT (fstT c'))
      rw [p,q]
    have den : 𝔞(K c) = 𝔞(K c') := natEq (congrSucc (congrSnd e))
    apply ZT.derive
    change ZT.toZ Γ (x*ZT.ofNat (K c)) = ZT.toZ Γ (N c*ZT.ofNat E)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,value,den]
    simpa only [ZT.toZ_mul,ZT.toZ_ofNat] using ZT.toZ_eq (normalize_preserves_value x E hE)
  have vy : Γ ⊢[PRAAx] RationalArithmetic.represents (mean a D) y F :=
    normalize_preserves_value y F hF
  have hp := natEq (power_at_succ (Γ := Γ) (d := d) M)
  have h := cleared_error (Γ := Γ) a M
  have hl := zsl_def h.1
  have hr := zsl_def h.2
  have hc := nn_term (Γ := Γ) (T*T*M)
  refine .andI (from_signed _ _ x y E F A B hE hF vx vy ?_)
    (from_signed _ _ y x F E A B hF hE vy vx ?_)
  · refine zle_of_comb _ ?_ (nn_mul hc (nn_zsl h.2))
    simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,hr,
      ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_mul,map_mul,toZ_zint,E,F,B,A,x,y,rowDen,hp]
    ring
  · refine zle_of_comb _ ?_ (nn_mul hc (nn_zsl h.1))
    simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,hl,
      ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_mul,map_mul,toZ_zint,E,F,B,A,x,y,rowDen,hp]
    ring

theorem actual_rational_polynomial_grid_mean_error_closed (a : Fin (d+1) → ℤ) (D : ℕ) (hD : 0 < D) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le one (var 0) ⟶ upper (average a D (var 0)) (mean a D) (num (radius a)) (num D*var 0) ⋏
        upper (mean a D) (average a D (var 0)) (num (radius a)) (num D*var 0)) :=
  closeUniv 1 (.impI (average_error a D hD _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPolynomialGridMean
