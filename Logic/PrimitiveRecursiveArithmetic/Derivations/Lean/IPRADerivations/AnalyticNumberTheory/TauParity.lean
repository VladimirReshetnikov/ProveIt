import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.AnalyticNumberTheory.DivisorHyperbola
import IPRADerivations.AnalyticNumberTheory.MertensTotient

/-!
# The parity of the divisor function

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem
`el:squareparity`, the assertion "`τ(n)` is odd `⟺` `n` is a square".

The packet pairs the exponents of the factorization. Here the parity is read off the Dirichlet hyperbola
identity `D(x) + m² = 2 ∑_{d ≤ m} ⌊x/d⌋`, `m = ⌊√x⌋` (`DivisorHyperbola.hyperbola`), for the summatory function
`D(x) = ∑_{n ≤ x} τ(n)`: it gives `D(x) ≡ m² ≡ ⌊√x⌋ (mod 2)`, hence

    τ(x + 1) = D(x + 1) − D(x) ≡ ⌊√(x + 1)⌋ − ⌊√x⌋ = [(⌊√x⌋ + 1)² = x + 1]   (mod 2).

* `tau`, `T`: `τ = 𝟏 * 𝟏` and `T(x) = ∑_{m ≤ x} τ(m)`; `T_succ`;
* `T_eq_S`: `T(x) = ∑_{d=1}^{x} ⌊x/d⌋` (`MertensTotient.floor_summatory` at the weight `𝟏`);
* `par_sq`, `par_T`: `par (s²) = par s` and `par T(x) = par ⌊√x⌋`;
* **`tau_parity`**: `par τ(x + 1) = [(⌊√x⌋ + 1)² = x + 1]`;
* `square_of_bit`, `bit_of_square`: the bit is `1` exactly when `x + 1` is a square;
* **`tau_odd_of_square`**, **`square_of_tau_odd`**: `k² = x + 1` gives `τ(x + 1)` odd, and `τ(x + 1)` odd gives
  `(⌊√x⌋ + 1)² = x + 1`.

The squarefree decomposition and the parity of `σ` in `el:squareparity` are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.TauParity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (hyperbola)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (conv)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB)
open LeanProofs.IPRA.AnalyticNumberTheory.MertensTotient (floor_summatory floor_term)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor (inst2_oneB)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The divisor function and its summatory function -/

/-- `τ(m) = (𝟏 * 𝟏)(m)`, the number of divisors of `m ≥ 1` (and `0` at `m = 0`). -/
abbrev tau (m : PTm n) : PTm n := conv one one m zero

/-- `T(x) = ∑_{m ≤ x} τ(m)`. -/
abbrev T (x : PTm n) : PTm n := ap2 (sumF (cvF one one)) (succ x) zero

theorem T_succ (x : PTm n) : Γ ⊢[PRAAx] T (succ x) ≐ T x + tau (succ x) := by
  have h := sum_succ' (Γ := Γ) (cvF one one) (succ x) zero
  rw [inst2_cvF] at h
  exact h

theorem one_alg (X : PTm n) : Γ ⊢[PRAAx] ((one : PTm n) * one) * X ≐ X := by
  apply deriveNat; ipra_simps; ring

/-- `T(x) = ∑_{d=1}^{x} ⌊x/d⌋`. -/
theorem T_eq_S (x : PTm n) : Γ ⊢[PRAAx] T x ≐ S x x := by
  have a := floor_summatory (Γ := Γ) one x zero
  have b := sum_shift (Γ := Γ) (RB one one) x (pairT x zero)
  have t0 : Γ ⊢[PRAAx] inst2 (RB one one) zero (pairT x zero) ≐ zero :=
    (floor_term one zero x zero).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)
  have c : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (RB one one))) x (pairT x zero) ≐ ap2 (sumF hB) x x := by
    refine sum_congr_bounded (shiftBody (RB one one)) hB (pairT x zero) x x (.allI (.impI ?_))
    rw [shift_pairT, inst2_shiftBody, inst2_h]
    refine (floor_term one _ _ _).eqTrans ?_
    rw [inst2_oneB]
    exact (congrMul (congrMul (sg_succ _) (.eqRefl _)) (.eqRefl _)).eqTrans (one_alg _)
  exact a.eqTrans (b.eqTrans ((congrAdd t0 c).eqTrans (zero_add _)))

/-! ## Parities -/

theorem sq_even {s h : PTm n} (e : Γ ⊢[PRAAx] s ≐ two * h) : Γ ⊢[PRAAx] s * s ≐ two * (h * s) := by
  have x := natEq e
  apply deriveNat; ipra_simps; linear_combination 𝔞 s * x

theorem sq_odd {s h : PTm n} (e : Γ ⊢[PRAAx] s ≐ two * h + one) :
    Γ ⊢[PRAAx] s * s ≐ two * (h * s + h) + one := by
  have x := natEq e
  apply deriveNat; ipra_simps; linear_combination (𝔞 s + 1) * x

/-- `par (s²) = par s`. -/
theorem par_sq (s : PTm n) : Γ ⊢[PRAAx] par (s * s) ≐ par s := by
  refine .orE (even_or_odd s) ?_ ?_
  · have e : ((s ≐ two * half s) :: Γ) ⊢[PRAAx] s ≐ two * half s := Prf.hyp0
    exact ((congrAp1 parF (sq_even e)).eqTrans (par_double _)).eqTrans
      ((congrAp1 parF e).eqTrans (par_double _)).eqSymm
  · have e : ((s ≐ two * half s + one) :: Γ) ⊢[PRAAx] s ≐ two * half s + one := Prf.hyp0
    exact ((congrAp1 parF (sq_odd e)).eqTrans (par_double_succ _)).eqTrans
      ((congrAp1 parF e).eqTrans (par_double_succ _)).eqSymm

theorem sq_succ (s : PTm n) : Γ ⊢[PRAAx] (s + one) * (s + one) ≐ succ s * succ s := by
  apply deriveNat; ipra_simps; ring

/-- `par T(x) = par ⌊√x⌋`. -/
theorem par_T (x : PTm n) : Γ ⊢[PRAAx] par (T x) ≐ par (isqrt x) := by
  have h := hyperbola (Γ := Γ) (isqrt_le x) (lt_congr (.eqRefl _) (sq_succ _) (lt_isqrt_succ_sq x))
  have z : Γ ⊢[PRAAx] par (S x x + isqrt x * isqrt x) ≐ zero := (congrAp1 parF h).eqTrans (par_double _)
  exact (congrAp1 parF (T_eq_S x)).eqTrans ((par_eq_of_add_even z).eqTrans (par_sq _))

theorem par_one : Γ ⊢[PRAAx] par (one : PTm n) ≐ one :=
  (par_succ zero).eqTrans ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero one))

/-- The parity of a bit is the bit. -/
theorem bit_par {e : PTm n} (h : Γ ⊢[PRAAx] (e ≐ zero) ⋎ (e ≐ one)) : Γ ⊢[PRAAx] par e ≐ e := by
  refine .orE h ?_ ?_
  · exact ((congrAp1 parF Prf.hyp0).eqTrans par_zero).eqTrans Prf.hyp0.eqSymm
  · exact ((congrAp1 parF Prf.hyp0).eqTrans par_one).eqTrans Prf.hyp0.eqSymm

theorem tau_alg {Ts Tx t : PTm n} (h : Γ ⊢[PRAAx] Ts ≐ Tx + t) : Γ ⊢[PRAAx] t + two * Tx ≐ Ts + Tx := by
  have x := natEq h
  apply deriveNat; ipra_simps; linear_combination -x

theorem s_alg {s' s e : PTm n} (h : Γ ⊢[PRAAx] s' ≐ s + e) : Γ ⊢[PRAAx] s' + s ≐ e + two * s := by
  have x := natEq h
  apply deriveNat; ipra_simps; linear_combination x

/-- **The parity of `τ`**: `par τ(x + 1) = [(⌊√x⌋ + 1)² = x + 1]`. -/
theorem tau_parity (x : PTm n) :
    Γ ⊢[PRAAx] par (tau (succ x)) ≐ eqb ((isqrt x + one) * (isqrt x + one)) (succ x) := by
  have a : Γ ⊢[PRAAx] par (tau (succ x)) ≐ par (T (succ x) + T x) :=
    (par_add_two _ _).eqSymm.eqTrans (congrAp1 parF (tau_alg (T_succ x)))
  have b : Γ ⊢[PRAAx] par (T (succ x) + T x) ≐ par (isqrt (succ x) + isqrt x) :=
    (par_add _ _).eqTrans ((congrAp1 parF (congrAdd (par_T _) (par_T _))).eqTrans (par_add _ _).eqSymm)
  have c : Γ ⊢[PRAAx] par (isqrt (succ x) + isqrt x) ≐
      par (eqb ((isqrt x + one) * (isqrt x + one)) (succ x)) :=
    (congrAp1 parF (s_alg (isqrt_succ x))).eqTrans (par_add_two _ _)
  exact a.eqTrans (b.eqTrans (c.eqTrans (bit_par (eqb_cases _ _))))

/-! ## The bit detects squares -/

/-- The bit `1` gives the square root `⌊√x⌋ + 1` of `x + 1`. -/
theorem square_of_bit {x : PTm n}
    (h : Γ ⊢[PRAAx] eqb ((isqrt x + one) * (isqrt x + one)) (succ x) ≐ one) :
    Γ ⊢[PRAAx] (isqrt x + one) * (isqrt x + one) ≐ succ x := eq_of_eqb h

theorem up_alg {k x : PTm n} (h : Γ ⊢[PRAAx] k * k ≐ succ x) :
    Γ ⊢[PRAAx] (k + one) * (k + one) ≐ succ (succ x) + two * k := by
  have a := natEq h
  apply deriveNat; ipra_simps; linear_combination a

/-- A square `x + 1 = k²` makes the bit `1`. -/
theorem bit_of_square {k x : PTm n} (h : Γ ⊢[PRAAx] k * k ≐ succ x) :
    Γ ⊢[PRAAx] eqb ((isqrt x + one) * (isqrt x + one)) (succ x) ≐ one := by
  refine .orE (eqb_cases ((isqrt x + one) * (isqrt x + one)) (succ x)) ?_ Prf.hyp0
  let C : List (Fm PTm n) := (eqb ((isqrt x + one) * (isqrt x + one)) (succ x) ≐ zero) :: Γ
  have e0 : C ⊢[PRAAx] eqb ((isqrt x + one) * (isqrt x + one)) (succ x) ≐ zero := Prf.hyp0
  have s1 : C ⊢[PRAAx] isqrt (succ x) ≐ isqrt x :=
    (isqrt_succ x).eqTrans ((congrAdd (.eqRefl _) e0).eqTrans (add_zero _))
  have sk : C ⊢[PRAAx] isqrt (succ x) ≐ k :=
    isqrt_unique (le_congr h.wk.eqSymm (.eqRefl _) (le_refl (succ x))) (le_of_eq_add (up_alg h.wk))
  have kq : C ⊢[PRAAx] k ≐ isqrt x := sk.eqSymm.eqTrans s1
  have l : C ⊢[PRAAx] le (succ x) x :=
    le_congr ((congrMul kq kq).eqSymm.eqTrans h.wk) (.eqRefl _) (isqrt_le x)
  exact lt_irrefl x _ l

/-- **A square has an odd number of divisors**. -/
theorem tau_odd_of_square {k x : PTm n} (h : Γ ⊢[PRAAx] k * k ≐ succ x) :
    Γ ⊢[PRAAx] par (tau (succ x)) ≐ one := (tau_parity x).eqTrans (bit_of_square h)

/-- **An odd number of divisors gives a square**: `(⌊√x⌋ + 1)² = x + 1`. -/
theorem square_of_tau_odd {x : PTm n} (h : Γ ⊢[PRAAx] par (tau (succ x)) ≐ one) :
    Γ ⊢[PRAAx] (isqrt x + one) * (isqrt x + one) ≐ succ x :=
  square_of_bit ((tau_parity x).eqSymm.eqTrans h)

end LeanProofs.IPRA.AnalyticNumberTheory.TauParity
