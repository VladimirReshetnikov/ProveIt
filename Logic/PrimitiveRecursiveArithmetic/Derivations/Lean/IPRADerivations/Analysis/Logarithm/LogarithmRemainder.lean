import IPRADerivations.Core.MultiSums
import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.Products
import IPRADerivations.Core.LinearCombination

/-!
# A finite Taylor-logarithm remainder bound

Packet `analysis/barnes_g_ipra_2026-11-16`, `eq:qseries` and `eq:qbound`.
For `2R ≤ N`, the positive finite Taylor tail

`F_L = ∑_{j<L} R^(j+3) / ((j+3) N^(j+3))`

is at most `2 R³ / (3 N³)`. Its exact common denominator is
`D_L = (L+2)! N^(L+2)`. The primitive-recursive Horner numerator is
`P_0 = 0`, `P_(L+1) = (L+3) N P_L + (L+2)! R^(L+3)`.
Thus the two defining recurrences implement ordinary exact addition of the
displayed rational summands; no rounding or assumed series estimate occurs.

The object-language proof retains the geometric remainder:
`3 N³ P_L + 2 (L+2)! N² R^(L+3) ≤ 2 R³ D_L`.
All three parameters are internal, and zero values are permitted in these
denominator-cleared statements. A rational interpretation requires `N ≥ 1`.
Multiplying the finite Taylor tail by `N` gives the finite version of
`eq:qbound`. Connecting these finite polynomials to an actual logarithm
still requires a certified logarithm name and a limit bridge.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.LogarithmRemainder

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

abbrev three : PTm n := num 3

/-- Variables `0 = L`, `1 = P_L`, `2 = ⟨R,N⟩`. -/
def numeratorStep : PTm 3 :=
  (var 0 + three) * sndT (var 2) * var 1 +
    fact (var 0 + two) * pw (fstT (var 2)) (var 0 + three)

def numeratorF : PR 2 := rec2 zero numeratorStep

/-- The exact positive Taylor-tail numerator, degrees `3` through `L+2`. -/
def numerator (R N L : PTm n) : PTm n := ap2 numeratorF L (pairT R N)

/-- A common denominator for every summand of the finite Taylor tail. -/
def denominator (N L : PTm n) : PTm n := fact (L + two) * pw N (L + two)

ipra_subst numerator

ipra_subst denominator [fact]

theorem numerator_zero (R N : PTm n) : Γ ⊢[PRAAx] numerator R N zero ≐ zero :=
  by simpa [numerator, numeratorF] using rec2_zero (Γ := Γ) zero numeratorStep (pairT R N)

theorem numerator_succ (R N L : PTm n) :
    Γ ⊢[PRAAx] numerator R N (succ L) ≐
      (L + three) * N * numerator R N L + fact (L + two) * pw R (L + three) := by
  have h := rec2_succ (Γ := Γ) zero numeratorStep L (pairT R N)
  simp only [numeratorStep, PTm.subst_add, PTm.subst_mul, subst_sndT, subst_fstT,
    subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, PTm.subst_num, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  refine h.eqTrans ?_
  exact congrAdd
    (congrMul (congrMul (.eqRefl _) (snd_pair R N)) (.eqRefl _))
    (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) (fst_pair R N)))

theorem denominator_succ (N L : PTm n) :
    Γ ⊢[PRAAx] denominator N (succ L) ≐ (L + three) * N * denominator N L := by
  have e : Γ ⊢[PRAAx] succ L + two ≐ succ (L + two) := by ipra_ring
  unfold denominator
  ipra_lc 𝔞(pw N (succ L + two)) * natEq ((congrAp2 factF e (.eqRefl zero)).eqTrans (fact_succ (L + two) zero)) +
    𝔞(fact (L + two)) * (𝔞(L) + 3) * natEq ((congrAp2 powF e (.eqRefl N)).eqTrans (pw_succ N (L + two)))

theorem denominator_zero (N : PTm n) :
    Γ ⊢[PRAAx] denominator N zero ≐ two * N * N := by
  have f₀ := fact_zero (Γ := Γ) (zero : PTm n)
  have f₁ : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul f₀ (.eqRefl _)).eqTrans (one_mul _))
  have f := natEq ((congrAp2 (Γ := Γ) factF (zero_add two) (.eqRefl zero)).eqTrans
    ((fact_succ one zero).eqTrans ((congrMul f₁ (.eqRefl _)).eqTrans (one_mul _))))
  have p := natEq ((congrAp2 (Γ := Γ) powF (zero_add two) (.eqRefl N)).eqTrans
    ((pw_succ N one).eqTrans (congrMul (pw_one N) (.eqRefl _))))
  unfold denominator
  ipra_lc 𝔞(pw N (zero + two)) * f + 2 * p

/-- The common denominator is positive whenever the input divisor is positive. -/
theorem denominator_positive (N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (denominator N L) := by
  have all : Γ ⊢[PRAAx] .all (le one (denominator (Syn.shift N) (var 0))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_denominator]
    · have d := natEq (denominator_zero (Γ := Γ) N)
      refine le_of_eq_add (d := N * N + monus N one * (N + one)) ?_
      ipra_lc d + (𝔞(N) + 1) * natEq (eq_add_of_le hN)
    · have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using hN.shift
      have i := natEq (eq_add_of_le (Prf.hyp0 :
        (le one (denominator (Syn.shift N) (var 0))) :: Γ.map Fm.shift ⊢[PRAAx] _))
      have h := natEq (eq_add_of_le
        (positive.wk (ψ := le one (denominator (Syn.shift N) (var 0)))))
      have d := natEq (denominator_succ
        (Γ := (le one (denominator (Syn.shift N) (var 0))) :: Γ.map Fm.shift)
        (Syn.shift N) (var 0))
      refine le_of_eq_add (d :=
        (var 0 + two) * Syn.shift N * denominator (Syn.shift N) (var 0) +
        monus (Syn.shift N) one * denominator (Syn.shift N) (var 0) +
        monus (denominator (Syn.shift N) (var 0)) one) ?_
      ipra_lc d + 𝔞(denominator (Syn.shift N) (var 0)) * h + i
  simpa only [subst_le, subst_denominator, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    using Prf.allE L all

/-- The next rational summand, with every denominator cleared. -/
theorem rational_addition (R N L : PTm n) :
    Γ ⊢[PRAAx] numerator R N (succ L) * denominator N L * (L + three) * pw N (L + three) ≐
      denominator N (succ L) *
        (numerator R N L * (L + three) * pw N (L + three) +
          pw R (L + three) * denominator N L) := by
  have a := natEq (numerator_succ (Γ := Γ) R N L)
  have d := natEq (denominator_succ (Γ := Γ) N L)
  have e : Γ ⊢[PRAAx] L + three ≐ succ (L + two) := by ipra_ring
  have p := natEq ((congrAp2 powF e (.eqRefl N)).eqTrans (pw_succ N (L + two)))
  unfold denominator at *
  apply deriveNat
  ipra_simps
  linear_combination
    𝔞(fact (L + two)) * 𝔞(pw N (L + two)) * (𝔞(L) + 3) * 𝔞(pw N (L + three)) * a -
    (𝔞(numerator R N L) * (𝔞(L) + 3) * 𝔞(pw N (L + three)) +
      𝔞(pw R (L + three)) * 𝔞(fact (L + two)) * 𝔞(pw N (L + two))) * d +
    𝔞(fact (L + two)) ^ 2 * 𝔞(pw N (L + two)) *
      (𝔞(L) + 3) * 𝔞(pw R (L + three)) * p

/-- The strong bound, retaining an explicit geometric remainder. -/
def strong (R N L : PTm n) : Fm PTm n :=
  le (three * N * N * N * numerator R N L +
      two * fact (L + two) * N * N * pw R (L + three))
    (two * R * R * R * denominator N L)

ipra_subst strong [fact]

theorem strong_zero (R N : PTm n) : Γ ⊢[PRAAx] strong R N zero := by
  have e : Γ ⊢[PRAAx] zero + three ≐ succ (succ (succ zero)) := by ipra_ring
  have p := natEq ((congrAp2 powF e (.eqRefl R)).eqTrans
    ((pw_succ R (succ (succ zero))).eqTrans
      ((congrMul (pw_succ R (succ zero)) (.eqRefl _)).eqTrans
        ((congrMul (congrMul (pw_one R) (.eqRefl _)) (.eqRefl _))))))
  have q := natEq ((congrAp2 (Γ := Γ) powF (zero_add two) (.eqRefl N)).eqTrans
    ((pw_succ N (succ zero)).eqTrans (congrMul (pw_one N) (.eqRefl _))))
  unfold strong denominator
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -3 * 𝔞(N) ^ 3 * natEq (numerator_zero (Γ := Γ) R N) - 2 * 𝔞(fact (zero + two)) * 𝔞(N) ^ 2 * p +
    2 * 𝔞(R) ^ 3 * 𝔞(fact (zero + two)) * q

/-- A polynomial induction step; the gap `N-2R` supplies the geometric estimate. -/
theorem strong_step {R N L : PTm n} (h : Γ ⊢[PRAAx] le (two * R) N)
    (ih : Γ ⊢[PRAAx] strong R N L) : Γ ⊢[PRAAx] strong R N (succ L) := by
  have d := natEq (denominator_succ (Γ := Γ) N L)
  have e₂ : Γ ⊢[PRAAx] succ L + two ≐ succ (L + two) := by ipra_ring
  have e₃ : Γ ⊢[PRAAx] succ L + three ≐ succ (L + three) := by ipra_ring
  unfold strong at *
  refine le_of_eq_add (d :=
    (L + three) * N * monus (two * R * R * R * denominator N L)
      (three * N * N * N * numerator R N L +
        two * fact (L + two) * N * N * pw R (L + three)) +
    fact (L + two) * N * N * pw R (L + three) *
      ((L + three) * monus N (two * R) + L * N)) ?_
  ipra_lc (𝔞(L) + 3) * 𝔞(N) * natEq (eq_add_of_le ih) +
    𝔞(fact (L + two)) * 𝔞(N) ^ 2 * 𝔞(pw R (L + three)) * (𝔞(L) + 3) * natEq (eq_add_of_le h) + 2 * 𝔞(R) ^ 3 * d -
    3 * 𝔞(N) ^ 3 * natEq (numerator_succ (Γ := Γ) R N L) -
    2 * 𝔞(N) ^ 2 * 𝔞(pw R (succ L + three)) * natEq ((congrAp2 factF e₂ (.eqRefl zero)).eqTrans (fact_succ (L + two) zero)) -
    2 * 𝔞(N) ^ 2 * 𝔞(fact (L + two)) * (𝔞(L) + 3) * natEq ((congrAp2 powF e₃ (.eqRefl R)).eqTrans (pw_succ R (L + three)))

/-- Every finite positive Taylor tail has the displayed explicit remainder. -/
theorem finite_taylor_strong (R N L : PTm n) (h : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] strong R N L := by
  have all : Γ ⊢[PRAAx] .all (strong (Syn.shift R) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_strong, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
        using strong_zero (Γ := Γ) R N
    · simp only [subst_strong, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have shifted : Γ.map Fm.shift ⊢[PRAAx] le (two * Syn.shift R) (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using h.shift
      exact strong_step shifted.wk Prf.hyp0
  simpa only [subst_strong, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    using Prf.allE L all

/-- The finite-series estimate `F_L ≤ 2R³/(3N³)`, with denominators cleared. -/
theorem finite_taylor_bound (R N L : PTm n) (h : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] le (three * N * N * N * numerator R N L)
      (two * R * R * R * denominator N L) :=
  le_trans (le_add_right _ _) (finite_taylor_strong R N L h)

/-- Variables `0 = L`, `1 = R`, `2 = N`. -/
def remainderFormula : Fm PTm 3 :=
  le (two * var 1) (var 2) ⟶ strong (var 1) (var 2) (var 0)

theorem finite_logarithm_remainder : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 remainderFormula :=
  closeUniv 3 (.impI (finite_taylor_strong _ _ _ Prf.hyp0))

/-- Variables `0 = L`, `1 = R`, `2 = N`. Multiplication by `N` is the Barnes factor. -/
def canonicalFactorFormula : Fm PTm 3 :=
  le (two * var 1) (var 2) ⟶
    le (three * var 2 * var 2 * (var 2 * numerator (var 1) (var 2) (var 0)))
      (two * var 1 * var 1 * var 1 * denominator (var 2) (var 0))

theorem finite_canonical_factor_bound :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 canonicalFactorFormula := by
  refine closeUniv 3 (.impI ?_)
  exact le_congr (by ipra_ring) (.eqRefl _) (finite_taylor_bound _ _ _ Prf.hyp0)

/-- Variables `0 = L`, `1 = R`, `2 = N`. This endpoint certifies both the
exact next-summand update and positivity of the rational denominator. -/
def evaluatorFormula : Fm PTm 3 :=
  (numerator (var 1) (var 2) zero ≐ zero) ⋏
    ((numerator (var 1) (var 2) (succ (var 0)) * denominator (var 2) (var 0) *
        (var 0 + three) * pw (var 2) (var 0 + three) ≐
      denominator (var 2) (succ (var 0)) *
        (numerator (var 1) (var 2) (var 0) * (var 0 + three) * pw (var 2) (var 0 + three) +
          pw (var 1) (var 0 + three) * denominator (var 2) (var 0))) ⋏
      (le one (var 2) ⟶ le one (denominator (var 2) (var 0))))

theorem exact_finite_taylor_evaluator :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 evaluatorFormula :=
  closeUniv 3 (.andI (numerator_zero _ _) (.andI (rational_addition _ _ _)
    (.impI (denominator_positive _ _ Prf.hyp0))))

#print axioms rational_addition
#print axioms finite_logarithm_remainder
#print axioms finite_canonical_factor_bound
#print axioms exact_finite_taylor_evaluator

end LeanProofs.IPRA.Analysis.LogarithmRemainder
