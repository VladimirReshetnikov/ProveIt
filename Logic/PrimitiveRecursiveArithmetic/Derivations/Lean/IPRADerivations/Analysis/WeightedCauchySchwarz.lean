import IPRADerivations.Analysis.WeierstrassProduct
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.LinearCombination

/-!
# The weighted Cauchy–Schwarz inequality for finite sums

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `energy.tex`, proof of `thm:energy`: "Weighted
Cauchy–Schwarz now gives `M(N)² ≤ E_N Σ_{d≤N} μ(d)²/J_2(d)` … It is an inequality between rationals, obtainable by sums of
squares and clearing denominators" (the packet's metatheory: `EnergyInequality.weighted_cauchy`).

For natural-valued bodies `a, b, w, c` over `i < N` with `b_i² ≤ w_i c_i` (i.e. `c_i ≥ b_i²/w_i`), cleared of every
denominator:

  `(Σ_{i<N} a_i b_i)² ≤ (Σ_{i<N} w_i a_i²) · (Σ_{i<N} c_i)`                              (`weighted_cs`)

so `(Σ a_i b_i)² ≤ (Σ w_i a_i²)(Σ b_i²/w_i)` whenever the `c_i` dominate `b_i²/w_i`. The proof is a quantifier-free
induction on `N`; the step needs only the square-root-free AM–GM `XY ≥ Z² → X + Y ≥ 2Z` (`amgm2`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.WeightedCauchySchwarz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Square-root-free AM–GM -/

/-- `4XY ≤ (X + Y)²`. -/
theorem four_le_sq (X Y : PTm n) : Γ ⊢[PRAAx] le (two * two * (X * Y)) ((X + Y) * (X + Y)) := by
  refine .orE (le_total X Y) ?_ ?_
  · have e := natEq (eq_add_of_le (Prf.hyp0 : (le X Y :: Γ) ⊢[PRAAx] le X Y))
    refine le_of_eq_add (d := monus Y X * monus Y X) ?_
    ipra_lc (𝔞 X + 𝔞 Y + 𝔞 (monus Y X) - 2 * 𝔞 X) * e + 0
  · have e := natEq (eq_add_of_le (Prf.hyp0 : (le Y X :: Γ) ⊢[PRAAx] le Y X))
    refine le_of_eq_add (d := monus X Y * monus X Y) ?_
    ipra_lc (𝔞 X + 𝔞 Y + 𝔞 (monus X Y) - 2 * 𝔞 Y) * e + 0

theorem sq_pw (a : PTm n) : Γ ⊢[PRAAx] pw a (succ one) ≐ a * a :=
  (pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl _))

/-- `Z² ≤ XY → 2Z ≤ X + Y`. -/
theorem amgm2 {X Y Z : PTm n} (h : Γ ⊢[PRAAx] le (Z * Z) (X * Y)) : Γ ⊢[PRAAx] le (two * Z) (X + Y) := by
  have a := le_mul_mono (le_refl (two * two : PTm n)) h
  have b := le_trans a (four_le_sq X Y)
  have c : Γ ⊢[PRAAx] le (pw (two * Z) (succ one)) (pw (X + Y) (succ one)) :=
    le_congr (by apply deriveNat; have e1 := natEq (sq_pw (Γ := Γ) (two * Z)); ipra_simps; linear_combination -e1)
      (sq_pw _).eqSymm b
  exact AnalyticNumberTheory.PowerCleared.pw_le_cancel c

/-! ## The step -/

/-- Abstract step: `S² ≤ AC`, `β² ≤ ωγ` give `(S + αβ)² ≤ (A + ωα²)(C + γ)`. -/
theorem cs_alg {S A C α β ω γ : PTm n} (ih : Γ ⊢[PRAAx] le (S * S) (A * C)) (hk : Γ ⊢[PRAAx] le (β * β) (ω * γ)) :
    Γ ⊢[PRAAx] le ((S + α * β) * (S + α * β)) ((A + ω * (α * α)) * (C + γ)) := by
  -- the cross terms: `(Aγ)(ωα²C) ≥ (Sαβ)²`
  have m1 := le_mul_mono (le_mul_mono ih hk) (le_refl (α * α))
  have m2 : Γ ⊢[PRAAx] le ((S * α * β) * (S * α * β)) ((A * γ) * (ω * α * α * C)) :=
    le_congr (by ipra_ring) (by ipra_ring) m1
  have cr := amgm2 m2
  -- the diagonal term: `ωα²γ ≥ α²β²`
  have dg := le_mul_mono (le_refl (α * α)) hk
  refine le_of_eq_add (d := monus (A * C) (S * S) + monus (A * γ + ω * α * α * C) (two * (S * α * β)) +
    monus (α * α * (ω * γ)) (α * α * (β * β))) ?_
  ipra_lc natEq (eq_add_of_le ih) + natEq (eq_add_of_le cr) + natEq (eq_add_of_le dg)

/-! ## The induction -/

section Main

variable (a b w c : PTm 2)

/-- `S_ab(k)`, `S_w(k)`, `S_c(k)`. -/
abbrev Sab (k x : PTm n) : PTm n := ap2 (sumF (a * b)) k x
abbrev Swa (k x : PTm n) : PTm n := ap2 (sumF (w * (a * a))) k x
abbrev Sc (k x : PTm n) : PTm n := ap2 (sumF c) k x

/-- The invariant `S_ab(k)² ≤ S_w(k) S_c(k)`. -/
abbrev CSF (k x : PTm n) : Fm PTm n := le (Sab a b k x * Sab a b k x) (Swa a w k x * Sc c k x)

theorem inst2_mul (f g : PTm 2) (i x : PTm n) : inst2 (f * g) i x = inst2 f i x * inst2 g i x := by simp [inst2]

theorem cs_base (x : PTm n) : Γ ⊢[PRAAx] CSF a b w c zero x := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc (𝔞 (ap2 (sumF c) zero x)) * natEq (sum_zero (Γ := Γ) (w * (a * a)) x) -
    (𝔞 (ap2 (sumF (a * b)) zero x)) * natEq (sum_zero (Γ := Γ) (a * b) x) + 0 * natEq (sum_zero (Γ := Γ) c x)

theorem cs_step {k x : PTm n}
    (hk : Γ ⊢[PRAAx] le (inst2 b k x * inst2 b k x) (inst2 w k x * inst2 c k x)) (ih : Γ ⊢[PRAAx] CSF a b w c k x) :
    Γ ⊢[PRAAx] CSF a b w c (succ k) x := by
  have s1 := sum_succ' (Γ := Γ) (a * b) k x
  have s2 := sum_succ' (Γ := Γ) (w * (a * a)) k x
  have s3 := sum_succ' (Γ := Γ) c k x
  rw [inst2_mul] at s1
  rw [inst2_mul, inst2_mul] at s2
  have st := cs_alg (α := inst2 a k x) ih hk
  exact le_congr (congrMul s1 s1).eqSymm (congrMul s2 s3).eqSymm st

variable {a b w c}

theorem cs_all {x N : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 b (var 0) (Syn.shift x) * inst2 b (var 0) (Syn.shift x))
        (inst2 w (var 0) (Syn.shift x) * inst2 c (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶ CSF a b w c (var 0) (Syn.shift x)) := by
  refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
    exact .impI (cs_base a b w c x)
  · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (cs_step a b w c (Prf.impE hb.allOpen.wk.wk Prf.hyp0)
      (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))

/-- The weighted Cauchy–Schwarz inequality: if `b_i² ≤ w_i c_i` for `i < N`, then
`(Σ_{i<N} a_i b_i)² ≤ (Σ_{i<N} w_i a_i²)(Σ_{i<N} c_i)`. -/
theorem weighted_cs {x N : PTm n}
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 b (var 0) (Syn.shift x) * inst2 b (var 0) (Syn.shift x))
        (inst2 w (var 0) (Syn.shift x) * inst2 c (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] CSF a b w c N x := by
  have h := Prf.allE N (cs_all (a := a) hb)
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h
  exact .impE h (le_refl N)

end Main

end LeanProofs.IPRA.Analysis.WeightedCauchySchwarz
