import IPRADerivations.Algebra.PowerDifference
import IPRADerivations.Core.SumOrder
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The pigeonhole step of the rational descent

Packet: `algebra/FTA_iPRA` (`lem:descent`, "A term dominant at three consecutive scales"). The
indices `k_j` of the dominant terms at the radii `r_j = 4^{−j} r_0`, `j ≤ 2n`, form a nonincreasing
sequence in `[1, n]`; some odd center `j = 2s + 1` has `k_{j−1} = k_j = k_{j+1}`, because otherwise
`k_{2n} ≤ k_0 − n ≤ 0`. For a body `k(j, x)`:

* `drop_pt`: `c ≤ b ≤ a` gives `c + 1 ≤ a + [c = a]`;
* `drops`: if `k_{2s+1} ≤ k_{2s}` and `k_{2s+2} ≤ k_{2s+1}` for `s < N`, then
  `k_{2m} + m ≤ k_0 + #{s < m : k_{2s+2} = k_{2s}}` for `m ≤ N`;
* `good_center`: if moreover `k_0 ≤ N` and `k_{2N} ≥ 1`, at least one center `s < N` has
  `k_{2s+2} = k_{2s}`, so the count is positive;
* `triple_of_center`: at such a center `k_{2s} = k_{2s+1} = k_{2s+2}`;
* `geom_third`: `3 ∑_{i<m} 4^i + 1 = 4^m`, the bound "each of the two finite geometric sums is at
  most `1/3`" of `eq:other-terms`.

The witness itself is then given by bounded search. The magnitude estimates are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.DescentPigeonhole

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.PowerDifference (gd geom_sum)
open LeanProofs.IPRA.Foundations.BoundedReflection (eq_of_eqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `c ≤ b ≤ a` gives `c + 1 ≤ a + [c = a]`. -/
theorem drop_pt {a b c : PTm n} (h₁ : Γ ⊢[PRAAx] le b a) (h₂ : Γ ⊢[PRAAx] le c b) :
    Γ ⊢[PRAAx] le (c + one) (a + eqb c a) := by
  refine .orE (lt_or_eq_of_le (le_trans h₂ h₁)) ?_ ?_
  · exact le_trans (le_congr (succ_eq_add_one _) (.eqRefl _) Prf.hyp0) (le_add_right _ _)
  · exact le_congr (.eqRefl _) (congrAdd Prf.hyp0 (eqb_of_eq Prf.hyp0).eqSymm) (le_refl _)

section Pigeonhole

variable (k : PTm 2)

/-- `[k(2s + 2) = k(2s)]`, over `0 = s`, `1 = x`. -/
abbrev eB : PTm 2 :=
  eqb (Syn.subst ![succ (succ (two * var 0)), var 1] k) (Syn.subst ![two * var 0, var 1] k)

theorem inst2_e (s x : PTm n) :
    inst2 (eB k) s x = eqb (inst2 k (succ (succ (two * s))) x) (inst2 k (two * s) x) := by
  have h₁ : Syn.subst ![s, x] (Syn.subst ![succ (succ (two * var 0)), var 1] k) =
      inst2 k (succ (succ (two * s))) x := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have h₂ : Syn.subst ![s, x] (Syn.subst ![two * var 0, var 1] k) = inst2 k (two * s) x := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, eB, subst_eqb, h₁, h₂]

/-- The paired monotonicity `k_{2s+1} ≤ k_{2s}`, `k_{2s+2} ≤ k_{2s+1}` for `s < N`. -/
abbrev Mono (N x : PTm n) : Fm PTm (n + 1) :=
  lt (var 0) (Syn.shift N) ⟶
    (le (inst2 k (succ (two * var 0)) (Syn.shift x)) (inst2 k (two * var 0) (Syn.shift x)) ⋏
      le (inst2 k (succ (succ (two * var 0))) (Syn.shift x)) (inst2 k (succ (two * var 0)) (Syn.shift x)))

alias two_succ := Common.two_mul_succ

theorem drops_step {m x : PTm n}
    (ih : Γ ⊢[PRAAx] le (inst2 k (two * m) x + m) (inst2 k (two * zero) x + ap2 (sumF (eB k)) m x))
    (hm : Γ ⊢[PRAAx] le (inst2 k (succ (two * m)) x) (inst2 k (two * m) x) ⋏
      le (inst2 k (succ (succ (two * m))) x) (inst2 k (succ (two * m)) x)) :
    Γ ⊢[PRAAx] le (inst2 k (two * succ m) x + succ m)
      (inst2 k (two * zero) x + ap2 (sumF (eB k)) (succ m) x) := by
  have d := drop_pt (Prf.andE₁ hm) (Prf.andE₂ hm)
  have s := sum_succ' (Γ := Γ) (eB k) m x
  rw [inst2_e] at s
  have t := add_le_add₂ ih d
  refine le_of_add_le_add_right (c := inst2 k (two * m) x) (le_congr ?_ ?_ t)
  · have c := natEq (congrInst2 (Γ := Γ) k (two_succ m) (.eqRefl x))
    apply deriveNat; ipra_simps; linear_combination -c
  · have c := natEq s
    apply deriveNat; ipra_simps; linear_combination -c

/-- `k_{2m} + m ≤ k_0 + #{s < m : k_{2s+2} = k_{2s}}` for `m ≤ N`. -/
theorem drops (N x : PTm n) (hm : Γ ⊢[PRAAx] Fm.all (Mono k N x)) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (inst2 k (two * var 0) (Syn.shift x) + var 0)
        (inst2 k (two * zero) (Syn.shift x) + ap2 (sumF (eB k)) (var 0) (Syn.shift x))) := by
  refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var,
      Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI (le_congr (.eqRefl _) ?_ (le_refl _))
    exact congrAdd (.eqRefl _) (sum_zero _ _).eqSymm
  · simp only [Fm.subst_imp, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var,
      Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have hf := hm.allOpen
    refine .impI ?_
    have hle : (le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ le (inst2 k (two * var 0) (Syn.shift x) + var 0)
          (inst2 k (two * zero) (Syn.shift x) + ap2 (sumF (eB k)) (var 0) (Syn.shift x))) ::
        Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
      le_trans (le_succ_self _) Prf.hyp0
    exact drops_step k (Prf.impE Prf.hyp1 hle) (Prf.impE hf.wk.wk Prf.hyp0)

/-- Some center `s < N` has `k_{2s+2} = k_{2s}`: the count is at least `1`. -/
theorem good_center {N x : PTm n} (hm : Γ ⊢[PRAAx] Fm.all (Mono k N x))
    (h₀ : Γ ⊢[PRAAx] le (inst2 k (two * zero) x) N) (h₁ : Γ ⊢[PRAAx] le one (inst2 k (two * N) x)) :
    Γ ⊢[PRAAx] le one (ap2 (sumF (eB k)) N x) := by
  have h := Prf.allE N (drops k N x hm)
  simp only [Fm.subst_imp, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  have d := Prf.impE h (le_refl N)
  have t := le_trans (add_le_add₂ h₁ (le_refl N)) (le_trans d (add_le_add₂ h₀ (le_refl _)))
  exact le_of_add_le_add_right (c := N) (le_congr (.eqRefl _) (add_comm _ _) t)

/-- At a good center the three indices agree. -/
theorem triple_of_center {s x : PTm n}
    (hm : Γ ⊢[PRAAx] le (inst2 k (succ (two * s)) x) (inst2 k (two * s) x) ⋏
      le (inst2 k (succ (succ (two * s))) x) (inst2 k (succ (two * s)) x))
    (he : Γ ⊢[PRAAx] inst2 (eB k) s x ≐ one) :
    Γ ⊢[PRAAx] (inst2 k (two * s) x ≐ inst2 k (succ (two * s)) x) ⋏
      (inst2 k (succ (two * s)) x ≐ inst2 k (succ (succ (two * s))) x) := by
  rw [inst2_e] at he
  have e := eq_of_eqb he
  have a : Γ ⊢[PRAAx] le (inst2 k (two * s) x) (inst2 k (succ (two * s)) x) :=
    le_congr e (.eqRefl _) (Prf.andE₂ hm)
  have b := le_antisymm (Prf.andE₁ hm) a
  exact .andI b.eqSymm (le_antisymm (le_congr (.eqRefl _) e.eqSymm (Prf.andE₁ hm)) (Prf.andE₂ hm))

end Pigeonhole

/-! ## The geometric bound -/

/-- `3 ∑_{i<m} 4^i + 1 = 4^m`. -/
theorem geom_third (m : PTm n) :
    Γ ⊢[PRAAx] (two + one) * gd (two * two) one m + one ≐ pw (two * two) m := by
  ipra_lc -natEq (geom_sum (Γ := Γ) (two * two) m)

end LeanProofs.IPRA.Algebra.DescentPigeonhole
