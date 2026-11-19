import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Combinatorics.BellTouchardPower
import IPRADerivations.AnalyticNumberTheory.Primes
import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Foundations.BoundedReflection

/-!
# The super-Catalan numbers are integers (`catalan_numbers_ipra_2026-11-16`, (7.14))

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Section 7, "Super-Catalan integers":
"The two-parameter super-Catalan numbers ... are `S(m, n) = (2m)!(2n)!/(m! n! (m + n)!)`
(7.14)", shown to be integers there by summing the floor inequality (7.15)
(`Combinatorics/SuperCatalanFloor`) with Legendre's formula.

This module derives the integrality by a different finite argument, Gessel's recurrence

  `S(m, n + 1) + S(m + 1, n) = 4 S(m, n)`,

which needs no prime factorization. With `Nu m k = (2m)!(2k)!` and `De m k = m! k! (m + k)!`:

* `gessel`: the recurrence cleared of denominators,
  `Nu(m, k+1) De(m, k) De(m+1, k) + De(m, k+1) Nu(m+1, k) De(m, k)
     = 4 De(m, k+1) Nu(m, k) De(m+1, k)`;
* `dvd_base`: `De(m, 0) ∣ Nu(m, 0)`, the central binomial coefficient;
* `dvd_step`: `De(m, k) ∣ Nu(m, k)` and `De(m+1, k) ∣ Nu(m+1, k)` give
  `De(m, k+1) ∣ Nu(m, k+1)`;
* the induction on `k` needs the statement for all `m`; below a bound `T` it is one bit
  (`vB`, `level_at`, `lv_ne`, `level_succ`, `level_all`), and level `k + 1` at `m` uses level
  `k` at `m` and `m + 1`, which stay below the same bound `m + k + 1 ≤ T`;
* `super_catalan_integral`: `m! k! (m + k)!` divides `(2m)! (2k)!` for all `m`, `k`;
  `super_catalan_integral_closed`.

Not derived: the derivation through Legendre's formula, and a combinatorial interpretation
(the packet lists it as an open problem).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.SuperCatalanIntegral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul bden binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (monus_of_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_sub')
open LeanProofs.IPRA.Foundations.BoundedReflection (allB allB_zero all_elim all_intro)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Numerator and denominator -/

/-- `(2m)! (2k)!`. -/
def Nu (m k : PTm n) : PTm n := fact (m + m) * fact (k + k)

/-- `m! k! (m + k)!`. -/
def De (m k : PTm n) : PTm n := fact m * fact k * fact (m + k)

theorem congrFact {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] fact a ≐ fact b :=
  congrAp2 factF h (.eqRefl _)

theorem congrNu {m m' k k' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hk : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] Nu m k ≐ Nu m' k' := by
  unfold Nu
  exact congrMul (congrFact (congrAdd hm hm)) (congrFact (congrAdd hk hk))

theorem congrDe {m m' k k' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hk : Γ ⊢[PRAAx] k ≐ k') :
    Γ ⊢[PRAAx] De m k ≐ De m' k' := by
  unfold De
  exact congrMul (congrMul (congrFact hm) (congrFact hk)) (congrFact (congrAdd hm hk))

theorem De_pos (m k : PTm n) : Γ ⊢[PRAAx] De m k ≐ succ (pred (De m k)) := by
  unfold De
  exact pos_mul (pos_mul (fact_pos m) (fact_pos k)) (fact_pos (m + k))

theorem shift_De (m k : PTm n) : Syn.shift (De m k) = De (Syn.shift m) (Syn.shift k) := by
  simp [De, Syn.shift]

theorem shift_Nu (m k : PTm n) : Syn.shift (Nu m k) = Nu (Syn.shift m) (Syn.shift k) := by
  simp [Nu, Syn.shift]

/-! ## Gessel's recurrence -/

/-- `S(m, k+1) + S(m+1, k) = 4 S(m, k)`, cleared of denominators. -/
theorem gessel (m k : PTm n) :
    Γ ⊢[PRAAx] Nu m (succ k) * (De m k * De (succ m) k) +
        De m (succ k) * (Nu (succ m) k * De m k) ≐
      num 4 * (De m (succ k) * (Nu m k * De (succ m) k)) := by
  have Ea := fact_succ (Γ := Γ) m zero
  have Eb := fact_succ (Γ := Γ) k zero
  have Ec : Γ ⊢[PRAAx] fact (succ m + k) ≐ fact (m + k) * succ (m + k) :=
    (congrFact (a := succ m + k) (b := succ (m + k))
      (by apply deriveNat; ipra_simps; ring)).eqTrans (fact_succ (m + k) zero)
  have Ed : Γ ⊢[PRAAx] fact (m + succ k) ≐ fact (m + k) * succ (m + k) :=
    (congrFact (a := m + succ k) (b := succ (m + k))
      (by apply deriveNat; ipra_simps; ring)).eqTrans (fact_succ (m + k) zero)
  have Ee : Γ ⊢[PRAAx] fact (succ m + succ m) ≐
      fact (m + m) * succ (m + m) * succ (succ (m + m)) :=
    (congrFact (a := succ m + succ m) (b := succ (succ (m + m)))
      (by apply deriveNat; ipra_simps; ring)).eqTrans
      ((fact_succ (succ (m + m)) zero).eqTrans (congrMul (fact_succ (m + m) zero) (.eqRefl _)))
  have Ef : Γ ⊢[PRAAx] fact (succ k + succ k) ≐
      fact (k + k) * succ (k + k) * succ (succ (k + k)) :=
    (congrFact (a := succ k + succ k) (b := succ (succ (k + k)))
      (by apply deriveNat; ipra_simps; ring)).eqTrans
      ((fact_succ (succ (k + k)) zero).eqTrans (congrMul (fact_succ (k + k) zero) (.eqRefl _)))
  unfold Nu De
  have ea := natEq Ea
  have eb := natEq Eb
  have ec := natEq Ec
  have ed := natEq Ed
  have ee := natEq Ee
  have ef := natEq Ef
  apply deriveNat; ipra_simps
  rw [ea, eb, ec, ed, ee, ef]
  ring

/-! ## The base and the step of the divisibility -/

/-- `(m!)² ∣ (2m)!`. -/
theorem dvd_base (m : PTm n) : Γ ⊢[PRAAx] dvd (De m zero) (Nu m zero) := by
  refine dvd_of_eq' (De_pos m zero) (w := binom (m + m) m) ?_
  have E1 := binom_eq (Γ := Γ) (k := m) (n := m + m) (le_add_right m m)
  have E2 : Γ ⊢[PRAAx] fact (monus (m + m) m) ≐ fact m := congrFact (add_monus m m)
  have E3 : Γ ⊢[PRAAx] fact (zero : PTm n) ≐ one := fact_zero _
  have E4 : Γ ⊢[PRAAx] fact ((zero : PTm n) + zero) ≐ one :=
    (congrFact (add_zero zero)).eqTrans (fact_zero _)
  have E5 : Γ ⊢[PRAAx] fact (m + zero) ≐ fact m := congrFact (add_zero m)
  unfold Nu De
  have e1 := natEq E1
  have e2 := natEq E2
  have e3 := natEq E3
  have e4 := natEq E4
  have e5 := natEq E5
  apply deriveNat; ipra_simps
  rw [e1, e2, e3, e4, e5]
  ring

/-- From `S(m, k)` and `S(m+1, k)` to `S(m, k+1)`. -/
theorem dvd_step {m k : PTm n} (h1 : Γ ⊢[PRAAx] dvd (De m k) (Nu m k))
    (h2 : Γ ⊢[PRAAx] dvd (De (succ m) k) (Nu (succ m) k)) :
    Γ ⊢[PRAAx] dvd (De m (succ k)) (Nu m (succ k)) := by
  have a := eq_of_dvd' (De_pos m k) h1
  have b := eq_of_dvd' (De_pos (succ m) k) h2
  have key : Γ ⊢[PRAAx] De m k * De (succ m) k *
        (Nu m (succ k) + De m (succ k) * quo (Nu (succ m) k) (De (succ m) k)) ≐
      De m k * De (succ m) k * (De m (succ k) * (num 4 * quo (Nu m k) (De m k))) := by
    have g := natEq (gessel (Γ := Γ) m k)
    have ea := natEq a
    have eb := natEq b
    apply deriveNat; ipra_simps
    linear_combination g - 𝔞 (De m (succ k)) * 𝔞 (De m k) * eb +
      4 * (𝔞 (De m (succ k)) * 𝔞 (De (succ m) k)) * ea
  have c := mul_cancel (pos_mul (De_pos m k) (De_pos (succ m) k)) key
  exact dvd_sub' (De_pos m (succ k)) (dvd_of_eq' (De_pos m (succ k)) c)
    (dvd_of_eq' (De_pos m (succ k)) (.eqRefl _))

/-! ## The level bit -/

/-- The parameter `⟨k, T⟩`. -/
abbrev lvP (k T : PTm n) : PTm n := pairT k T

/-- The bit of `m + k ≤ T → De(m, k) ∣ Nu(m, k)`, over `0 = m`, `1 = ⟨k, T⟩`. -/
def vB : PTm 2 :=
  monus (var 0 + fstT (var 1)) (sndT (var 1)) +
    eqb (rem (Nu (var 0) (fstT (var 1))) (De (var 0) (fstT (var 1)))) zero

theorem v_at (m k T : PTm n) :
    Γ ⊢[PRAAx] inst2 vB m (lvP k T) ≐ monus (m + k) T + eqb (rem (Nu m k) (De m k)) zero := by
  have h : inst2 vB m (lvP k T) = monus (m + fstT (lvP k T)) (sndT (lvP k T)) +
      eqb (rem (Nu m (fstT (lvP k T))) (De m (fstT (lvP k T)))) zero := by
    simp [inst2, vB, Nu, De]
  rw [h]
  exact congrAdd (congrMonus (congrAdd (.eqRefl m) (fst_pair _ _)) (snd_pair _ _))
    (congrEqb (congrAp2 remF (congrNu (.eqRefl m) (fst_pair _ _))
      (congrDe (.eqRefl m) (fst_pair _ _))) (.eqRefl _))

theorem level_at {m k T : PTm n} (hQ : Γ ⊢[PRAAx] allB vB (succ T) (lvP k T) ≐ one)
    (hm : Γ ⊢[PRAAx] le (m + k) T) : Γ ⊢[PRAAx] dvd (De m k) (Nu m k) := by
  have hlt : Γ ⊢[PRAAx] lt m (succ T) :=
    (succ_monus_succ m T).eqTrans (le_trans (le_add_right m _) hm)
  have ne := all_elim vB hQ hlt
  refine eq_of_eqb_ne (.impI (.impE ne.wk ?_))
  exact (v_at m k T).eqTrans ((congrAdd hm.wk Prf.hyp0).eqTrans (add_zero _))

theorem lv_ne_gt {m k T : PTm n} (h : Γ ⊢[PRAAx] lt T (m + k))
    (hz : Γ ⊢[PRAAx] inst2 vB m (lvP k T) ≐ zero) : Γ ⊢[PRAAx] Fm.bot := by
  refine succ_ne_zero' _ (a := monus (m + k) (succ T) + eqb (rem (Nu m k) (De m k)) zero) ?_
  have e₁ := natEq (v_at (Γ := Γ) m k T)
  have e₂ := natEq hz
  have e₃ := natEq (monus_of_lt h)
  apply deriveNat; ipra_simps
  linear_combination e₂ - e₁ - e₃

theorem lv_ne_le {m k T : PTm n} (h : Γ ⊢[PRAAx] dvd (De m k) (Nu m k))
    (hm : Γ ⊢[PRAAx] le (m + k) T)
    (hz : Γ ⊢[PRAAx] inst2 vB m (lvP k T) ≐ zero) : Γ ⊢[PRAAx] Fm.bot :=
  Foundations.BoundedReflection.one_ne_zero _
    (((v_at m k T).eqTrans ((congrAdd hm (eqb_of_eq h)).eqTrans (zero_add one))).eqSymm.eqTrans hz)

theorem lv_ne {m k T : PTm n}
    (h : Γ ⊢[PRAAx] le (m + k) T ⟶ dvd (De m k) (Nu m k)) :
    Γ ⊢[PRAAx] neg (inst2 vB m (lvP k T) ≐ zero) :=
  .impI (.orE (lt_or_le T (m + k)) (lv_ne_gt Prf.hyp0 Prf.hyp1)
    (lv_ne_le (.impE h.wk.wk Prf.hyp0) Prf.hyp0 Prf.hyp1))

theorem shift_lvP (k T : PTm n) : Syn.shift (lvP k T) = lvP (Syn.shift k) (Syn.shift T) := by
  simp [Syn.shift]

theorem shift_lvP_succ (k T : PTm n) :
    Syn.shift (lvP (succ k) T) = lvP (succ (Syn.shift k)) (Syn.shift T) := by
  simp [Syn.shift]

theorem shift_lvP_zero (T : PTm n) : Syn.shift (lvP zero T) = lvP zero (Syn.shift T) := by
  simp [Syn.shift]

/-- From level `k` to level `k + 1`, below the same bound. -/
theorem level_succ {k T : PTm n} (hQ : Γ ⊢[PRAAx] allB vB (succ T) (lvP k T) ≐ one) :
    Γ ⊢[PRAAx] allB vB (succ T) (lvP (succ k) T) ≐ one := by
  refine all_intro vB (.allI (.impI ?_))
  rw [shift_lvP_succ]
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
      allB vB (succ (Syn.shift T)) (lvP (Syn.shift k) (Syn.shift T)) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  refine lv_ne (.impI (dvd_step
    (level_at hQ'.wk.wk (le_trans (le_of_eq_add (d := one) ?_) Prf.hyp0))
    (level_at hQ'.wk.wk (le_congr ?_ (.eqRefl _) Prf.hyp0))))
  · apply deriveNat; ipra_simps; ring
  · apply deriveNat; ipra_simps; ring

/-- The induction formula on `k`: the level bit below `T`. -/
abbrev powF (T : PTm n) : Fm PTm (n + 1) :=
  allB vB (succ (Syn.shift T)) (lvP (var 0) (Syn.shift T)) ≐ one

theorem level_all (k T : PTm n) : Γ ⊢[PRAAx] allB vB (succ T) (lvP k T) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (powF T) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] allB vB (succ T) (lvP zero T) ≐ one := by
        refine all_intro vB (.allI (.impI ?_))
        rw [shift_lvP_zero]
        exact lv_ne (.impI (dvd_base _))
      simpa using b
    · have st : (powF T :: Γ.map Fm.shift) ⊢[PRAAx]
          allB vB (succ (Syn.shift T)) (lvP (succ (var 0)) (Syn.shift T)) ≐ one :=
        level_succ Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE k hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-! ## The theorem -/

/-- (7.14): the super-Catalan number `(2m)!(2k)!/(m! k! (m + k)!)` is an integer. -/
theorem super_catalan_integral (m k : PTm n) : Γ ⊢[PRAAx] dvd (De m k) (Nu m k) :=
  level_at (level_all k (m + k)) (le_refl _)

/-- Closed over `m` and `k`, with the factorials written out. -/
theorem super_catalan_integral_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (dvd (fact (var 0) * fact (var 1) * fact (var 0 + var 1))
        (fact (var 0 + var 0) * fact (var 1 + var 1))) :=
  closeUniv 2 (super_catalan_integral (var 0) (var 1))

end LeanProofs.IPRA.Combinatorics.SuperCatalanIntegral
