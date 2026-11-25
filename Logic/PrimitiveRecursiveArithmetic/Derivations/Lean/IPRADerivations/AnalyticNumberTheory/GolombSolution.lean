import IPRADerivations.AnalyticNumberTheory.ChebyshevCorollaries
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.CommonLemmas

/-!
# Golomb's theorem with a bounded witness

Packet: `analytic-number-theory/prime-counting-ipra`, `sections/sieve.tex`, Proposition "Golomb's theorem with
bounded witnesses": for `k ≥ 2` the equation `N = k π(N)` has a solution with `N ≥ 2` below an explicit bound.

The solution is the least `N ≥ 2` with `k π(N) ≤ N`, found by a bounded search below `B(k) = 2^{13k+1}`
(`ChebyshevCorollaries.pi_density` gives `k π(B) < B`). At that `N`:

* if `N = 2`, then `k π(2) = k ≥ 2` and `k π(2) ≤ 2`, so `k π(2) = 2`;
* otherwise `k π(N − 1) > N − 1` by minimality, hence `k π(N) ≥ k π(N − 1) ≥ N`, and `k π(N) ≤ N`.

* `pc_two`: `π(2) = 1`;
* `gB`, `Ng`: the search body and the solution `N(k)`;
* **`golomb`**: for `k ≥ 2`, `N(k) = k π(N(k))`, `2 ≤ N(k)` and `N(k) ≤ B(k) + 1`.

The packet's bound `B(k) = 2k(a + 2^a) + 1` and the count of all solutions are not derived; the bound here comes
from the Chebyshev estimate.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GolombSolution

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP isP_of_prime pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (piB)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank (pc pc_zero pc_succ pc_mono isP_small congrPc)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevCorollaries (pi_density)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_intro ex_elim ex_least)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `π(2) = 1`. -/
theorem pc_two : Γ ⊢[PRAAx] pc (two : PTm n) ≐ one :=
  (pc_succ one).eqTrans ((congrAdd ((pc_succ zero).eqTrans
    ((congrAdd pc_zero (isP_small (le_refl one))).eqTrans (zero_add zero)))
    (isP_of_prime PhiLower.prime_two)).eqTrans (zero_add one))

/-! ## The search -/

/-- `(i + 3) ∸ k π(i + 2)`: nonzero exactly when `k π(i + 2) ≤ i + 2`; variables `0 = i`, `1 = k`. -/
abbrev gB : PTm 2 := monus (succ (var 0 + two)) (var 1 * ap2 (sumF piB) (succ (var 0 + two)) zero)

theorem inst2_gB (i k : PTm n) : inst2 gB i k = monus (succ (i + two)) (k * pc (i + two)) := by
  simp [inst2, subst_ap2, PTm.subst_monus]

theorem g_ne {i k : PTm n} (h : Γ ⊢[PRAAx] le (k * pc (i + two)) (i + two)) :
    Γ ⊢[PRAAx] neg (inst2 gB i k ≐ zero) := by
  rw [inst2_gB]
  refine .impI ?_
  have hl : ((monus (succ (i + two)) (k * pc (i + two)) ≐ zero) :: Γ) ⊢[PRAAx]
      lt (i + two) (k * pc (i + two)) := Prf.hyp0
  exact le_lt_absurd _ h.wk hl

theorem le_of_g_ne {i k : PTm n} (h : Γ ⊢[PRAAx] neg (inst2 gB i k ≐ zero)) :
    Γ ⊢[PRAAx] le (k * pc (i + two)) (i + two) := by
  rw [inst2_gB] at h
  refine .orE (lt_or_le (i + two) (k * pc (i + two))) ?_ Prf.hyp0
  have hl : (lt (i + two) (k * pc (i + two)) :: Γ) ⊢[PRAAx]
      monus (succ (i + two)) (k * pc (i + two)) ≐ zero := Prf.hyp0
  exact .botE _ (.impE h.wk hl)

/-- The bound `B(k) = 2^{13k+1}`. -/
abbrev Bk (k : PTm n) : PTm n := pw two (succ (num 13 * k))

/-- The solution `N(k)`: `2` plus the least `i < B(k)` with `k π(i + 2) ≤ i + 2`. -/
abbrev Ng (k : PTm n) : PTm n := wit gB (Bk k) k + two

theorem bk_alg {B P : PTm n} (e : Γ ⊢[PRAAx] B ≐ P * two) (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) :
    Γ ⊢[PRAAx] B ≐ two + two * pred P := by
  ipra_lc natEq e + 2 * natEq hP

theorem comm2 {B i : PTm n} (e : Γ ⊢[PRAAx] B ≐ two + i) : Γ ⊢[PRAAx] i + two ≐ B := by
  ipra_lc -natEq e

theorem lt_of_add_two {B i : PTm n} (e : Γ ⊢[PRAAx] B ≐ two + i) : Γ ⊢[PRAAx] lt i B := by
  refine le_of_eq_add (d := one) ?_
  ipra_lc natEq e

theorem succ_two (j : PTm n) : Γ ⊢[PRAAx] succ (j + two) ≐ succ j + two := by
  ipra_ring

theorem zero_two : Γ ⊢[PRAAx] (zero : PTm n) + two ≐ two := zero_add two

alias mul_one_r := Common.mul_one_right

/-- **Golomb**: for `k ≥ 2`, `N(k) = k π(N(k))`, with `2 ≤ N(k) ≤ B(k) + 1`. -/
theorem golomb {k : PTm n} (hk2 : Γ ⊢[PRAAx] le two k) :
    Γ ⊢[PRAAx] (Ng k ≐ k * pc (Ng k)) ⋏ (le two (Ng k) ⋏ le (Ng k) (succ (Bk k))) := by
  have hk := p_pos hk2
  -- the search has a witness: `i₀ + 2 = B(k)`
  have hB2 : Γ ⊢[PRAAx] le two (Bk k) :=
    le_of_eq_add (bk_alg (pw_succ two (num 13 * k)) (pw_pos' two_pos' (num 13 * k)))
  have eB := eq_add_of_le hB2
  have eB' := comm2 eB
  have dens := pi_density hk (le_refl (succ (num 13 * k))) (le_refl (Bk k))
  have w0 : Γ ⊢[PRAAx] le (k * pc (monus (Bk k) two + two)) (monus (Bk k) two + two) :=
    le_congr (congrMul (.eqRefl _) (congrPc eB'.eqSymm)) eB'.eqSymm (le_of_lt dens)
  have ex := ex_intro gB (g_ne w0) (lt_of_add_two eB)
  have el := ex_elim gB ex
  have hle := le_of_g_ne (Prf.andE₂ el)
  have hlow : Γ ⊢[PRAAx] le two (Ng k) := le_add_left two (wit gB (Bk k) k)
  have hup : Γ ⊢[PRAAx] le (Ng k) (succ (Bk k)) := by
    refine le_of_eq_add (d := monus (Bk k) (succ (wit gB (Bk k) k))) ?_
    ipra_lc natEq (eq_add_of_le (Prf.andE₁ el))
  refine .andI ?_ (.andI hlow hup)
  refine le_antisymm ?_ hle
  refine .orE (zero_or_succ (wit gB (Bk k) k)) ?_ ?_
  · -- the witness is `0`: `N = 2`, and `k π(2) = k ≥ 2`
    let C : List (Fm PTm n) := (wit gB (Bk k) k ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] wit gB (Bk k) k ≐ zero := Prf.hyp0
    have eN : C ⊢[PRAAx] Ng k ≐ two := (congrAdd h0 (.eqRefl _)).eqTrans zero_two
    have eR : C ⊢[PRAAx] k * pc (Ng k) ≐ k :=
      (congrMul (.eqRefl _) ((congrPc eN).eqTrans pc_two)).eqTrans (mul_one_r k)
    exact le_congr eN.eqSymm eR.eqSymm hk2.wk
  · -- the witness is `j + 1`: minimality at `j`
    let C : List (Fm PTm n) := (wit gB (Bk k) k ≐ succ (pred (wit gB (Bk k) k))) :: Γ
    have hw : C ⊢[PRAAx] wit gB (Bk k) k ≐ succ (pred (wit gB (Bk k) k)) := Prf.hyp0
    have below : C ⊢[PRAAx] lt (pred (wit gB (Bk k) k)) (wit gB (Bk k) k) :=
      lt_congr (.eqRefl _) hw.eqSymm (le_refl (succ (pred (wit gB (Bk k) k))))
    have m := ex_least gB below
    rw [inst2_gB] at m
    have gt : C ⊢[PRAAx] le (succ (pred (wit gB (Bk k) k) + two))
        (k * pc (pred (wit gB (Bk k) k) + two)) := m
    have eS : C ⊢[PRAAx] succ (pred (wit gB (Bk k) k) + two) ≐ Ng k :=
      (succ_two _).eqTrans (congrAdd hw.eqSymm (.eqRefl _))
    have mono : C ⊢[PRAAx] le (pc (pred (wit gB (Bk k) k) + two)) (pc (Ng k)) :=
      pc_mono (le_congr (.eqRefl _) eS (le_succ_self _))
    exact le_congr eS (.eqRefl _) (le_trans gt (le_mul_mono (le_refl k) mono))

end LeanProofs.IPRA.AnalyticNumberTheory.GolombSolution
