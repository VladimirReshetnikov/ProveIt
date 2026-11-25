import IPRADerivations.Combinatorics.CatalanPowers
import IPRADerivations.Combinatorics.CatalanExtensions
import IPRADerivations.Foundations.ShiftedInduction
import IPRADerivations.Core.CertificateTactics

/-!
# The `k`-fold Catalan convolution

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Section 7, (7.3):

"`Σ_{i_1 + ⋯ + i_k = n} Cat_{i_1} ⋯ Cat_{i_k} = (k/(2n + k)) C(2n + k, n)`. The internal theorem
is `(2n + k)` times the left side equals `k C(2n + k, n)`."

The left side is the iterated convolution `T(k, n)` of `Combinatorics/CatalanPowers`
(`T(0, n) = [n = 0]`, `T(k + 1, n) = Σ_{i ≤ n} Cat_i T(k, n − i)`).

* `kfold`: `(2n + k) T(k, n) = k C(2n + k, n)` for all `k`, `n`;
* `kfold_closed`: the same as a closed sentence.

The packet proves (7.3) by the Raney form of the cycle lemma on Polish codes of forests, and
notes that it is also Lagrange inversion for `C(x)^k`. The derivation here is the coefficient
form of `C^{k+2} = (C^{k+1} − C^k)/x`: with `A(k, n) = (2n + k) T(k, n)` and
`B(k, n) = k C(2n + k, n)`,

* `kfold_zero`, `kfold_one`: `A = B` for `k = 0` (both sides vanish) and `k = 1` (the ballot
  identity (7.1), `Combinatorics/CatalanExtensions.ballot`);
* `kfold_step`: `A = B` at `(k, n + 1)` and `(k + 1, n + 1)` gives `A = B` at `(k + 2, n)`, from
  `CatalanPowers.T_rec`, Pascal's rule and the ratio `(N − n) C(N, n) = (n + 1) C(N, n + 1)`;
* the induction on `k` uses the hypothesis at the shifted parameter `n + 1`, and is
  `Foundations/ShiftedInduction.shifted_induction` applied to the pair
  `⟨A(k, n), A(k + 1, n)⟩ = ⟨B(k, n), B(k + 1, n)⟩`.

Not derived: the bijection with forests and the cycle lemma.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanKFold

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel pascal_at)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Catalan (cat)
open LeanProofs.IPRA.Combinatorics.CatalanBallot (binom_ratio)
open LeanProofs.IPRA.Combinatorics.CatalanExtensions (ballot)
open LeanProofs.IPRA.Combinatorics.CatalanPowers (T T_zero T_one T_rec)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (pair_congr)
open LeanProofs.IPRA.Foundations.ShiftedInduction (shifted_induction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(2m + k) T(k, m)`. -/
abbrev A (k m : PTm n) : PTm n := (two * m + k) * T k m
/-- `k C(2m + k, m)`. -/
abbrev B (k m : PTm n) : PTm n := k * binom (two * m + k) m

/-! ## The rows `k = 0` and `k = 1` -/

theorem mul_compl (m : PTm n) : Γ ⊢[PRAAx] m * monus one m ≐ zero := by
  refine .orE (zero_or_succ m) ?_ ?_
  · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
  · exact (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans
      ((succ_monus_succ _ _).eqTrans (zero_monus _)))).eqTrans (mul_zero _)

theorem kfold_zero (m : PTm n) : Γ ⊢[PRAAx] A zero m ≐ B zero m := by
  ipra_lc (2 * 𝔞 m) * natEq (T_zero (Γ := Γ) m) + 2 * natEq (mul_compl (Γ := Γ) m)

theorem kfold_one (m : PTm n) : Γ ⊢[PRAAx] A (succ zero) m ≐ B (succ zero) m := by
  ipra_lc (2 * 𝔞 m + 1) * natEq (T_one (Γ := Γ) m) -
    natEq ((congrBinom (a := two * m + succ zero) (a' := succ (two * m)) (by ipra_ring) (.eqRefl m)).eqTrans (ballot (Γ := Γ) m))

/-! ## The step -/

/-- From `(k, m + 1)` and `(k + 1, m + 1)` to `(k + 2, m)`. -/
theorem kfold_step {k m : PTm n} (h0 : Γ ⊢[PRAAx] A k (succ m) ≐ B k (succ m))
    (h1 : Γ ⊢[PRAAx] A (succ k) (succ m) ≐ B (succ k) (succ m)) :
    Γ ⊢[PRAAx] A (succ (succ k)) m ≐ B (succ (succ k)) m := by
  -- `N = 2m + k + 2`
  have hlt : Γ ⊢[PRAAx] lt m (two * m + succ (succ k)) :=
    le_of_eq_add (d := m + succ k) (by ipra_ring)
  have mN : Γ ⊢[PRAAx] monus (two * m + succ (succ k)) m ≐ m + succ (succ k) :=
    (congrMonus (by ipra_ring :
      Γ ⊢[PRAAx] two * m + succ (succ k) ≐ (m + succ (succ k)) + m) (.eqRefl _)).eqTrans
      (add_monus _ _)
  have e0 := natEq (h0.eqTrans (congrMul (.eqRefl _) (congrBinom
    (by ipra_ring :
      Γ ⊢[PRAAx] two * succ m + k ≐ two * m + succ (succ k)) (.eqRefl _))))
  have e1 := natEq (h1.eqTrans (congrMul (.eqRefl _) (congrBinom
    (by ipra_ring :
      Γ ⊢[PRAAx] two * succ m + succ k ≐ succ (two * m + succ (succ k))) (.eqRefl _))))
  refine mul_cancel (D := succ (two * m + succ (succ k))) (congrSucc (pred_succ _).eqSymm) ?_
  ipra_lc (-(2 * 𝔞 m + 𝔞 k + 3) * (2 * 𝔞 m + 𝔞 k + 2)) * natEq (T_rec (Γ := Γ) k m) + (2 * 𝔞 m + 𝔞 k + 2) * e1 -
    (2 * 𝔞 m + 𝔞 k + 3) * e0 + ((2 * 𝔞 m + 𝔞 k + 2) * (𝔞 k + 1)) * natEq (pascal_at hlt) -
    2 * natEq ((congrMul mN.eqSymm (.eqRefl _)).eqTrans (binom_ratio hlt))

/-! ## The induction with a shifting parameter -/

theorem pair_fst {a b c d : PTm n} (h : Γ ⊢[PRAAx] pairT a b ≐ pairT c d) : Γ ⊢[PRAAx] a ≐ c :=
  (fst_pair a b).eqSymm.eqTrans ((congrFst h).eqTrans (fst_pair c d))

theorem pair_snd {a b c d : PTm n} (h : Γ ⊢[PRAAx] pairT a b ≐ pairT c d) : Γ ⊢[PRAAx] b ≐ d :=
  (snd_pair a b).eqSymm.eqTrans ((congrSnd h).eqTrans (snd_pair c d))

/-- The statement at `(k, m)` and `(k + 1, m)`, as one equation. -/
abbrev Pk (k m : PTm n) : Fm PTm n :=
  pairT (A k m) (A (succ k) m) ≐ pairT (B k m) (B (succ k) m)

theorem kfold_imp (k m : PTm n) : Γ ⊢[PRAAx] Pk k m ⟶ (Pk k (succ m) ⟶ Pk (succ k) m) := by
  refine .impI (.impI ?_)
  have h2 : (Pk k (succ m) :: Pk k m :: Γ) ⊢[PRAAx] Pk k (succ m) := Prf.hyp0
  have h1 : (Pk k (succ m) :: Pk k m :: Γ) ⊢[PRAAx] Pk k m :=
    (Prf.hyp0 (Γ := Γ) (φ := Pk k m)).wk
  exact pair_congr (pair_snd h1) (kfold_step (pair_fst h2) (pair_snd h2))

/-- Variables `0 = k`, `1 = m`, `2` unused. -/
abbrev kL : PTm 3 := pairT (A (var 0) (var 1)) (A (succ (var 0)) (var 1))
abbrev kR : PTm 3 := pairT (B (var 0) (var 1)) (B (succ (var 0)) (var 1))

theorem inst3_kL (k m x : PTm n) : inst3 kL k m x = pairT (A k m) (A (succ k) m) := by
  simp [inst3]

theorem inst3_kR (k m x : PTm n) : inst3 kR k m x = pairT (B k m) (B (succ k) m) := by
  simp [inst3]

theorem kfold_pair (k m : PTm n) : Γ ⊢[PRAAx] Pk k m := by
  have hb : ([] : List (Fm PTm 2)) ⊢[PRAAx]
      inst3 kL zero (var 0) (var 1) ≐ inst3 kR zero (var 0) (var 1) := by
    rw [inst3_kL, inst3_kR]
    exact pair_congr (kfold_zero _) (kfold_one _)
  have hs : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      (inst3 kL (var 0) (var 1) (var 2) ≐ inst3 kR (var 0) (var 1) (var 2)) ⟶
      ((inst3 kL (var 0) (succ (var 1)) (var 2) ≐ inst3 kR (var 0) (succ (var 1)) (var 2)) ⟶
        (inst3 kL (succ (var 0)) (var 1) (var 2) ≐ inst3 kR (succ (var 0)) (var 1) (var 2))) := by
    simp only [inst3_kL, inst3_kR]
    exact kfold_imp (var 0) (var 1)
  have h := shifted_induction (Γ := Γ) (L := kL) (R := kR) hb hs k m zero
  rw [inst3_kL, inst3_kR] at h
  exact h

/-- (7.3): `(2m + k) · Σ_{i_1 + ⋯ + i_k = m} Cat_{i_1} ⋯ Cat_{i_k} = k C(2m + k, m)`. -/
theorem kfold (k m : PTm n) : Γ ⊢[PRAAx] (two * m + k) * T k m ≐ k * binom (two * m + k) m :=
  pair_fst (kfold_pair k m)

/-- (7.3) as a closed sentence; variables `0 = k`, `1 = m`. -/
theorem kfold_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((two * var 1 + var 0) * T (var 0) (var 1) ≐ var 0 * binom (two * var 1 + var 0) (var 1)) :=
  closeUniv 2 (kfold _ _)

end LeanProofs.IPRA.Combinatorics.CatalanKFold
