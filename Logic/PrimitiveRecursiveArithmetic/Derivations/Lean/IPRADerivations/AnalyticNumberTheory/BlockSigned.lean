import IPRADerivations.AnalyticNumberTheory.BlockTrunc
import IPRADerivations.AnalyticNumberTheory.LogRefinement
import IPRADerivations.AnalyticNumberTheory.ChebyshevAbel
import IPRADerivations.Core.Header

/-!
# The signed mean of the excess sums (`pnt_ipra_constructive_2026-11-14`, `con:signed`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, `sb:signed-integral`
(`|∫_a^b R(u)/u² du| ≤ 20`), which is `con:signed`. For the excess sums of `ChebyshevBlock.block_id`,
`E_Λ(D) = Σ_n Λ(n)(⌊x/n⌋ ∸ D)` and `E_F(D) = Σ_n F(⌊x/n⌋ ∸ D)` (`F = L!`, harmonic mesh `K`),

  `|E_Λ(D) − E_F(D)| ≤ 12 F x`  for `1 ≤ D ≤ x`, `P = ⌊x/D⌋ ≤ K`.

Since a block sum over divisors is `Σ_{D₁<d≤D₂} R(⌊x/d⌋) = (E_Λ(D₁) − E_F(D₁)) − (E_Λ(D₂) − E_F(D₂))`, every block
sum is at most `24 F x` in absolute value: the finite `con:signed`. The proof combines

* `BlockTrunc`: `Σ_{n≤P} Λ(n)⌊x/n⌋ = E_Λ(D) + D ψ(P)`, `Σ_{n≤P} F⌊x/n⌋ = E_F(D) + D F P` (`e_lam`, `e_f`);
* `BlockFloor`: those sums against `x A_1(P)` and `x F H_P` (`P!`-scaled);
* `HarmonicSignedMean.signed_upper`/`signed_lower` at `N = P`: `−6 ≤ A_1(P) − ψ(P)/P − λ_K(P) ≤ 5`;
* `log_pair` (`LogRefinement.log_refine` at `c₁ = 0`): `H_P − 1 ≤ λ_K(P) ≤ H_P`, i.e.
  `S(P) + S(K) ≤ S(KP) + F` and `S(KP) ≤ S(K) + S(P)`;
* `ChebyshevAbel.psi_k`: `ψ(P) ≤ 4PF`, and `x = DP + r`, `r < D`.

The two final certificates (`excess_upper`, `excess_lower`) were found by eliminating the equations in the order
`E_Λ, E_F, x, D` (exact rational elimination; residual zero).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockSigned

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda (Sw)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicSignedMean (signed_upper signed_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (log_refine quo_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel (psi_k pw_exp_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock (eB gB)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFloor (lB fB lam_sum_lo lam_sum_hi f_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTrunc (dB e_trunc e_split d_lam d_f)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `H_P − 1 ≤ λ_K(P) ≤ H_P`: `S(KP) ≤ S(K) + S(P)` and `S(P) + S(K) ≤ S(KP) + F`, `F = L!`. -/
theorem log_pair {P K L : PTm n} (hP1 : Γ ⊢[PRAAx] le one P) (hK1 : Γ ⊢[PRAAx] le one K)
    (hKP : Γ ⊢[PRAAx] le (K * P) L) :
    Γ ⊢[PRAAx] le (S (K * P) (fact L)) (S K (fact L) + S P (fact L)) ⋏
      le (S P (fact L) + S K (fact L)) (S (K * P) (fact L) + fact L) := by
  have hP' : Γ ⊢[PRAAx] P ≐ succ zero + pred P :=
    (pos_of_one_le hP1).eqTrans (by ipra_ring)
  have lr := log_refine (c₁ := zero) (T := pred P) (pos_of_one_le hK1)
    (le_congr (congrMul (.eqRefl K) hP') (.eqRefl L) hKP)
  have cP := natEq (congrAp2 (Γ := Γ) (sumF hB) hP'.eqSymm (.eqRefl (fact L)))
  have cKP := natEq (congrAp2 (Γ := Γ) (sumF hB) (congrMul (.eqRefl K) hP'.eqSymm) (.eqRefl (fact L)))
  have k1 : Γ ⊢[PRAAx] K * succ zero ≐ K := by ipra_ring
  have cK := natEq (congrAp2 (Γ := Γ) (sumF hB) k1 (.eqRefl (fact L)))
  have q1 : Γ ⊢[PRAAx] inst2 hB zero (fact L) ≐ fact L := by
    rw [inst2_h]
    exact quo_mul (congrSucc (pred_succ _).eqSymm) (by ipra_ring)
  have c1 := natEq ((sum_singleton hB (fact L)).eqTrans q1)
  have c0 := natEq (sum_zero (Γ := Γ) hB (fact L))
  have m := S_mono (Γ := Γ) (fact L) (le_of_eq_add (d := one) (b := P) (a := zero + pred P)
    (by have e := natEq hP'; apply deriveNat; ipra_simps; linear_combination e))
  refine .andI ?_ ?_
  · ipra_le sl (Prf.andE₂ lr) + sl m with cKP + c0 - cK
  · ipra_le sl (Prf.andE₁ lr) with cP + cK - cKP - c1

section Excess

variable {x D K L : PTm n} (hD1 : Γ ⊢[PRAAx] le one D) (hDx : Γ ⊢[PRAAx] le D x) (hK1 : Γ ⊢[PRAAx] le one K)
  (hPK : Γ ⊢[PRAAx] le (quo x D) K) (hNN : Γ ⊢[PRAAx] le (K * pw (quo x D) (quo x D)) L)
  (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)

/-- `Σ_{n≤P} Λ(n)⌊x/n⌋ = E_Λ(D) + D ψ(P)`. -/
theorem e_lam (z : PTm n) (hD1 : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] ap2 (sumF (gB lB)) (succ (quo x D)) (pairT x (pairT D z)) ≐
      ap2 (sumF (eB lB)) (succ x) (pairT x (pairT D z)) + D * Psi wt (quo x D) z :=
  (e_split lB x D z).eqTrans (congrAdd (e_trunc lB hD1).eqSymm (d_lam _ _ _ _))

/-- `Σ_{n≤P} F⌊x/n⌋ = E_F(D) + D F P`. -/
theorem e_f (hD1 : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] ap2 (sumF (gB fB)) (succ (quo x D)) (pairT x (pairT D (pairT K (fact L)))) ≐
      ap2 (sumF (eB fB)) (succ x) (pairT x (pairT D (pairT K (fact L)))) + D * (fact L * quo x D) :=
  (e_split fB x D _).eqTrans (congrAdd (e_trunc fB hD1).eqSymm (d_f _ _ _ _ _))

include hD1 hDx in
theorem p_pos : Γ ⊢[PRAAx] le one (quo x D) :=
  le_quo_of_mul_le (pos_of_one_le hD1) (le_congr (by ipra_ring) (.eqRefl _) hDx)

include hD1 in
theorem p_le_x : Γ ⊢[PRAAx] le (quo x D) x := by
  have dD := div_mod_at (Γ := Γ) (x := x) (pos_of_one_le hD1)
  have e1 := natEq (Prf.andE₁ dD)
  have w := natEq (eq_add_of_le hD1)
  ipra_le 𝔞 (quo x D) * 𝔞 (monus D one) + 𝔞 (rem x D) with e1 + 𝔞 (quo x D) * w

include hD1 hDx hK1 hPK hNN hKx hP

/-- `E_Λ(D) ≤ E_F(D) + 12 F x`. -/
theorem excess_upper :
    Γ ⊢[PRAAx] le (ap2 (sumF (eB lB)) (succ x) (pairT x (pairT D (pairT K (fact L)))))
      (ap2 (sumF (eB fB)) (succ x) (pairT x (pairT D (pairT K (fact L)))) + num 12 * (fact L * x)) := by
  have hP1 := p_pos hD1 hDx
  have hPx := p_le_x (x := x) hD1
  have hKP : Γ ⊢[PRAAx] le (K * quo x D) L := le_trans (le_scale K hPx) hKx
  have hPL : Γ ⊢[PRAAx] le (quo x D) L := by
    have w := natEq (eq_add_of_le hK1)
    exact le_trans (le_of_eq_add (d := monus K one * quo x D) (by apply deriveNat; ipra_simps; linear_combination 𝔞 (quo x D) * w)) hKP
  have h2 : Γ ⊢[PRAAx] le (K * pw two (two * (two * quo x D))) L :=
    le_trans (le_scale K (pw_exp_le (le_scale two (le_scale two hPx)))) hP
  have e1 := natEq (e_lam (Γ := Γ) (x := x) (pairT K (fact L)) hD1)
  have e2 := natEq (e_f (Γ := Γ) (x := x) (K := K) (L := L) hD1)
  have dD := div_mod_at (Γ := Γ) (x := x) (pos_of_one_le hD1)
  have e3 := natEq (Prf.andE₁ dD)
  have e4 := natEq (eq_add_of_le hD1)
  have b1 := lam_sum_lo (Γ := Γ) x (quo x D) D (pairT K (fact L))
  have su := signed_upper hP1 hK1 hNN h2
  have f2 := Prf.andE₂ (f_sum (Γ := Γ) (x := x) (D := D) (K := K) hPL)
  have kr := Prf.andE₁ (log_pair hP1 hK1 hKP)
  have ps := psi_k hK1 hP hPx
  have fp := natEq (Primes.fact_pos (Γ := Γ) (quo x D))
  have pw1 := natEq (eq_add_of_le hP1)
  refine cancel_pos (c := quo x D * fact (quo x D)) (by
    ipra_le 𝔞 (monus (quo x D) one) * 𝔞 (fact (quo x D)) + 𝔞 (pred (fact (quo x D))) with
      𝔞 (fact (quo x D)) * pw1 + fp) ?_
  ipra_le 𝔞 (quo x D) * sl b1 + 𝔞 x * sl su + 𝔞 (quo x D) * 𝔞 (fact (quo x D)) * sl f2 +
      𝔞 x * 𝔞 (quo x D) * 𝔞 (fact (quo x D)) * sl kr + 𝔞 (fact (quo x D)) * 𝔞 (rem x D) * sl ps +
      𝔞 (quo x D) * 𝔞 (fact (quo x D)) * 𝔞 (fact L) *
        (6 * 𝔞 (quo x D) * 𝔞 (monus D one) + 5 * 𝔞 (quo x D) + 3 * 𝔞 (rem x D)) with
    𝔞 (fact (quo x D)) * 𝔞 (quo x D) * e1 - 𝔞 (fact (quo x D)) * 𝔞 (quo x D) * e2 +
      𝔞 (fact (quo x D)) * (7 * 𝔞 (fact L) * 𝔞 (quo x D) - 𝔞 (Psi wt (quo x D) (pairT K (fact L)))) * e3 +
      6 * 𝔞 (fact L) * 𝔞 (fact (quo x D)) * 𝔞 (quo x D) * 𝔞 (quo x D) * e4

/-- `E_F(D) ≤ E_Λ(D) + 12 F x`. -/
theorem excess_lower :
    Γ ⊢[PRAAx] le (ap2 (sumF (eB fB)) (succ x) (pairT x (pairT D (pairT K (fact L)))))
      (ap2 (sumF (eB lB)) (succ x) (pairT x (pairT D (pairT K (fact L)))) + num 12 * (fact L * x)) := by
  have hP1 := p_pos hD1 hDx
  have hPx := p_le_x (x := x) hD1
  have hKP : Γ ⊢[PRAAx] le (K * quo x D) L := le_trans (le_scale K hPx) hKx
  have hPL : Γ ⊢[PRAAx] le (quo x D) L := by
    have w := natEq (eq_add_of_le hK1)
    exact le_trans (le_of_eq_add (d := monus K one * quo x D) (by apply deriveNat; ipra_simps; linear_combination 𝔞 (quo x D) * w)) hKP
  have h2 : Γ ⊢[PRAAx] le (K * pw two (two * (two * quo x D))) L :=
    le_trans (le_scale K (pw_exp_le (le_scale two (le_scale two hPx)))) hP
  have e1 := natEq (e_lam (Γ := Γ) (x := x) (pairT K (fact L)) hD1)
  have e2 := natEq (e_f (Γ := Γ) (x := x) (K := K) (L := L) hD1)
  have dD := div_mod_at (Γ := Γ) (x := x) (pos_of_one_le hD1)
  have e3 := natEq (Prf.andE₁ dD)
  have e4 := natEq (eq_add_of_le hD1)
  have b2 := lam_sum_hi (Γ := Γ) x (quo x D) D (pairT K (fact L))
  have sl' := signed_lower hP1 hK1 hPK hKP h2
  have f1 := Prf.andE₁ (f_sum (Γ := Γ) (x := x) (D := D) (K := K) hPL)
  have r1 := Prf.andE₂ (log_pair hP1 hK1 hKP)
  have ps := psi_k hK1 hP hPx
  have fp := natEq (Primes.fact_pos (Γ := Γ) (quo x D))
  have pw1 := natEq (eq_add_of_le hP1)
  refine cancel_pos (c := quo x D * fact (quo x D)) (by
    ipra_le 𝔞 (monus (quo x D) one) * 𝔞 (fact (quo x D)) + 𝔞 (pred (fact (quo x D))) with
      𝔞 (fact (quo x D)) * pw1 + fp) ?_
  ipra_le 𝔞 (quo x D) * sl b2 + 𝔞 x * sl sl' + 𝔞 (quo x D) * 𝔞 (fact (quo x D)) * sl f1 +
      𝔞 x * 𝔞 (quo x D) * 𝔞 (fact (quo x D)) * sl r1 + 𝔞 (quo x D) * 𝔞 (fact (quo x D)) * sl ps +
      𝔞 (fact (quo x D)) * 𝔞 (Psi wt (quo x D) (pairT K (fact L))) * 𝔞 (rem x D) +
      𝔞 (quo x D) * 𝔞 (fact (quo x D)) * 𝔞 D * 𝔞 (fact L) * 𝔞 (quo x D) +
      𝔞 (quo x D) * 𝔞 (fact (quo x D)) * 𝔞 (fact L) *
        (5 * 𝔞 (quo x D) * 𝔞 (monus D one) + 𝔞 (quo x D) + 5 * 𝔞 (rem x D)) with
    - (𝔞 (fact (quo x D)) * 𝔞 (quo x D) * e1) + 𝔞 (fact (quo x D)) * 𝔞 (quo x D) * e2 +
      𝔞 (fact (quo x D)) * (5 * 𝔞 (fact L) * 𝔞 (quo x D) + 𝔞 (Psi wt (quo x D) (pairT K (fact L)))) * e3 +
      5 * 𝔞 (fact L) * 𝔞 (fact (quo x D)) * 𝔞 (quo x D) * 𝔞 (quo x D) * e4

end Excess

end LeanProofs.IPRA.AnalyticNumberTheory.BlockSigned
