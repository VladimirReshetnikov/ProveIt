import IPRADerivations.AnalyticNumberTheory.BlockFloor
import IPRADerivations.AnalyticNumberTheory.PNTStageStep
import IPRADerivations.Foundations.ProductSumDomination

/-!
# Truncating the excess sum of the Chebyshev block identity (`pnt_ipra_constructive_2026-11-14`, `con:signed`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, `sb:signed-integral`. In
`ChebyshevBlock.block_id` the excess `E_b(D) = Σ_{1≤n≤x} b(n)(⌊x/n⌋ ∸ D)` only has terms with `n ≤ P = ⌊x/D⌋`,
and there `⌊x/n⌋ ≥ D`, so

  `E_b(D) = Σ_{n≤P} b(n)⌊x/n⌋ − D Σ_{n≤P} b(n)`:

* `quo_le_of_gt`: `⌊x/k⌋ ≤ D` for `k ≥ ⌊x/D⌋ + 1`; `le_quo_of_le`: `D ≤ ⌊x/k⌋` for `1 ≤ k ≤ ⌊x/D⌋`;
* `e_trunc`: `E_b(D) = Σ_{n≤P} b(n)(⌊x/n⌋ ∸ D)`;
* `e_split`: `Σ_{n≤P} b(n)⌊x/n⌋ = Σ_{n≤P} b(n)(⌊x/n⌋ ∸ D) + Σ_{n≤P} D b(n)` (body `dB`);
* `d_lam`: `Σ_{n≤P} D Λ(n) = D ψ(P)`; `d_f`: `Σ_{n≤P} D F = D (F P)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockTrunc

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB inst2_LamB)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (sg_lam)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock (eB gB eB_at gB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFloor (lB fB lB_at fB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l congrSg)
open LeanProofs.IPRA.Foundations.ProductSumDomination (sum_trunc)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.Probability.Variance (sum_const_of)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `⌊x/k⌋ ≤ D` for `D ≥ 1` and `k ≥ ⌊x/D⌋ + 1`. -/
theorem quo_le_of_gt {x D k : PTm n} (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le (succ (quo x D)) k) :
    Γ ⊢[PRAAx] le (quo x k) D := by
  have hk1 : Γ ⊢[PRAAx] le one k := le_trans ((succ_monus_succ _ _).eqTrans (zero_le _)) hk
  have dD := div_mod_at (Γ := Γ) (x := x) (pos_of_one_le hD)
  have dk := div_mod_at (Γ := Γ) (x := x) (pos_of_one_le hk1)
  have e1 := natEq (Prf.andE₁ dD); have r1 := Prf.andE₂ dD
  have e2 := natEq (Prf.andE₁ dk)
  have m := le_scale D hk
  refine cancel_pos hk1 ?_
  ipra_le sl r1 + sl m + 𝔞 (rem x k) + 1 with e1 - e2

/-- `D ≤ ⌊x/k⌋` for `1 ≤ k ≤ ⌊x/D⌋`. -/
theorem le_quo_of_le {x D k : PTm n} (hk1 : Γ ⊢[PRAAx] le one k) (hk : Γ ⊢[PRAAx] le k (quo x D)) :
    Γ ⊢[PRAAx] le D (quo x k) := by
  refine le_quo_of_mul_le (pos_of_one_le hk1) ?_
  refine .orE (zero_or_succ D) ?_ ?_
  · have e := natEq (Prf.hyp0 : ((D ≐ zero) :: Γ) ⊢[PRAAx] D ≐ zero)
    ipra_le 𝔞 x with 𝔞 k * e
  · have dD := div_mod_at (Γ := ((D ≐ succ (pred D)) :: Γ)) (x := x) Prf.hyp0
    have e1 := natEq (Prf.andE₁ dD)
    have m := le_scale D (hk.wk (ψ := D ≐ succ (pred D)))
    ipra_le sl m + 𝔞 (rem x D) with e1

/-- `E_b(D) = Σ_{n≤⌊x/D⌋} b(n)(⌊x/n⌋ ∸ D)`. -/
theorem e_trunc (b : PTm 2) {x D z : PTm n} (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] ap2 (sumF (eB b)) (succ x) (pairT x (pairT D z)) ≐
      ap2 (sumF (eB b)) (succ (quo x D)) (pairT x (pairT D z)) := by
  have hD' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift, Syn.shift] using hD.shift
  have hP : Γ ⊢[PRAAx] le (succ (quo x D)) (succ x) := by
    have dD := div_mod_at (Γ := Γ) (x := x) (pos_of_one_le hD)
    have e1 := natEq (Prf.andE₁ dD)
    have w := natEq (eq_add_of_le hD)
    have l : Γ ⊢[PRAAx] le (quo x D) x := by
      ipra_le 𝔞 (quo x D) * 𝔞 (monus D one) + 𝔞 (rem x D) with e1 + 𝔞 (quo x D) * w
    exact (succ_monus_succ _ _).eqTrans l
  refine sum_trunc (eB b) hP (.allI (.impI (.impI ?_)))
  simp only [shift_pairT]
  have hv : (le (Syn.shift (succ (quo x D))) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (succ (quo (Syn.shift x) (Syn.shift D))) (var 0) := by
    have h0 : (le (Syn.shift (succ (quo x D))) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (Syn.shift (succ (quo x D))) (var 0) := Prf.hyp0
    have e : Syn.shift (succ (quo x D)) = succ (quo (Syn.shift x) (Syn.shift D)) := by simp [Syn.shift]
    rw [e] at h0 ⊢; exact h0
  have q := quo_le_of_gt hD'.wk.wk hv
  exact (eB_at _ _ _ _ _).eqTrans (congrMul (.eqRefl _) q |>.eqTrans (by apply deriveNat; ipra_simps; ring))

/-- `[n ≥ 1] D b(n)` over `0 = n`, `1 = (x, (D, z))`. -/
abbrev dB (b : PTm 2) : PTm 2 := fstT (sndT (var 1)) * (sg (var 0) * Syn.subst ![var 0, sndT (var 1)] b)

theorem dB_at (b : PTm 2) (k X D z : PTm n) :
    Γ ⊢[PRAAx] inst2 (dB b) k (pairT X (pairT D z)) ≐ D * (sg k * inst2 b k (pairT D z)) := by
  have h : Syn.subst ![k, pairT X (pairT D z)] (Syn.subst ![var 0, sndT (var 1)] b) =
      inst2 b k (sndT (pairT X (pairT D z))) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have raw : inst2 (dB b) k (pairT X (pairT D z)) =
      fstT (sndT (pairT X (pairT D z))) * (sg k * inst2 b k (sndT (pairT X (pairT D z)))) := by
    simp only [inst2, dB, PTm.subst_mul, h]; simp [sg]
  rw [raw]
  exact congrMul ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (congrMul (.eqRefl _) (congrInst2 b (.eqRefl _) (snd_pair _ _)))

theorem split_alg {s c q d D : PTm n} (h : Γ ⊢[PRAAx] q ≐ D + d) :
    Γ ⊢[PRAAx] (s * c) * q ≐ (s * c) * d + D * (s * c) := by
  have a := natEq h; apply deriveNat; ipra_simps; linear_combination 𝔞 s * 𝔞 c * a

theorem split_zero {s c q d D : PTm n} (h : Γ ⊢[PRAAx] s ≐ zero) :
    Γ ⊢[PRAAx] (s * c) * q ≐ (s * c) * d + D * (s * c) := by
  have a := natEq h; apply deriveNat; ipra_simps; linear_combination (𝔞 c * 𝔞 q - 𝔞 c * 𝔞 d - 𝔞 D * 𝔞 c) * a

/-- `Σ_{n≤P} b(n)⌊x/n⌋ = Σ_{n≤P} b(n)(⌊x/n⌋ ∸ D) + Σ_{n≤P} D b(n)`, `P = ⌊x/D⌋`. -/
theorem e_split (b : PTm 2) (x D z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (gB b)) (succ (quo x D)) (pairT x (pairT D z)) ≐
      ap2 (sumF (eB b)) (succ (quo x D)) (pairT x (pairT D z)) + ap2 (sumF (dB b)) (succ (quo x D)) (pairT x (pairT D z)) := by
  refine sum_add2 (eB b) (dB b) (gB b) (.allI (.impI ?_))
  simp only [shift_pairT]
  refine (gB_at _ _ _ _).eqTrans (.eqSymm ((congrAdd (eB_at _ _ _ _ _) (dB_at _ _ _ _ _)).eqTrans ?_))
  refine .eqSymm (.orE (zero_or_succ (var 0)) (split_zero ((congrSg Prf.hyp0).eqTrans sg_zero)) ?_)
  have hv : (lt (var 0) (Syn.shift (succ (quo x D))) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (var 0) (quo (Syn.shift x) (Syn.shift D)) := by
    have h0 : (lt (var 0) (Syn.shift (succ (quo x D))) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (Syn.shift (succ (quo x D))) := Prf.hyp0
    have e : Syn.shift (succ (quo x D)) = succ (quo (Syn.shift x) (Syn.shift D)) := by simp [Syn.shift]
    rw [e] at h0 ⊢; exact (succ_monus_succ _ _).eqSymm.eqTrans h0
  have hk1 : ((var 0 ≐ succ (pred (var 0))) :: lt (var 0) (Syn.shift (succ (quo x D))) :: Γ.map Fm.shift) ⊢[PRAAx]
      le one (var 0) := le_congr (.eqRefl _) Prf.hyp0.eqSymm ((succ_monus_succ _ _).eqTrans (zero_le _))
  have q := le_quo_of_le hk1 hv.wk
  exact split_alg (eq_add_of_le q)

/-- `Σ_{n≤P} D Λ(n) = D ψ(P)`. -/
theorem d_lam (N x D z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (dB lB)) (succ N) (pairT x (pairT D z)) ≐ D * Psi wt N z := by
  refine sum_scale (dB lB) (LamB wt) (succ N) D z (pairT x (pairT D z)) (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [inst2_LamB]
  exact (dB_at _ _ _ _ _).eqTrans (congrMul (.eqRefl _) ((congrMul (.eqRefl _) (lB_at _ _ _)).eqTrans (sg_lam _ _)))

/-- `Σ_{n≤P} D F = D (F P)`. -/
theorem d_f (N x D K L : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (dB fB)) (succ N) (pairT x (pairT D (pairT K (fact L)))) ≐ D * (fact L * N) := by
  refine (sum_shift _ _ _).eqTrans ?_
  have z0 : Γ ⊢[PRAAx] inst2 (dB fB) zero (pairT x (pairT D (pairT K (fact L)))) ≐ zero :=
    (dB_at _ _ _ _ _).eqTrans (by
      have s := natEq (sg_zero (Γ := Γ)); apply deriveNat; ipra_simps
      linear_combination 𝔞 D * 𝔞 (inst2 fB zero (pairT D (pairT K (fact L)))) * s)
  have c := sum_const_of (Γ := Γ) (shiftBody (dB fB)) N (D * fact L) (pairT x (pairT D (pairT K (fact L))))
    (.allI (.impI (by
      rw [inst2_shiftBody]
      simp only [shift_pairT, shift_fact']
      rw [show Syn.shift (D * fact L) = Syn.shift D * fact (Syn.shift L) by simp [Syn.shift]]
      refine (dB_at _ _ _ _ _).eqTrans ?_
      have s := natEq (sg_succ (Γ := (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)) (var 0))
      have f := natEq (fB_at (Γ := (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)) (succ (var 0)) (Syn.shift D)
        (Syn.shift K) (fact (Syn.shift L)))
      apply deriveNat; ipra_simps
      linear_combination 𝔞 (Syn.shift D) * 𝔞 (inst2 fB (succ (var 0)) (pairT (Syn.shift D)
        (pairT (Syn.shift K) (fact (Syn.shift L))))) * s + 𝔞 (Syn.shift D) * f)))
  refine (congrAdd z0 c).eqTrans ?_
  apply deriveNat; ipra_simps; ring

end LeanProofs.IPRA.AnalyticNumberTheory.BlockTrunc
