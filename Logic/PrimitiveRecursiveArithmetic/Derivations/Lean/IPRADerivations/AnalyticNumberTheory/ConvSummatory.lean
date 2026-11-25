import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.SummatoryPhi
import IPRADerivations.Core.LinearCombination

/-!
# The summatory function of a Dirichlet convolution (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
"For each `d ≤ x`, apply (sb:comparison-error) at `y = x/d`. Since `|μ(d)| ≤ 1`, reversing finite sums gives …".
The reversal is the hyperbola-free swap of a convolution's summatory function, proved here for any two bodies
`a, b` with a common parameter `y`:

  `Σ_{n≤x} (a * b)(n, y) = Σ_{1≤d≤x} a(d, y) B(⌊x/d⌋, y)`,   `B(m, y) = Σ_{1≤k≤m} b(k, y)`   (`conv_summatory`).

The proof is one QF induction on `x`: the step `⌊(x+1)/d⌋ = ⌊x/d⌋ + [d ∣ x+1]` (`SummatoryPhi.quo_succ`) adds
exactly the terms `a(d) b((x+1)/d)` of `(a * b)(x+1)` (`row_step`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi (quo_lt_self)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Summatory

variable (a b : PTm 2)

/-- `b(k + 1, y)`. -/
def bS : PTm 2 := Syn.subst ![succ (var 0), var 1] b

theorem inst2_bS (k y : PTm n) : inst2 (bS b) k y = inst2 b (succ k) y := by
  simp only [inst2, bS, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

/-- `B(m, y) = Σ_{k<m} b(k + 1, y)`. -/
abbrev Bs (m y : PTm n) : PTm n := ap2 (sumF (bS b)) m y

/-- `[d ≥ 1] a(d, y) B(⌊x/d⌋, y)` with `z = (x, y)`. -/
def RB : PTm 2 := (sg (var 0) * Syn.subst ![var 0, sndT (var 1)] a) *
  ap2 (sumF (bS b)) (quo (fstT (var 1)) (var 0)) (sndT (var 1))

theorem inst2_RB (d z : PTm n) :
    inst2 (RB a b) d z = (sg d * inst2 a d (sndT z)) * Bs b (quo (fstT z) d) (sndT z) := by
  have ha : Syn.subst ![d, z] (Syn.subst ![var 0, sndT (var 1)] a) = inst2 a d (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  simp only [inst2, RB, PTm.subst_mul, ha]
  simp

theorem RB_at (d X y : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB a b) d (pairT X y) ≐ (sg d * inst2 a d y) * Bs b (quo X d) y := by
  rw [inst2_RB]
  exact congrMul (congrMul (.eqRefl _) (congrInst2 a (.eqRefl _) (snd_pair _ _)))
    (congrAp2 _ (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

/-- The pointwise step: `a(d) B(⌊(x+1)/d⌋) = a(d) B(⌊x/d⌋) + [d ∣ x+1] a(d) b((x+1)/d)`. -/
theorem row_step (d x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB a b) d (pairT (succ x) y) ≐
      inst2 (RB a b) d (pairT x y) + inst2 (cvB a b) d (pairT (succ x) y) := by
  refine (RB_at a b _ _ _).eqTrans (.eqTrans ?_ (congrAdd (RB_at a b _ _ _) (cv_at _ _ _ _ _)).eqSymm)
  refine .orE (zero_or_succ d) ?_ ?_
  · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    ipra_lc (𝔞 (inst2 a d y) * 𝔞 (Bs b (quo (succ x) d) y) - 𝔞 (inst2 a d y) * 𝔞 (Bs b (quo x d) y) - 𝔞 (eqb (rem (succ x) d) zero) * 𝔞 (inst2 a d y) * 𝔞 (inst2 b (quo (succ x) d) y)) * natEq s0
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have q := LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi.quo_succ (N := x) hd
    refine .orE (eq_or_ne (rem (succ x) d) zero) ?_ ?_
    · let D : List (Fm PTm n) := (rem (succ x) d ≐ zero) :: C
      have e1 : D ⊢[PRAAx] eqb (rem (succ x) d) zero ≐ one := eqb_of_eq Prf.hyp0
      have qs : D ⊢[PRAAx] quo (succ x) d ≐ succ (quo x d) :=
        q.wk.eqTrans ((congrAdd (.eqRefl _) e1).eqTrans (by ipra_ring))
      have bs : D ⊢[PRAAx] Bs b (quo (succ x) d) y ≐ Bs b (quo x d) y + inst2 b (succ (quo x d)) y := by
        refine (congrAp2 _ qs (.eqRefl _)).eqTrans ?_
        have s := sum_succ' (Γ := D) (bS b) (quo x d) y
        rw [inst2_bS] at s
        exact s
      have bq : D ⊢[PRAAx] inst2 b (quo (succ x) d) y ≐ inst2 b (succ (quo x d)) y := congrInst2 b qs (.eqRefl _)
      have w1 := natEq bs; have w2 := natEq bq; have w3 := natEq e1
      apply deriveNat; ipra_simps
      linear_combination 𝔞 (sg d) * 𝔞 (inst2 a d y) * w1 -
        𝔞 (sg d) * 𝔞 (eqb (rem (succ x) d) zero) * 𝔞 (inst2 a d y) * w2 -
        𝔞 (sg d) * 𝔞 (inst2 a d y) * 𝔞 (inst2 b (succ (quo x d)) y) * w3
    · let D : List (Fm PTm n) := neg (rem (succ x) d ≐ zero) :: C
      have e0 : D ⊢[PRAAx] eqb (rem (succ x) d) zero ≐ zero := eqb_of_ne Prf.hyp0
      have qs : D ⊢[PRAAx] quo (succ x) d ≐ quo x d :=
        q.wk.eqTrans ((congrAdd (.eqRefl _) e0).eqTrans (add_zero _))
      have bs : D ⊢[PRAAx] Bs b (quo (succ x) d) y ≐ Bs b (quo x d) y := congrAp2 _ qs (.eqRefl _)
      have w1 := natEq bs; have w3 := natEq e0
      apply deriveNat; ipra_simps
      linear_combination 𝔞 (sg d) * 𝔞 (inst2 a d y) * w1 -
        𝔞 (sg d) * 𝔞 (inst2 a d y) * 𝔞 (inst2 b (quo (succ x) d) y) * w3

/-- Variables `0 = x`, `1 = y`. -/
private abbrev csF : Fm PTm 2 :=
  ap2 (sumF (cvF a b)) (succ (var 0)) (var 1) ≐ ap2 (sumF (RB a b)) (succ (var 0)) (pairT (var 0) (var 1))

theorem shift_succ_x (x : PTm n) : Syn.shift (succ x) = succ (Syn.shift x) := by simp [Syn.shift]

/-- The step `x → x + 1` of `conv_summatory`. -/
theorem cs_step (x y : PTm n)
    (ih : Γ ⊢[PRAAx] ap2 (sumF (cvF a b)) (succ x) y ≐ ap2 (sumF (RB a b)) (succ x) (pairT x y)) :
    Γ ⊢[PRAAx] ap2 (sumF (cvF a b)) (succ (succ x)) y ≐
      ap2 (sumF (RB a b)) (succ (succ x)) (pairT (succ x) y) := by
  have l := sum_succ' (Γ := Γ) (cvF a b) (succ x) y
  rw [inst2_cvF] at l
  have s := sum_add2 (Γ := Γ) (RB a b) (cvB a b) (RB a b) (K := succ (succ x)) (x := pairT x y)
    (x' := pairT (succ x) y) (z := pairT (succ x) y) (.allI (.impI (by
      simp only [shift_pairT]
      rw [shift_succ_x]
      exact row_step a b _ _ _)))
  have r := sum_succ' (Γ := Γ) (RB a b) (succ x) (pairT x y)
  have z : Γ ⊢[PRAAx] inst2 (RB a b) (succ x) (pairT x y) ≐ zero :=
    (RB_at a b _ _ _).eqTrans ((congrMul (.eqRefl _) ((congrAp2 _ (quo_lt_self x) (.eqRefl _)).eqTrans
      (sum_zero _ _))).eqTrans (mul_zero _))
  ipra_lc natEq l + natEq ih - natEq s - natEq r - natEq z

private theorem cs₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] csF a b := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have l := sum_succ' (Γ := ([] : List (Fm PTm 1))) (cvF a b) zero (var 0)
    rw [inst2_cvF] at l
    have l0 := sum_zero (Γ := ([] : List (Fm PTm 1))) (cvF a b) (var 0)
    have c := sum_succ' (Γ := ([] : List (Fm PTm 1))) (cvB a b) zero (pairT zero (var 0))
    have c0 := sum_zero (Γ := ([] : List (Fm PTm 1))) (cvB a b) (pairT zero (var 0))
    have cz : ([] : List (Fm PTm 1)) ⊢[PRAAx] inst2 (cvB a b) zero (pairT zero (var 0)) ≐ zero :=
      (cv_at _ _ _ _ _).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)
    have r := sum_succ' (Γ := ([] : List (Fm PTm 1))) (RB a b) zero (pairT zero (var 0))
    have r0 := sum_zero (Γ := ([] : List (Fm PTm 1))) (RB a b) (pairT zero (var 0))
    have rz : ([] : List (Fm PTm 1)) ⊢[PRAAx] inst2 (RB a b) zero (pairT zero (var 0)) ≐ zero :=
      (RB_at a b _ _ _).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)
    ipra_lc natEq l + natEq l0 + natEq c + natEq c0 + natEq cz - natEq r - natEq r0 - natEq rz
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact cs_step a b _ _ Prf.hyp0

/-- The summatory function of a convolution:
`Σ_{n≤x} (a * b)(n, y) = Σ_{1≤d≤x} a(d, y) B(⌊x/d⌋, y)` with `B(m, y) = Σ_{1≤k≤m} b(k, y)`. -/
theorem conv_summatory (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (cvF a b)) (succ x) y ≐ ap2 (sumF (RB a b)) (succ x) (pairT x y) := by
  have i := inst (Γ := Γ) (cs₀ a b) (![x, y] : Fin 2 → PTm n)
  simpa using i

end Summatory

end LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory
