import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.Parity
import IPRADerivations.Core.LinearCombination

/-!
# Palindromic sums

If a body is symmetric on `[0, N)`, `t(N − 1 − k) = t(k)` for `k < N`, then

  `∑_{k<N} t(k) = 2 ∑_{k<⌊N/2⌋} t(k) + [N odd] · t(⌊N/2⌋)`.

With `h = half N` and `p = par N`, `N = 2h + p`: split the sum at `h + p` (`Core/SumSplit`), map the
upper part onto the lower part by the symmetry, and reflect it (`Core/SumReflect`).

* `sum_palindrome`: the identity, with the symmetry as a bounded universal hypothesis.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem subst_up_shift_pal {m k : ℕ} (σ : Fin m → PTm k) (t : PTm m) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

/-- The symmetry, instantiated: for `v < half N` and `j = half N ∸ (v + 1)`,
`t(half N + par N + v) = t(j)`. -/
theorem pal_pt (t : PTm 2) {N x v : PTm n} (hv : Γ ⊢[PRAAx] lt v (half N))
    (hsym : Γ ⊢[PRAAx] lt (monus (half N) (succ v)) N ⟶
      (inst2 t (monus N (succ (monus (half N) (succ v)))) x ≐ inst2 t (monus (half N) (succ v)) x)) :
    Γ ⊢[PRAAx] inst2 t (half N + par N + v) x ≐ inst2 t (monus (half N) (succ v)) x := by
  have e : Γ ⊢[PRAAx] N ≐ (half N + par N + v) + succ (monus (half N) (succ v)) := by
    ipra_lc natEq (half_par (Γ := Γ) N) + natEq (eq_add_of_le hv)
  have mN : Γ ⊢[PRAAx] monus N (succ (monus (half N) (succ v))) ≐ half N + par N + v :=
    (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  have lj : Γ ⊢[PRAAx] lt (monus (half N) (succ v)) N :=
    le_of_eq_add (e.eqTrans (add_comm _ _))
  exact (congrInst2 t mN.eqSymm (.eqRefl _)).eqTrans (.impE hsym lj)

/-- `∑_{k<h+p} t = ∑_{k<h} t + p · t(h)` for a parity bit `p`. -/
theorem sum_half_par (t : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF t) (half N + par N) x ≐ ap2 (sumF t) (half N) x + par N * inst2 t (half N) x := by
  refine .orE (par_cases N) ?_ ?_
  · have p : ((par N ≐ zero) :: Γ) ⊢[PRAAx] par N ≐ zero := Prf.hyp0
    refine (congrAp2 (sumF t) ((congrAdd (.eqRefl _) p).eqTrans (add_zero _)) (.eqRefl _)).eqTrans ?_
    exact (add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) ((congrMul p (.eqRefl _)).eqTrans (zero_mul _)).eqSymm)
  · have p : ((par N ≐ one) :: Γ) ⊢[PRAAx] par N ≐ one := Prf.hyp0
    have e : ((par N ≐ one) :: Γ) ⊢[PRAAx] half N + par N ≐ succ (half N) :=
      (congrAdd (.eqRefl _) p).eqTrans (succ_eq_add_one _).eqSymm
    refine (congrAp2 (sumF t) e (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
    exact congrAdd (.eqRefl _) ((one_mul _).eqSymm.eqTrans (congrMul p.eqSymm (.eqRefl _)))

/-- Palindromic sums: if `t(N − 1 − k) = t(k)` for `k < N`, then
`∑_{k<N} t(k) = 2 ∑_{k<⌊N/2⌋} t(k) + [N odd] t(⌊N/2⌋)`. -/
theorem sum_palindrome (t : PTm 2) (N x : PTm n)
    (hs : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 t (monus (Syn.shift N) (succ (var 0))) (Syn.shift x) ≐ inst2 t (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF t) N x ≐ two * ap2 (sumF t) (half N) x + par N * inst2 t (half N) x := by
  have eN : Γ ⊢[PRAAx] N ≐ (half N + par N) + half N := by
    have a := natEq (half_par (Γ := Γ) N)
    apply deriveNat; ipra_simps
    linear_combination a
  have up : Γ ⊢[PRAAx] ap2 (sumF (offB t)) (half N) (pairT (half N + par N) x) ≐
      ap2 (sumF (rflBody t)) (half N) (pairT (half N) x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have e₁ : Syn.shift (pairT (half N + par N) x) = pairT (half (Syn.shift N) + par (Syn.shift N)) (Syn.shift x) := by
      simp [Syn.shift]
    have e₂ : Syn.shift (pairT (half N) x) = pairT (half (Syn.shift N)) (Syn.shift x) := by simp [Syn.shift]
    have e₃ : Syn.shift (half N) = half (Syn.shift N) := by simp [Syn.shift]
    rw [e₁, e₂, inst2_offB, inst2_rflBody]
    rw [e₃] at *
    have hsym : (lt (var 0) (half (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (monus (half (Syn.shift N)) (succ (var 0))) (Syn.shift N) ⟶
          (inst2 t (monus (Syn.shift N) (succ (monus (half (Syn.shift N)) (succ (var 0))))) (Syn.shift x) ≐
            inst2 t (monus (half (Syn.shift N)) (succ (var 0))) (Syn.shift x)) := by
      have a := Prf.allE (monus (half (Syn.shift N)) (succ (var 0))) hs.shift
      simp only [Fm.shift, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst2, PTm.subst_monus,
        ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero, Syn.inst_zero, subst_up_shift_pal,
        Syn.subst_inst_shift] at a
      exact a.wk
    refine (congrInst2 t (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
      ((pal_pt t Prf.hyp0 hsym).eqTrans ?_)
    exact congrInst2 t (congrMonus (fst_pair _ _) (.eqRefl _)).eqSymm (snd_pair _ _).eqSymm
  ipra_lc natEq ((congrAp2 (sumF t) eN (.eqRefl x)).eqTrans (sum_split t (half N + par N) (half N) x)) +
    natEq (sum_half_par (Γ := Γ) t N x) + natEq up - natEq (sum_reflect (Γ := Γ) t (half N) x)

end LeanProofs.IPRA
