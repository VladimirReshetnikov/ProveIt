import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.LinearCombination

/-!
# The binomial theorem

`∑_{k ≤ m} C(m, k) aᵏ = (a + 1)ᵐ`.

Bounded sums take one parameter, so the body reads `m` and `a` from the pair
`x = ⟨m, a⟩`: the summand is `C(fst x, k) · (snd x)ᵏ`. The induction on `m` follows
`binom_sum_open`: shift the index, apply Pascal's rule below the top term, and split the
sum, with one new step that pulls the factor `snd x = a` out of a sum.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BinomialTheorem

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self' pascal_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem congrBinom {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] binom a b ≐ binom a' b' := by
  have h := Prf.eqCongr (Γ := Γ) (binom (var 0) (var 1) : PTm 2) (σ := ![a, b]) (σ' := ![a', b'])
    (fun j => by fin_cases j <;> assumption)
  simpa using h

theorem congrPw {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] pw a b ≐ pw a' b' := congrAp2 powF h₂ h₁

/-! ## Bodies; variables `0 = k`, `1 = x` -/

/-- `C(fst x, k) (snd x)ᵏ`. -/
abbrev tBody : PTm 2 := binom (fstT (var 1)) (var 0) * pw (sndT (var 1)) (var 0)
/-- `snd x · C(fst x, k) (snd x)ᵏ`. -/
abbrev aBody : PTm 2 := sndT (var 1) * tBody
abbrev hBody : PTm 2 := addBody aBody (shiftBody tBody)

theorem inst2_t (k x : PTm n) : inst2 tBody k x = binom (fstT x) k * pw (sndT x) k := by
  simp [inst2]
theorem inst2_a (k x : PTm n) : inst2 aBody k x = sndT x * (binom (fstT x) k * pw (sndT x) k) := by
  simp [inst2]
theorem inst2_s (k x : PTm n) :
    inst2 (shiftBody tBody) k x = binom (fstT x) (succ k) * pw (sndT x) (succ k) := by
  rw [inst2_shiftBody, inst2_t]
theorem inst2_h (k x : PTm n) : inst2 hBody k x =
    sndT x * (binom (fstT x) k * pw (sndT x) k) + binom (fstT x) (succ k) * pw (sndT x) (succ k) := by
  rw [inst2_addBody, inst2_a, inst2_s]

/-! ## Pulling out the factor `snd x` -/

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev mulF (f : PTm 2) : Fm PTm 2 :=
  ap2 (sumF (sndT (var 1) * f)) (var 0) (var 1) ≐ sndT (var 1) * ap2 (sumF f) (var 0) (var 1)

private theorem sum_mul_snd₀ (f : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] mulF f := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_sndT, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero]
    exact (sum_zero _ _).eqTrans ((mul_zero _).eqSymm.eqTrans (congrMul (.eqRefl _) (sum_zero _ _).eqSymm))
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_sndT, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have e : inst2 (sndT (var 1) * f) (var 0 : PTm 2) (var 1) = sndT (var 1) * inst2 f (var 0) (var 1) := by
      simp [inst2]
    refine (sum_succ' _ (var 0) (var 1)).eqTrans ?_
    rw [e]
    refine withEq Prf.hyp0 fun e₁ => withEq (sum_succ' f (var 0) (var 1)) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

theorem sum_mul_snd (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (sndT (var 1) * f)) N x ≐ sndT x * ap2 (sumF f) N x := by
  have h := inst (Γ := Γ) (sum_mul_snd₀ f) (![N, x] : Fin 2 → PTm n)
  simpa using h

/-! ## The theorem -/

/-- `∑_{k ≤ m} C(m, k) aᵏ = (a + 1)ᵐ`, with the summand reading `m, a` from `⟨m, a⟩`;
variables `0 = m`, `1 = a`. -/
abbrev binomThmFormula : Fm PTm 2 :=
  ap2 (sumF tBody) (succ (var 0)) (pairT (var 0) (var 1)) ≐ pw (succ (var 1)) (var 0)

theorem binomial_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] binomThmFormula := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine (sum_succ' tBody zero _).eqTrans ?_
    rw [inst2_t]
    refine withEq (sum_zero (Γ := []) tBody (pairT zero (var 0))) fun e₁ =>
      withEq (binom_zero' (Γ := []) (fstT (pairT (zero : PTm 1) (var 0)))) fun e₂ =>
      withEq (pw_zero (Γ := []) (sndT (pairT (zero : PTm 1) (var 0)))) fun e₃ =>
      withEq (pw_zero (Γ := []) (succ (var 0) : PTm 1)) fun e₄ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₃, e₄]; ring
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    -- `X = ⟨m, a⟩`, `X' = ⟨m + 1, a⟩`.
    generalize hΓ : ([binomThmFormula] : List (Fm PTm 2)) = Γ₀
    have ih : Γ₀ ⊢[PRAAx] binomThmFormula := hΓ ▸ Prf.hyp0
    have fX := fst_pair (Γ := Γ₀) (var 0 : PTm 2) (var 1)
    have sX := snd_pair (Γ := Γ₀) (var 0 : PTm 2) (var 1)
    have fX' := fst_pair (Γ := Γ₀) (succ (var 0) : PTm 2) (var 1)
    have sX' := snd_pair (Γ := Γ₀) (succ (var 0) : PTm 2) (var 1)
    -- E0: the shifted sum.
    have E0 := sum_shift (Γ := Γ₀) tBody (succ (var 0)) (pairT (succ (var 0)) (var 1))
    rw [inst2_t] at E0
    have T0 := (congrMul (binom_zero' (Γ := Γ₀) (fstT (pairT (succ (var 0)) (var 1))))
      (pw_zero (Γ := Γ₀) (sndT (pairT (succ (var 0)) (var 1)))))
    -- E1: the top term of the shifted sum.
    have E1 := sum_succ' (Γ := Γ₀) (shiftBody tBody) (var 0) (pairT (succ (var 0)) (var 1))
    rw [inst2_s] at E1
    have T1 := congrMul ((congrBinom fX' (.eqRefl _)).eqTrans (binom_self' _))
      (congrPw sX' (.eqRefl (succ (var 0) : PTm 2)))
    -- E2: Pascal's rule below the top.
    have E2 : Γ₀ ⊢[PRAAx] ap2 (sumF (shiftBody tBody)) (var 0) (pairT (succ (var 0)) (var 1)) ≐
        ap2 (sumF hBody) (var 0) (pairT (var 0) (var 1)) := by
      refine sum_congr_bounded _ _ _ _ _ (.allI ?_)
      simp only [inst2_s, inst2_h, Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_succ, Syn.subst_var]
      refine .impI ?_
      have p := pascal_at (Prf.hyp0 : (lt (var 0) (var (Fin.succ 0)) :: Γ₀.map Fm.shift) ⊢[PRAAx] _)
      have f₁ := fst_pair (Γ := lt (var 0) (var (Fin.succ 0)) :: Γ₀.map Fm.shift)
        (succ (var (Fin.succ 0)) : PTm 3) (var (Fin.succ 1))
      have f₂ := fst_pair (Γ := lt (var 0) (var (Fin.succ 0)) :: Γ₀.map Fm.shift)
        (var (Fin.succ 0) : PTm 3) (var (Fin.succ 1))
      have s₁ := snd_pair (Γ := lt (var 0) (var (Fin.succ 0)) :: Γ₀.map Fm.shift)
        (succ (var (Fin.succ 0)) : PTm 3) (var (Fin.succ 1))
      have s₂ := snd_pair (Γ := lt (var 0) (var (Fin.succ 0)) :: Γ₀.map Fm.shift)
        (var (Fin.succ 0) : PTm 3) (var (Fin.succ 1))
      refine (congrMul ((congrBinom f₁ (.eqRefl _)).eqTrans p) (congrPw s₁ (.eqRefl _))).eqTrans ?_
      refine .eqTrans ?_ (congrAdd (congrMul s₂ (congrMul (congrBinom f₂ (.eqRefl _))
        (congrPw s₂ (.eqRefl _)))) (congrMul (congrBinom f₂ (.eqRefl _)) (congrPw s₂ (.eqRefl _)))).eqSymm
      refine withEq (pw_succ (Γ := lt (var 0) (var (Fin.succ 0)) :: Γ₀.map Fm.shift)
        (var (Fin.succ 1) : PTm 3) (var 0)) fun e => ?_
      apply deriveNat; ipra_simps; rw [e]; ring
    -- E3, E4: split the sum and pull out `a`.
    have E3 := sum_add (Γ := Γ₀) aBody (shiftBody tBody) (var 0) (pairT (var 0) (var 1))
    have E4 := (sum_mul_snd (Γ := Γ₀) tBody (var 0) (pairT (var 0) (var 1))).eqTrans
      (congrMul sX (.eqRefl _))
    -- E5, E6: the unshifted sum, by its top term and by its bottom term.
    have E5 := sum_succ' (Γ := Γ₀) tBody (var 0) (pairT (var 0) (var 1))
    rw [inst2_t] at E5
    have T5 := congrMul ((congrBinom fX (.eqRefl _)).eqTrans (binom_self' _))
      (congrPw sX (.eqRefl (var 0 : PTm 2)))
    have E6 := sum_shift (Γ := Γ₀) tBody (var 0) (pairT (var 0) (var 1))
    rw [inst2_t] at E6
    have T6 := congrMul (binom_zero' (Γ := Γ₀) (fstT (pairT (var 0) (var 1))))
      (pw_zero (Γ := Γ₀) (sndT (pairT (var 0) (var 1))))
    have P1 := pw_succ (Γ := Γ₀) (var 1 : PTm 2) (var 0)
    have P2 := pw_succ (Γ := Γ₀) (succ (var 1) : PTm 2) (var 0)
    ipra_lc natEq E0 + natEq T0 + natEq E1 + natEq T1 + natEq E2 + natEq E3 + natEq E4 + natEq P1 - natEq E6 -
      natEq T6 - (V Γ₀ 1) * (natEq E5 + natEq T5) + (1 + V Γ₀ 1) * natEq ih - natEq P2

theorem binomial : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 binomThmFormula := closeUniv 2 binomial_open

theorem binomial_at (m a : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF tBody) (succ m) (pairT m a) ≐ pw (succ a) m := by
  have h := inst (Γ := Γ) binomial_open (![m, a] : Fin 2 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.BinomialTheorem
