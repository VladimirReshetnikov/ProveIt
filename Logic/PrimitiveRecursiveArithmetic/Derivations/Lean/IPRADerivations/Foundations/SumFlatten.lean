import IPRADerivations.Core.Fubini
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.Totient

/-!
# Flattening a double sum

A double sum over the rectangle `i < A`, `p < M` is a single sum over `k < AM`, with `k = iM + p`
decoded by `i = ⌊k/M⌋`, `p = k mod M` (`flatten`, for `M ≥ 1`):

  `Σ_{k<AM} g(⌊k/M⌋, k mod M) = Σ_{i<A} Σ_{p<M} g(i, p)`.

The double sum is `Core/Fubini`'s `Σ_{i<A} oB g (i, ⟨M, x⟩)`. The proof is an induction on `A`: the block
`AM ≤ k < AM + M` is split off (`Core/SumSplit`) and decoded by `⌊(AM + j)/M⌋ = A`, `(AM + j) mod M = j`
for `j < M` (`decode`, by uniqueness of division).

Reusable wherever a family indexed by pairs (for instance the reduced fractions `p/q` of the Khinchin
packet, `hurwitz_khinchin_ipra`) must be handed to a single-index lemma such as
`Foundations/IntervalPacking.packing` or `Foundations/InjectionCount.injection_count`.
-/

namespace LeanProofs.IPRA.Foundations.SumFlatten

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `⌊(AM + j)/M⌋ = A` and `(AM + j) mod M = j` for `j < M`. -/
theorem decode {A M j : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hj : Γ ⊢[PRAAx] lt j M) :
    Γ ⊢[PRAAx] (quo (A * M + j) M ≐ A) ⋏ (rem (A * M + j) M ≐ j) := by
  have u := div_mod_unique (Γ := Γ) (z := A * M + j) (q := A) (r := j) (K' := pred M)
    (by have e := natEq hM; apply deriveNat; ipra_simps; linear_combination 𝔞 A * e)
    (lt_congr (.eqRefl _) hM hj)
  exact .andI ((congrAp2 quoF (.eqRefl _) hM).eqTrans (Prf.andE₁ u))
    ((congrAp2 remF (.eqRefl _) hM).eqTrans (Prf.andE₂ u))

section Flat

variable (g : PTm 3)

/-- `g(⌊k/M⌋, k mod M, x)` over `0 = k`, `1 = ⟨M, x⟩`. -/
def flB : PTm 2 := Syn.subst ![quo (var 0) (fstT (var 1)), rem (var 0) (fstT (var 1)), sndT (var 1)] g

theorem inst2_flB (k z : PTm n) : inst2 (flB g) k z = inst3 g (quo k (fstT z)) (rem k (fstT z)) (sndT z) := by
  simp only [inst2, inst3, flB, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp [subst_ap2]

/-- The invariant: `Σ_{k<AM} g(⌊k/M⌋, k mod M) = Σ_{i<A} Σ_{p<M} g(i, p)`. -/
def flInv (A M x : PTm n) : Fm PTm n :=
  ap2 (sumF (flB g)) (A * M) (pairT M x) ≐ ap2 (sumF (oB g)) A (pairT M x)

@[simp] theorem subst_flInv {k : ℕ} (σ : Fin n → PTm k) (A M x : PTm n) :
    (flInv g A M x).subst σ = flInv g (Syn.subst σ A) (Syn.subst σ M) (Syn.subst σ x) := by
  simp [flInv, subst_ap2]

/-- One block: `Σ_{j<M} g(⌊(AM + j)/M⌋, (AM + j) mod M) = Σ_{j<M} g(A, j)`. -/
theorem block {A M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] ap2 (sumF (offB (flB g))) M (pairT (A * M) (pairT M x)) ≐ inst2 (oB g) A (pairT M x) := by
  refine .eqTrans ?_ (oB_at g A M x).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_offB, inst2_flB, inst2_rowB,
    show Syn.shift (pairT (A * M) (pairT M x)) = pairT (Syn.shift A * Syn.shift M) (pairT (Syn.shift M) (Syn.shift x)) by
      simp [Syn.shift],
    show Syn.shift (pairT A x) = pairT (Syn.shift A) (Syn.shift x) by simp [Syn.shift]]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  have hM' : Θ ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    have s0 : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
      simpa [Fm.shift, Syn.shift] using hM.shift
    exact s0.wk
  have d := decode (A := Syn.shift A) hM' (Prf.hyp0 : Θ ⊢[PRAAx] lt (var 0) (Syn.shift M))
  have s1 : Θ ⊢[PRAAx] sndT (pairT (Syn.shift A * Syn.shift M) (pairT (Syn.shift M) (Syn.shift x))) ≐
      pairT (Syn.shift M) (Syn.shift x) := snd_pair _ _
  have kq : Θ ⊢[PRAAx] fstT (pairT (Syn.shift A * Syn.shift M) (pairT (Syn.shift M) (Syn.shift x))) + var 0 ≐
      Syn.shift A * Syn.shift M + var 0 := congrAdd (fst_pair _ _) (.eqRefl _)
  have mM : Θ ⊢[PRAAx] fstT (sndT (pairT (Syn.shift A * Syn.shift M) (pairT (Syn.shift M) (Syn.shift x)))) ≐ Syn.shift M :=
    (congrFst s1).eqTrans (fst_pair _ _)
  have xx : Θ ⊢[PRAAx] sndT (sndT (pairT (Syn.shift A * Syn.shift M) (pairT (Syn.shift M) (Syn.shift x)))) ≐ Syn.shift x :=
    (congrSnd s1).eqTrans (snd_pair _ _)
  refine (congrInst3 g ((congrAp2 quoF kq mM).eqTrans (Prf.andE₁ d)) ((congrAp2 remF kq mM).eqTrans (Prf.andE₂ d)) xx).eqTrans ?_
  exact (congrInst3 g (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqSymm

/-- Flattening: `Σ_{k<AM} g(⌊k/M⌋, k mod M) = Σ_{i<A} Σ_{p<M} g(i, p)` for `M ≥ 1`. -/
theorem flatten {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (A : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (flB g)) (A * M) (pairT M x) ≐ ap2 (sumF (oB g)) A (pairT M x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (flInv g (var 0) (Syn.shift M) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · rw [subst_flInv]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      show Γ ⊢[PRAAx] ap2 (sumF (flB g)) (zero * M) (pairT M x) ≐ ap2 (sumF (oB g)) zero (pairT M x)
      exact (congrAp2 (sumF (flB g)) (zero_mul _) (.eqRefl _)).eqTrans ((sum_zero _ _).eqTrans (sum_zero _ _).eqSymm)
    · rw [subst_flInv]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := flInv g (var 0) (Syn.shift M) (Syn.shift x) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] ap2 (sumF (flB g)) (var 0 * Syn.shift M) (pairT (Syn.shift M) (Syn.shift x)) ≐
          ap2 (sumF (oB g)) (var 0) (pairT (Syn.shift M) (Syn.shift x)) := Prf.hyp0
      have hM' : Δ ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
        have s0 : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
          simpa [Fm.shift, Syn.shift] using hM.shift
        exact s0.wk
      have es : Δ ⊢[PRAAx] succ (var 0) * Syn.shift M ≐ var 0 * Syn.shift M + Syn.shift M := by
        apply deriveNat; ipra_simps; ring
      show Δ ⊢[PRAAx] ap2 (sumF (flB g)) (succ (var 0) * Syn.shift M) (pairT (Syn.shift M) (Syn.shift x)) ≐
        ap2 (sumF (oB g)) (succ (var 0)) (pairT (Syn.shift M) (Syn.shift x))
      refine (congrAp2 (sumF (flB g)) es (.eqRefl _)).eqTrans ((sum_split _ _ _ _).eqTrans ?_)
      refine .eqTrans ?_ (sum_succ' _ _ _).eqSymm
      exact congrAdd ih (block g hM')
  have a := Prf.allE A hall
  rw [subst_flInv] at a
  simp only [Syn.subst_inst_shift] at a
  exact a

end Flat

end LeanProofs.IPRA.Foundations.SumFlatten
