import IPRADerivations.Foundations.BackwardDemand

/-!
# Predetermined demand recursion (`ipra_resources_and_elimination_2026-11-15`, `lem:horizon`, `thm:demand`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, Section 3: for fixed PR
functions `D`, `b`, `F` one wants

`X(0, k) = b(k)`,   `X(n + 1, k) = F(n, k, X(n, D(n, k)))`,

where "the recursive call changes `k`. It is therefore not the ordinary PR constructor with `k`
held fixed." The construction: the backward array `B(0; N, K) = K`,
`B(j + 1; N, K) = D(N ∸ (j + 1), B(j; N, K))`, the horizon `H(t; N, K) = B(N ∸ t; N, K)`, the
forward pass `V(0; N, K) = b(H(0; N, K))`, `V(t + 1; N, K) = F(t, H(t + 1; N, K), V(t; N, K))`,
and `X(N, K) = V(N; N, K)`.

`Foundations/BackwardDemand` (packet `ipra_finite_demand`) has the backward array, the horizon
and the two horizon identities of `lem:horizon`. This module derives the coherence identities
of `lem:horizon` and `thm:demand`, with an extra parameter `x` carried everywhere; `b` and `F`
are arbitrary terms:

* `appF`, `congrAppF`, `horizon_congr`: `F` at terms, and congruences;
* `back_coherent`: `B(j + 1; N + 1, K) = B(j; N, D(N, K))`, by quantifier-free induction on
  `j`;
* `succ_monus_of_le`, `horizon_coherent`: `H(t; N + 1, K) = H(t; N, D(N, K))` for `t ≤ N`;
* `fwdBase`, `fwdStep`, `V`, `V_zero`, `V_succ`: the forward pass as one primitive recursion
  on the packed terminal data `⟨N, ⟨K, x⟩⟩`;
* `V_coherent`: `t ≤ N` gives `V(t; N + 1, K) = V(t; N, D(N, K))`, by quantifier-free
  induction on the guarded equation;
* `X`, `demand_zero`, `demand_succ`: `thm:demand`. `X(0, K) = b(K)` and
  `X(N + 1, K) = F(N, K, X(N, D(N, K)))`.

Not derived: `thm:term-compile` (the internal correctness of the term compiler).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.DemandRecursion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BackwardDemand
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem pair_congr {a a' c c' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hc : Γ ⊢[PRAAx] c ≐ c') :
    Γ ⊢[PRAAx] pairT a c ≐ pairT a' c' :=
  congrAdd (congrMul (congrAdd ha hc) (congrAdd ha hc)) ha

variable (D : PR 3)

/-- The horizon depends only on the values of its arguments. -/
theorem horizon_congr {N N' K K' t t' x x' : PTm n} (hN : Γ ⊢[PRAAx] N ≐ N')
    (hK : Γ ⊢[PRAAx] K ≐ K') (ht : Γ ⊢[PRAAx] t ≐ t') (hx : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] horizon D N K t x ≐ horizon D N' K' t' x' :=
  congrAp2 (backwardF D) (congrMonus hN ht) (pair_congr hN (pair_congr hK hx))

/-! ## The coherence identities of `lem:horizon` -/

/-- Variables: `0 = j`, `1 = N`, `2 = K`, `3 = x`. -/
private abbrev c1F : Fm PTm 4 :=
  backward D (succ (var 1)) (var 2) (succ (var 0)) (var 3) ≐
    backward D (var 1) (ap3 D (var 1) (var 2) (var 3)) (var 0) (var 3)

private theorem c1₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] c1F D := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_backward, subst_ap3, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, inst_two, inst_three, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine (backward_succ D _ _ zero _).eqTrans (.eqTrans ?_ (backward_zero D _ _ _).eqSymm)
    exact congrAp3 D ((succ_monus_succ _ zero).eqTrans (monus_zero _)) (backward_zero D _ _ _)
      (.eqRefl _)
  · simp only [Fm.subst_eq, subst_backward, subst_ap3, Syn.subst_var, Syn.repl_zero, repl_one,
      repl_two, repl_three, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine (backward_succ D _ _ (succ (var 0)) _).eqTrans
      (.eqTrans ?_ (backward_succ D _ _ (var 0) _).eqSymm)
    exact congrAp3 D (succ_monus_succ _ _) Prf.hyp0 (.eqRefl _)

/-- `B(j + 1; N + 1, K) = B(j; N, D(N, K))`. -/
theorem back_coherent (N K j x : PTm n) :
    Γ ⊢[PRAAx] backward D (succ N) K (succ j) x ≐ backward D N (ap3 D N K x) j x := by
  have i := inst (Γ := Γ) (c1₀ D) (![j, N, K, x] : Fin 4 → PTm n)
  simpa using i

/-- `(N + 1) ∸ t = (N ∸ t) + 1` for `t ≤ N`. -/
theorem succ_monus_of_le {t N : PTm n} (h : Γ ⊢[PRAAx] le t N) :
    Γ ⊢[PRAAx] monus (succ N) t ≐ succ (monus N t) :=
  (congrMonus ((congrSucc (eq_add_of_le h)).eqTrans (add_succ t _).eqSymm) (.eqRefl t)).eqTrans
    (add_monus' _ t)

/-- `H(t; N + 1, K) = H(t; N, D(N, K))` for `t ≤ N`. -/
theorem horizon_coherent {t N : PTm n} (h : Γ ⊢[PRAAx] le t N) (K x : PTm n) :
    Γ ⊢[PRAAx] horizon D (succ N) K t x ≐ horizon D N (ap3 D N K x) t x :=
  (backward_index_congr D (succ N) K x (succ_monus_of_le h)).eqTrans
    (back_coherent D N K (monus N t) x)

/-! ## The forward pass -/

variable (b : PTm 2) (F : PTm 4)

/-- `F(t, k, v, x)` at terms. -/
def appF (t k v x : PTm n) : PTm n := Syn.subst ![t, k, v, x] F

@[simp] theorem subst_appF {m : ℕ} (σ : Fin n → PTm m) (t k v x : PTm n) :
    Syn.subst σ (appF F t k v x) =
      appF F (Syn.subst σ t) (Syn.subst σ k) (Syn.subst σ v) (Syn.subst σ x) := by
  simp only [appF, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> rfl

theorem congrAppF {t t' k k' v v' x x' : PTm n} (h₁ : Γ ⊢[PRAAx] t ≐ t')
    (h₂ : Γ ⊢[PRAAx] k ≐ k') (h₃ : Γ ⊢[PRAAx] v ≐ v') (h₄ : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] appF F t k v x ≐ appF F t' k' v' x' :=
  Prf.eqCongr F fun i => by fin_cases i <;> assumption

/-- The base of the forward pass; variable `0 = ⟨N, ⟨K, x⟩⟩`. -/
def fwdBase : PTm 1 :=
  inst2 b (horizon D (fstT (var 0)) (fstT (sndT (var 0))) zero (sndT (sndT (var 0))))
    (sndT (sndT (var 0)))

/-- The step of the forward pass; variables `0 = t`, `1 = V(t)`, `2 = ⟨N, ⟨K, x⟩⟩`. -/
def fwdStep : PTm 3 :=
  appF F (var 0)
    (horizon D (fstT (var 2)) (fstT (sndT (var 2))) (succ (var 0)) (sndT (sndT (var 2))))
    (var 1) (sndT (sndT (var 2)))

/-- `V(t; N, K)`, with the parameter `x`. -/
def V (N K t x : PTm n) : PTm n :=
  ap2 (rec2 (fwdBase D b) (fwdStep D F)) t (pairT N (pairT K x))

@[simp] theorem subst_V {m : ℕ} (σ : Fin n → PTm m) (N K t x : PTm n) :
    Syn.subst σ (V D b F N K t x) =
      V D b F (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [V, subst_ap2, subst_pairT]

theorem V_zero (N K x : PTm n) :
    Γ ⊢[PRAAx] V D b F N K zero x ≐ inst2 b (horizon D N K zero x) x := by
  have h := rec2_zero (Γ := Γ) (fwdBase D b) (fwdStep D F) (pairT N (pairT K x))
  have e : Syn.subst ![pairT N (pairT K x)] (fwdBase D b) =
      inst2 b (horizon D (fstT (pairT N (pairT K x))) (fstT (sndT (pairT N (pairT K x)))) zero
        (sndT (sndT (pairT N (pairT K x))))) (sndT (sndT (pairT N (pairT K x)))) := by
    simp [fwdBase]
  rw [e] at h
  have ex : Γ ⊢[PRAAx] sndT (sndT (pairT N (pairT K x))) ≐ x :=
    (congrSnd (snd_pair N (pairT K x))).eqTrans (snd_pair K x)
  exact h.eqTrans (congrInst2 b
    (horizon_congr D (fst_pair _ _)
      ((congrFst (snd_pair N (pairT K x))).eqTrans (fst_pair K x)) (.eqRefl _) ex) ex)

theorem V_succ (N K t x : PTm n) :
    Γ ⊢[PRAAx] V D b F N K (succ t) x ≐
      appF F t (horizon D N K (succ t) x) (V D b F N K t x) x := by
  have h := rec2_succ (Γ := Γ) (fwdBase D b) (fwdStep D F) t (pairT N (pairT K x))
  have e : Syn.subst ![t, ap2 (rec2 (fwdBase D b) (fwdStep D F)) t (pairT N (pairT K x)),
        pairT N (pairT K x)] (fwdStep D F) =
      appF F t (horizon D (fstT (pairT N (pairT K x))) (fstT (sndT (pairT N (pairT K x))))
          (succ t) (sndT (sndT (pairT N (pairT K x)))))
        (V D b F N K t x) (sndT (sndT (pairT N (pairT K x)))) := by
    simp [fwdStep]
    rfl
  rw [e] at h
  have ex : Γ ⊢[PRAAx] sndT (sndT (pairT N (pairT K x))) ≐ x :=
    (congrSnd (snd_pair N (pairT K x))).eqTrans (snd_pair K x)
  exact h.eqTrans (congrAppF F (.eqRefl _)
    (horizon_congr D (fst_pair _ _)
      ((congrFst (snd_pair N (pairT K x))).eqTrans (fst_pair K x)) (.eqRefl _) ex)
    (.eqRefl _) ex)

/-- Variables: `0 = t`, `1 = N`, `2 = K`, `3 = x`. -/
private abbrev vcF : Fm PTm 4 :=
  le (var 0) (var 1) ⟶
    (V D b F (succ (var 1)) (var 2) (var 0) (var 3) ≐
      V D b F (var 1) (ap3 D (var 1) (var 2) (var 3)) (var 0) (var 3))

private theorem vc₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] vcF D b F := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_V, subst_ap3, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, inst_three, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine .impI ((V_zero D b F _ _ _).eqTrans (.eqTrans ?_ (V_zero D b F _ _ _).eqSymm))
    exact congrInst2 b (horizon_coherent D Prf.hyp0 _ _) (.eqRefl _)
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_V, subst_ap3, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, repl_three, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine .impI ((V_succ D b F _ _ _ _).eqTrans (.eqTrans ?_ (V_succ D b F _ _ _ _).eqSymm))
    exact congrAppF F (.eqRefl _) (horizon_coherent D Prf.hyp0 _ _)
      (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)) (.eqRefl _)

/-- The two forward executions agree up to time `N`. -/
theorem V_coherent {t N : PTm n} (h : Γ ⊢[PRAAx] le t N) (K x : PTm n) :
    Γ ⊢[PRAAx] V D b F (succ N) K t x ≐ V D b F N (ap3 D N K x) t x := by
  have i := inst (Γ := Γ) (vc₀ D b F) (![t, N, K, x] : Fin 4 → PTm n)
  simp at i
  exact .impE i h

/-! ## `thm:demand` -/

/-- `X(N, K) = V(N; N, K)`. -/
def X (N K x : PTm n) : PTm n := V D b F N K N x

/-- `X(0, K) = b(K)`. -/
theorem demand_zero (K x : PTm n) : Γ ⊢[PRAAx] X D b F zero K x ≐ inst2 b K x :=
  (V_zero D b F zero K x).eqTrans (congrInst2 b (horizon_final D zero K x) (.eqRefl _))

/-- `X(N + 1, K) = F(N, K, X(N, D(N, K)))`. -/
theorem demand_succ (N K x : PTm n) :
    Γ ⊢[PRAAx] X D b F (succ N) K x ≐ appF F N K (X D b F N (ap3 D N K x) x) x :=
  (V_succ D b F (succ N) K N x).eqTrans
    (congrAppF F (.eqRefl _) (horizon_final D (succ N) K x)
      (V_coherent D b F (le_refl N) K x) (.eqRefl _))

end LeanProofs.IPRA.Foundations.DemandRecursion
