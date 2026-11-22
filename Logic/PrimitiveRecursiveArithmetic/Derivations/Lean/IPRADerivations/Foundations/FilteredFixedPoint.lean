import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Core.OrderCertificates

/-!
# Fixed points of filtered contractions

Packet: `analysis/lambert_w_ipra_2026-11-16`, Lemma `lem:finite-fix` ("Finite fixed point"): for
`Φ ∈ T_N(R)` put `G_0 = 0`, `G_{j+1} = X Φ(G_j)`; then `G_{N+1}` is the unique `G ∈ X T_N(R)` with
`G = X Φ(G)`. "If two series agree below degree `m`, their images under `A ↦ X Φ(A)` agree below degree
`m + 1`. Induction shows that the `j`-th iterate has stabilized through degree `j − 1`. After `N + 1` steps
all represented coefficients are stable. The same one-degree improvement proves uniqueness."

The argument depends only on the filtration, so it is stated for an arbitrary unary step `T`, an agreement
order `ν(A, B)` ("`A` and `B` agree below degree `ν(A, B)`") and a size `c(A)` (the truncation degree `N`).
The hypotheses (`Filtered`) are rules at arbitrary contexts and terms:

* `size`: `c(T A) = c(A)` (the step keeps the truncation);
* `contr`: `j ≤ ν(A, B)` and `j ≤ c(A)` give `j + 1 ≤ ν(T A, T B)` (the one-degree improvement);
* `sep`: `c(A) + 1 ≤ ν(A, B)` gives `A = B` (agreement in every represented degree is equality).

With `G_t = T^t(s₀)` (`IterationFusion.iter`):

* `size_at`: `c(G_t) = c(s₀)`;
* `agree_at`: for `t ≤ c(s₀) + 1`, `t ≤ ν(G_t, G_{t+1})` (the `t`-th iterate is stable below degree `t`);
* `fixed_point`: `G_{N+1} = T(G_{N+1})` for `N = c(s₀)`;
* `unique`: two fixed points `G = T G`, `G′ = T G′` are equal (`j ≤ ν(G, G′)` for `j ≤ c(G) + 1`, by the same
  induction).

Each induction is a quantifier-free induction on the number of steps.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FilteredFixedPoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IterationFusion
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The hypotheses of a filtered contraction. -/
structure Filtered (T c : PTm 1) (ν : PTm 2) : Prop where
  size : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (A : PTm k), Γ ⊢[PRAAx] app1 c (app1 T A) ≐ app1 c A
  contr : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {A B j : PTm k},
    (Γ ⊢[PRAAx] le j (inst2 ν A B)) → (Γ ⊢[PRAAx] le j (app1 c A)) →
      (Γ ⊢[PRAAx] le (succ j) (inst2 ν (app1 T A) (app1 T B)))
  sep : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {A B : PTm k},
    (Γ ⊢[PRAAx] le (succ (app1 c A)) (inst2 ν A B)) → (Γ ⊢[PRAAx] A ≐ B)

variable {T c : PTm 1} {ν : PTm 2}

/-! ## The size along the iteration -/

/-- Variables: `0 = t`, `1 = s₀`. -/
private def sizeF (T c : PTm 1) : Fm PTm 2 := app1 c (iter T (var 0) (var 1)) ≐ app1 c (var 1)

private theorem size₀ (H : Filtered T c ν) : ([] : List (Fm PTm 2)) ⊢[PRAAx] sizeF T c := by
  refine ind _ trivial ?_ ?_
  · simp only [sizeF, Fm.subst_eq, subst_app1, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact congrApp1 c (iter_zero T _)
  · simp only [sizeF, Fm.subst_eq, subst_app1, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [sizeF T c] ⊢[PRAAx] app1 c (iter T (var 0) (var 1)) ≐ app1 c (var 1) := Prf.hyp0
    exact (congrApp1 c (iter_succ T _ _)).eqTrans ((H.size _).eqTrans ih)

/-- `c(T^t s₀) = c(s₀)`. -/
theorem size_at (H : Filtered T c ν) (t s₀ : PTm k) : Γ ⊢[PRAAx] app1 c (iter T t s₀) ≐ app1 c s₀ := by
  have i := inst (Γ := Γ) (size₀ H) (![t, s₀] : Fin 2 → PTm k)
  simpa [sizeF] using i

/-! ## Stabilization of the iterates -/

/-- Variables: `0 = t`, `1 = s₀`. -/
private def agrF (T c : PTm 1) (ν : PTm 2) : Fm PTm 2 :=
  le (var 0) (succ (app1 c (var 1))) ⟶
    le (var 0) (inst2 ν (iter T (var 0) (var 1)) (iter T (succ (var 0)) (var 1)))

private theorem agr₀ (H : Filtered T c ν) : ([] : List (Fm PTm 2)) ⊢[PRAAx] agrF T c ν := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [agrF, Fm.subst_imp, subst_le, subst_app1, subst_ap2, subst_inst2, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (zero_le _)
  · simp only [agrF, Fm.subst_imp, subst_le, subst_app1, subst_ap2, subst_inst2, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih : [agrF T c ν] ⊢[PRAAx] le (var 0) (succ (app1 c (var 1))) ⟶
        le (var 0) (inst2 ν (iter T (var 0) (var 1)) (iter T (succ (var 0)) (var 1))) := Prf.hyp0
    refine .impI ?_
    have hk : (le (succ (var 0)) (succ (app1 c (var 1))) :: [agrF T c ν]) ⊢[PRAAx]
        le (succ (var 0)) (succ (app1 c (var 1))) := Prf.hyp0
    have a := Prf.impE ih.wk (le_trans (le_succ_self _) hk)
    have sz := size_at (Γ := le (succ (var 0)) (succ (app1 c (var 1))) :: [agrF T c ν]) H (var 0) (var 1)
    have hc : (le (succ (var 0)) (succ (app1 c (var 1))) :: [agrF T c ν]) ⊢[PRAAx]
        le (var 0) (app1 c (iter T (var 0) (var 1))) :=
      le_congr (.eqRefl _) sz.eqSymm (by ipra_le sl hk)
    have s := H.contr a hc
    exact le_congr (.eqRefl _)
      (congrInst2 ν (iter_succ T _ _).eqSymm (iter_succ T _ _).eqSymm) s

/-- For `t ≤ c(s₀) + 1`, the iterates `T^t s₀` and `T^{t+1} s₀` agree below degree `t`. -/
theorem agree_at (H : Filtered T c ν) {t s₀ : PTm k} (h : Γ ⊢[PRAAx] le t (succ (app1 c s₀))) :
    Γ ⊢[PRAAx] le t (inst2 ν (iter T t s₀) (iter T (succ t) s₀)) := by
  have i := inst (Γ := Γ) (agr₀ H) (![t, s₀] : Fin 2 → PTm k)
  simp [agrF] at i
  exact .impE i h

/-- `lem:finite-fix`, existence: `G_{N+1} = T(G_{N+1})` for `N = c(s₀)`. -/
theorem fixed_point (H : Filtered T c ν) (s₀ : PTm k) :
    Γ ⊢[PRAAx] iter T (succ (app1 c s₀)) s₀ ≐ app1 T (iter T (succ (app1 c s₀)) s₀) := by
  have a := agree_at H (Γ := Γ) (le_refl (succ (app1 c s₀)))
  have sz := size_at (Γ := Γ) H (succ (app1 c s₀)) s₀
  have e := H.sep (le_congr (congrSucc sz.eqSymm) (.eqRefl _) a)
  exact e.eqTrans (iter_succ T _ _)

/-! ## Uniqueness -/

/-- Variables: `0 = j`, `1 = G`, `2 = G′`. -/
private def uniF (T c : PTm 1) (ν : PTm 2) : Fm PTm 3 :=
  (var 1 ≐ app1 T (var 1)) ⟶ (var 2 ≐ app1 T (var 2)) ⟶ le (var 0) (succ (app1 c (var 1))) ⟶
    le (var 0) (inst2 ν (var 1) (var 2))

private theorem uni₀ (H : Filtered T c ν) : ([] : List (Fm PTm 3)) ⊢[PRAAx] uniF T c ν := by
  refine ind _ ⟨trivial, trivial, le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [uniF, Fm.subst_imp, Fm.subst_eq, subst_le, subst_app1, subst_inst2, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (.impI (zero_le _)))
  · simp only [uniF, Fm.subst_imp, Fm.subst_eq, subst_le, subst_app1, subst_inst2, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI (.impI (.impI ?_))
    let Δ : List (Fm PTm 3) := [le (succ (var 0)) (succ (app1 c (var 1))), var 2 ≐ app1 T (var 2),
      var 1 ≐ app1 T (var 1), uniF T c ν]
    have hk : Δ ⊢[PRAAx] le (succ (var 0)) (succ (app1 c (var 1))) := .hyp (by simp [Δ])
    have h₂ : Δ ⊢[PRAAx] var 2 ≐ app1 T (var 2) := .hyp (by simp [Δ])
    have h₁ : Δ ⊢[PRAAx] var 1 ≐ app1 T (var 1) := .hyp (by simp [Δ])
    have ih : Δ ⊢[PRAAx] (var 1 ≐ app1 T (var 1)) ⟶ (var 2 ≐ app1 T (var 2)) ⟶
        le (var 0) (succ (app1 c (var 1))) ⟶ le (var 0) (inst2 ν (var 1) (var 2)) := .hyp (by simp [Δ, uniF])
    have a := Prf.impE (Prf.impE (Prf.impE ih h₁) h₂) (le_trans (le_succ_self _) hk)
    have hc : Δ ⊢[PRAAx] le (var 0) (app1 c (var 1)) := by ipra_le sl hk
    have s := H.contr a hc
    exact le_congr (.eqRefl _) (congrInst2 ν h₁.eqSymm h₂.eqSymm) s

/-- `lem:finite-fix`, uniqueness: two fixed points of `T` are equal. -/
theorem unique (H : Filtered T c ν) {G G' : PTm k} (hG : Γ ⊢[PRAAx] G ≐ app1 T G)
    (hG' : Γ ⊢[PRAAx] G' ≐ app1 T G') : Γ ⊢[PRAAx] G ≐ G' := by
  have i := inst (Γ := Γ) (uni₀ H) (![succ (app1 c G), G, G'] : Fin 3 → PTm k)
  simp [uniF] at i
  exact H.sep (Prf.impE (Prf.impE (Prf.impE i hG) hG') (le_refl _))

end LeanProofs.IPRA.Foundations.FilteredFixedPoint
