import IPRADerivations.Foundations.GridSumsContext
import IPRADerivations.Core.SumOrder
import IPRADerivations.Probability.Variance

/-!
# Grid sums: inequalities, the cells of the grid, and constant summands

A reusable piece of the embedding framework, extending `Foundations/GridSums` and
`Foundations/GridSumsContext` (sums over `[0, N)^d` with the dimension `d` a parameter of the Lean
statements). First use: the finite Stokes inequality on a cube
(`Analysis/StokesCube`, packet `analysis/constructive_stokes_ipra_2026-11-21`).

* `gs_le_gen`: summands that are ordered wherever the facts `P` hold at full depth have ordered grid
  sums (the order analogue of `GridSumsContext.gs_congr_gen`); `gs_le` is the unconditional form;
* `Cells`, `cells_base`, `cells_steps`: the canonical facts "every entry of the list is below the
  bound `N`", so that a hypothesis about the cells of the grid can be used inside the sums;
* `lsum_le`, `fsum_le`: finite sums indexed in the metatheory (`Foundations/TermSums`) are monotone;
* `gpow N k`: the product `N ⋯ N` of `k` factors, with `subst_gpow`, `congrGpow`;
* `gs_const`: a summand that does not depend on the `k` summed entries, `F(y) = C(tl k y)`, has the
  grid sum `N^k · C(x)`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.GridSumsOrder

open_ipra exports
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.GridSumsContext
open LeanProofs.IPRA.Foundations.TermSums (lsum fsum)
open LeanProofs.IPRA.Probability.Variance (sum_const_of)

variable {n : ℕ}

/-! ## Monotonicity -/

/-- Summands that are ordered wherever the facts hold at full depth have ordered grid sums. -/
theorem gs_le_gen {P : ListFacts} {lo D : ℕ} (hP : Steps P lo D) {F G : PTm 1}
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P D m Δ x →
      (Δ ⊢[PRAAx] le (Syn.subst ![x] F) (Syn.subst ![x] G))) :
    ∀ (k e : ℕ), e + k = D → lo ≤ e → ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), P e m Δ x →
      (Δ ⊢[PRAAx] le (Syn.subst ![x] (gs e k F)) (Syn.subst ![x] (gs e k G)))
  | 0, e, he, _, m, Δ, x, hx => by
    have : e = D := by omega
    subst this
    exact H m Δ x hx
  | k + 1, e, he, hlo, m, Δ, x, hx => by
    rw [gs_succ, gs_succ]
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_gsBody, inst2_gsBody]
    exact gs_le_gen hP H k (e + 1) (by omega) (by omega) _ _ _ (hP e hlo (by omega) m Δ x hx)

/-- Summands that are ordered at every argument have ordered grid sums. -/
theorem gs_le {F G : PTm 1}
    (H : ∀ (m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m), Δ ⊢[PRAAx] le (Syn.subst ![x] F) (Syn.subst ![x] G))
    (e k : ℕ) {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) :
    Δ ⊢[PRAAx] le (Syn.subst ![x] (gs e k F)) (Syn.subst ![x] (gs e k G)) :=
  gs_le_gen (P := fun _ _ _ _ => True) (lo := 0) (D := e + k) (fun _ _ _ _ _ _ _ => trivial)
    (fun m Δ x _ => H m Δ x) k e rfl (Nat.zero_le _) m Δ x trivial

/-! ## The cells of the grid -/

/-- Every entry of the list (of depth `e`) is below the bound. -/
def Cells : ListFacts := fun e _ Δ x => ∀ q, q < e → (Δ ⊢[PRAAx] lt (proj q x) (fstT (tl e x)))

theorem cells_base {m : ℕ} (Δ : List (Fm PTm m)) (x : PTm m) : Cells 0 m Δ x :=
  fun q hq => absurd hq (Nat.not_lt_zero q)

theorem cells_steps (lo hi : ℕ) : Steps Cells lo hi := by
  intro e _ _ m Δ x hx q hq
  have hb := gs_bound (Γ := lt (var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift) e (var 0) (Syn.shift x)
  have s : Syn.shift (fstT (tl e x)) = fstT (tl e (Syn.shift x)) := by simp [Syn.shift]
  cases q with
  | zero =>
    have h0 : (lt (var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (fstT (tl e (Syn.shift x))) := by
      rw [← s]; exact Prf.hyp0
    exact lt_congr (proj_pair_zero _ _).eqSymm hb.eqSymm h0
  | succ q =>
    have h := (hx q (by omega)).shift
    have h' : Δ.map Fm.shift ⊢[PRAAx] lt (proj q (Syn.shift x)) (fstT (tl e (Syn.shift x))) := by
      simpa [Fm.shift, Syn.shift, subst_lt] using h
    exact lt_congr (proj_pair_succ q _ _).eqSymm hb.eqSymm h'.wk

/-! ## Finite sums indexed in the metatheory -/

theorem lsum_le {Γ : List (Fm PTm n)} {ι : Type} (f g : ι → PTm n) (h : ∀ i, Γ ⊢[PRAAx] le (f i) (g i)) :
    ∀ l : List ι, Γ ⊢[PRAAx] le (lsum (l.map f)) (lsum (l.map g))
  | [] => le_refl _
  | a :: l => add_le_add₂ (h a) (lsum_le f g h l)

theorem fsum_le {Γ : List (Fm PTm n)} {k : ℕ} {f g : Fin k → PTm n} (h : ∀ i, Γ ⊢[PRAAx] le (f i) (g i)) :
    Γ ⊢[PRAAx] le (fsum k f) (fsum k g) := by
  simp only [fsum, List.ofFn_eq_map]
  exact lsum_le f g h _

/-! ## Constant summands -/

/-- `N ⋯ N`, `k` factors. -/
def gpow (N : PTm n) : ℕ → PTm n
  | 0 => one
  | k + 1 => N * gpow N k

@[simp] theorem subst_gpow {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    ∀ k : ℕ, Syn.subst σ (gpow N k) = gpow (Syn.subst σ N) k
  | 0 => by simp [gpow]
  | k + 1 => by simp [gpow, subst_gpow σ N k]

theorem congrGpow {Γ : List (Fm PTm n)} {N N' : PTm n} (h : Γ ⊢[PRAAx] N ≐ N') :
    ∀ k : ℕ, Γ ⊢[PRAAx] gpow N k ≐ gpow N' k
  | 0 => .eqRefl _
  | k + 1 => congrMul h (congrGpow h k)

/-- The list after `j + 1` entries is the tail of the list after `j` entries. -/
theorem tl_snd : ∀ (j : ℕ) (x : PTm n), tl j (sndT x) = sndT (tl j x)
  | 0, _ => rfl
  | j + 1, x => tl_snd j (sndT x)

theorem shift_subst1 (C : PTm 1) (x : PTm n) :
    Syn.shift (Syn.subst ![x] C) = Syn.subst ![Syn.shift x] C := by
  simp only [Syn.shift, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

/-- A summand that does not depend on the `k` summed entries: `∑ F = N^k · C(x)` when
`F(y) = C(tl k y)` at every list `y`. -/
theorem gs_const (C : PTm 1) : ∀ (k : ℕ) {F : PTm 1},
    (∀ (m : ℕ) (Δ : List (Fm PTm m)) (y : PTm m),
      Δ ⊢[PRAAx] Syn.subst ![y] F ≐ Syn.subst ![tl k y] C) →
    ∀ (e m : ℕ) (Δ : List (Fm PTm m)) (x : PTm m),
      Δ ⊢[PRAAx] Syn.subst ![x] (gs e k F) ≐ gpow (fstT (tl e x)) k * Syn.subst ![x] C
  | 0, _, H, _, m, Δ, x => (H m Δ x).eqTrans (one_mul _).eqSymm
  | k + 1, F, H, e, m, Δ, x => by
    rw [gs_succ]
    have hs : Syn.shift (gpow (fstT (tl e x)) k * Syn.subst ![x] C) =
        gpow (fstT (tl e (Syn.shift x))) k * Syn.subst ![Syn.shift x] C := by
      rw [← shift_subst1]; simp [Syn.shift]
    have hp : Δ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (fstT (tl e x))) ⟶
        (inst2 (gsBody (gs (e + 1) k F)) (var 0) (Syn.shift x) ≐
          Syn.shift (gpow (fstT (tl e x)) k * Syn.subst ![x] C))) := by
      refine .allI (.impI ?_)
      rw [inst2_gsBody, hs]
      have ih := gs_const (comp C (sndT (var 0))) k (F := F) (fun m' Δ' y => by
          have hs' : Syn.subst ![tl k y] (sndT (var 0) : PTm 1) = sndT (tl k y) := by simp
          rw [subst_comp, hs', ← tl_snd]
          exact H m' Δ' y) (e + 1) _ (lt (var 0) (Syn.shift (fstT (tl e x))) :: Δ.map Fm.shift)
        (pairT (var 0) (Syn.shift x))
      have hs'' : Syn.subst ![pairT (var 0) (Syn.shift x)] (sndT (var 0) : PTm 1) =
          sndT (pairT (var 0) (Syn.shift x)) := by simp
      rw [subst_comp, hs''] at ih
      exact ih.eqTrans (congrMul (congrGpow (gs_bound e _ _) k) (congr1 C (snd_pair _ _)))
    exact (sum_const_of _ _ _ _ hp).eqTrans (mul_assoc _ _ _).eqSymm

end LeanProofs.IPRA.Foundations.GridSumsOrder
