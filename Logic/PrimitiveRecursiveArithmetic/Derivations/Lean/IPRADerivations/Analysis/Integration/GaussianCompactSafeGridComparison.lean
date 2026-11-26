import IPRADerivations.Analysis.Integration.GaussianCompactUniformGridComparison

/-!
# Safe positive counts for an actual panel whose width is its count

The count K may be zero. Replacing it by succ(pred K) leaves the
original quadrature on the panel of width K CODE-equal: positive K
is unchanged, while both actual zero-width programs are literal zero.
The independent positive-grid comparison therefore extends to all K
without imposing a new count guard or a desired quadrature identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactSafeGridComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qzero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def safeCount (K : PTm n) : PTm n := succ (pred K)
def numerator (p q K H E L : PTm n) : PTm n := GaussianCompactUniformGridComparison.numerator p q (safeCount K) H K E L
def denominator (p q K H E : PTm n) : PTm n := GaussianCompactUniformGridComparison.denominator p q (safeCount K) H E

@[simp] theorem subst_safeCount {m : ℕ} (σ : Fin n → PTm m) (K : PTm n) :
    Syn.subst σ (safeCount K) = safeCount (Syn.subst σ K) := by simp [safeCount]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p q K H E L : PTm n) :
    Syn.subst σ (numerator p q K H E L) = numerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ K)
      (Syn.subst σ H) (Syn.subst σ E) (Syn.subst σ L) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p q K H E : PTm n) :
    Syn.subst σ (denominator p q K H E) = denominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ K)
      (Syn.subst σ H) (Syn.subst σ E) := by simp [denominator]

theorem safe_positive (K : PTm n) : Γ ⊢[PRAAx] le one (safeCount K) := zero_lt_succ _

theorem denominator_positive (p q K H E : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le one (denominator p q K H E) := GaussianCompactUniformGridComparison.denominator_positive p q (safeCount K) H E hE (safe_positive K) hH

private theorem zero_panel (F : PR 3) (p N a C E x : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] C ≐ zero) : Γ ⊢[PRAAx] quadrature F p N a C E x ≐ qzero := by
  have move : Γ ⊢[PRAAx] quadrature F p N a C E x ≐ quadrature F p N a zero E x := by
    simpa using Prf.eqCongr1 (quadrature F (Syn.shift p) (Syn.shift N) (Syn.shift a) (var 0) (Syn.shift E) (Syn.shift x)) hC
  exact move.eqTrans (GaussianCompactUniformGridComparison.zero_width_any_count F p N a E x hE)

/-- Exact actual program equality, valid for every native K. -/
theorem safe_quadrature (F : PR 3) (p K a E x : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    quadrature F p K a K E x ≐ quadrature F p (safeCount K) a K E x := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact (zero_panel F p K a K E x hE.wk Prf.hyp0).eqTrans
      (zero_panel F p (safeCount K) a K E x hE.wk Prf.hyp0).eqSymm
  · exact GaussianCompactRiemannName.quadrature_index_congr F p K (safeCount K) a K E x Prf.hyp0

/-- The first original count may be zero; the second is any positive H.
Both original observation queries remain independent. -/
theorem original_comparison (F : PR 3) (p q K H a E L x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hH : Γ ⊢[PRAAx] le one H)
    (hMod : Γ ⊢[PRAAx] sampledModulus F a K E L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p K a K E x) (quadrature F q H a K E x) (numerator p q K H E L) (denominator p q K H E) :=
  GaussianRationalDistanceOrder.distance_congr (safe_quadrature F p K a E x hE).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianCompactUniformGridComparison.original_comparison F p q (safeCount K) H a K E L x ha hE (safe_positive K) hH hMod)

theorem actual_safe_positive_count_preserves_quadrature_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ quadrature F (var 0) (var 1) (var 2) (var 1) (var 3) (var 4) ≐
      quadrature F (var 0) (safeCount (var 1)) (var 2) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (safe_quadrature F _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactSafeGridComparison
