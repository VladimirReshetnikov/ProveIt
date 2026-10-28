import DiophantineConsistency.NaturalSimplifier
import DiophantineConsistency.ExecutableJones

/-!
# A smaller Jones source obtained by deleting redundant natural gates

All values and witness domains are preserved. The source quartic uses no
more witness slots than the unsimplified gate compiler, which also reduces
or preserves the exponent parameter of the subsequent Jones encoding.
-/

namespace DiophantineConsistency.SimplifiedJones

open Jones1982

def left {A : Prop} (r : Rep Empty (fun _ => A)) := r.expression.splitNatural.1.simplify
def right {A : Prop} (r : Rep Empty (fun _ => A)) := r.expression.splitNatural.2.simplify

def witnessCount {A : Prop} (r : Rep Empty (fun _ => A)) : ℕ :=
  QuarticCompiler.witnessCount (left r) (right r)

theorem witnessCount_le {A : Prop} (r : Rep Empty (fun _ => A)) :
    witnessCount r ≤ (QuarticCompiler.compile r).ν := by
  have hp := NatExpr.count_simplify_le r.expression.splitNatural.1
  have hq := NatExpr.count_simplify_le r.expression.splitNatural.2
  change r.witnessCount + (QuarticCompiler.Gates.count (left r) +
    (QuarticCompiler.Gates.count (right r) + 1)) ≤
    r.witnessCount + (QuarticCompiler.Gates.count r.expression.splitNatural.1 +
      (QuarticCompiler.Gates.count r.expression.splitNatural.2 + 1))
  dsimp only [left, right]
  omega

/-- The positional exponent parameter cannot increase after gate deletion. -/
theorem Lexp_le {A : Prop} (r : Rep Empty (fun _ => A)) :
    Lexp (witnessCount r) 4 ≤ Lexp (QuarticCompiler.compile r).ν 4 := by
  exact pow_le_pow_right₀ (by decide : 1 ≤ (5 : ℕ))
    (Nat.add_le_add_right (witnessCount_le r) 1)

theorem wset_iff {A : Prop} (r : Rep Empty (fun _ => A)) (x : ℕ) :
    Wset (QuarticCompiler.quartic (left r) (right r)) x ↔ A := by
  rw [QuarticCompiler.wset_quartic_iff]
  simpa only [left, right, NatExpr.eval_simplify] using
    (r.correct_splitNatural Empty.elim).symm

/-- Normalized quartic data with a nonincreasing number of witness slots. -/
noncomputable def compile {A : Prop} (r : Rep Empty (fun _ => A)) : QuarticCompiler.Result A :=
  { ν := witnessCount r
    positive := by dsimp only [witnessCount, QuarticCompiler.witnessCount]; omega
    polynomial := QuarticCompiler.quartic (left r) (right r)
    degree := QuarticCompiler.quartic_degree _ _
    normalized := QuarticCompiler.quartic_normalized _ _
    correct := wset_iff r }

/-- Executable final syntax using the simplified natural gate source. -/
def expression {A : Prop} (r : Rep Empty (fun _ => A)) : Expr (Fin 9) :=
  ExecutableJones.expression (QuarticSyntax.expression (left r) (right r)) 0

theorem expression_correct {A : Prop} (r : Rep Empty (fun _ => A)) :
    (∃ v : Fin 9 → ℕ, (expression r).eval (fun i => (v i : ℤ)) = 0) ↔ A := by
  exact (ExecutableJones.hasNaturalZero_quartic (left r) (right r)).trans (wset_iff r 1)

theorem eval_expression {A : Prop} (r : Rep Empty (fun _ => A)) (v : Fin 9 → ℤ) :
    (expression r).eval v =
      MvPolynomial.eval v (NinePolynomial.polynomial (compile r).polynomial 0) := by
  rw [expression, ExecutableJones.eval_expression, JonesSyntax.eval_expression,
    QuarticSyntax.polynomial_expression]
  rfl

theorem noZero_expression {A : Prop} (r : Rep Empty (fun _ => A)) :
    (¬ ∃ v : Fin 9 → ℕ, (expression r).eval (fun i => (v i : ℤ)) = 0) ↔ ¬ A :=
  not_congr (expression_correct r)

end DiophantineConsistency.SimplifiedJones
