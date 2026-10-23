import DiophantineConsistency.DirectComposition
import DiophantineConsistency.CompactedJones

/-!
# Structural sizes without constructing representation syntax

The recurrences in this file involve natural numbers only. Their proofs connect
those recurrences to the expression and quartic compilers. In particular, a
compiler client may propagate size bounds alongside its constructor calls,
without evaluating the expression fields of the resulting representations.
-/

namespace DiophantineConsistency

namespace Expr

/-- Maximum number of binary operations along a root-to-leaf path. -/
def depth {σ : Type*} : Expr σ → ℕ
  | .constant _ | .var _ => 0
  | .add p q | .sub p q | .mul p q => 1 + max p.depth q.depth

@[simp] theorem depth_constant {σ : Type*} (a : ℤ) : (constant (σ := σ) a).depth = 0 := rfl
@[simp] theorem depth_var {σ : Type*} (i : σ) : (var i).depth = 0 := rfl
@[simp] theorem depth_add {σ : Type*} (p q : Expr σ) :
    (p + q).depth = 1 + max p.depth q.depth := rfl
@[simp] theorem depth_sub {σ : Type*} (p q : Expr σ) :
    (p - q).depth = 1 + max p.depth q.depth := rfl
@[simp] theorem depth_mul {σ : Type*} (p q : Expr σ) :
    (p * q).depth = 1 + max p.depth q.depth := rfl

@[simp] theorem depth_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    (e.rename f).depth = e.depth := by
  induction e <;> simp_all [rename, depth]

/-- Total number of natural syntax nodes after splitting an integer residual.
This recurrence does not construct either natural expression. -/
def splitSize {σ : Type*} : Expr σ → ℕ
  | .constant _ | .var _ => 2
  | .add p q | .sub p q => 2 + p.splitSize + q.splitSize
  | .mul p q => 6 + 2 * p.splitSize + 2 * q.splitSize

@[simp] theorem splitSize_rename {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    (e.rename f).splitSize = e.splitSize := by
  induction e <;> simp_all [rename, splitSize]

/-- The count-only recurrence agrees with the compiler's two tree counts. -/
theorem splitSize_eq {σ : Type*} (e : Expr σ) :
    e.splitSize = QuarticCompiler.Gates.count e.splitNatural.1 +
      QuarticCompiler.Gates.count e.splitNatural.2 := by
  induction e <;> simp_all only [splitSize, splitNatural, QuarticCompiler.Gates.count]
  all_goals omega

end Expr

namespace NatExpr

/-- Natural expression depth, with leaves at depth zero. -/
def depth {σ : Type*} : NatExpr σ → ℕ
  | .constant _ | .var _ => 0
  | .add p q | .mul p q => 1 + max p.depth q.depth

/-- A depth bound controls tree size even when a shared source expands into a
large tree. The proof uses ordinary natural arithmetic, not native evaluation. -/
theorem count_le_pow_depth {σ : Type*} (e : NatExpr σ) :
    QuarticCompiler.Gates.count e + 1 ≤ 2 ^ (e.depth + 1) := by
  induction e with
  | constant a => simp [QuarticCompiler.Gates.count, depth]
  | var i => simp [QuarticCompiler.Gates.count, depth]
  | add p q hp hq | mul p q hp hq =>
      have hp' : QuarticCompiler.Gates.count p + 1 ≤ 2 ^ (max p.depth q.depth + 1) :=
        hp.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (le_max_left _ _) _))
      have hq' : QuarticCompiler.Gates.count q + 1 ≤ 2 ^ (max p.depth q.depth + 1) :=
        hq.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (le_max_right _ _) _))
      simp only [QuarticCompiler.Gates.count, depth]
      rw [show 1 + max p.depth q.depth + 1 = (max p.depth q.depth + 1) + 1 by omega,
        pow_succ]
      omega

end NatExpr

namespace Expr

/-- Splitting can at most double syntax depth. -/
theorem splitNatural_depth_le {σ : Type*} (e : Expr σ) :
    e.splitNatural.1.depth ≤ 2 * e.depth ∧ e.splitNatural.2.depth ≤ 2 * e.depth := by
  induction e with
  | constant a => simp [splitNatural, depth, NatExpr.depth]
  | var i => simp [splitNatural, depth, NatExpr.depth]
  | add p q hp hq | sub p q hp hq | mul p q hp hq =>
      simp only [splitNatural, depth, NatExpr.depth]
      constructor <;> omega

/-- A cheap bound on split tree size, independent of variable names and values. -/
theorem splitSize_le_pow_depth {σ : Type*} (e : Expr σ) :
    e.splitSize + 2 ≤ 2 ^ (2 * e.depth + 2) := by
  obtain ⟨hp, hq⟩ := e.splitNatural_depth_le
  have hp' := (NatExpr.count_le_pow_depth e.splitNatural.1).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hp 1))
  have hq' := (NatExpr.count_le_pow_depth e.splitNatural.2).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hq 1))
  rw [splitSize_eq]
  rw [show 2 * e.depth + 2 = (2 * e.depth + 1) + 1 by omega, pow_succ]
  omega

end Expr

namespace Rep

variable {σ τ : Type*} {P Q : (σ → ℕ) → Prop}

/-- Expression depth, without referring to the represented predicate. -/
def depth (r : Rep σ P) : ℕ := r.expression.depth

/-- Exact number of variables used by the unsimplified quartic compiler. -/
def rawQuarticVariables (r : Rep σ P) : ℕ :=
  r.witnessCount + r.expression.splitSize + 1

@[simp] theorem depth_ofIff (r : Rep σ P) (h : ∀ v, P v ↔ Q v) :
    (r.ofIff h).depth = r.depth := rfl
@[simp] theorem depth_reindex (r : Rep σ P) (f : σ → τ) :
    (r.reindex f).depth = r.depth := by simp only [depth, reindex, Expr.depth_rename]
@[simp] theorem depth_equality (p q : Expr σ) :
    (equality p q).depth = 1 + max p.depth q.depth := by
  simp only [depth, equality, Expr.depth_rename]; rfl
@[simp] theorem depth_conjunction (r : Rep σ P) (s : Rep σ Q) :
    (r.conjunction s).depth = 2 + max r.depth s.depth := by
  simp only [depth, conjunction, Expr.depth, Expr.depth_rename, max_self]
  omega
@[simp] theorem depth_disjunction (r : Rep σ P) (s : Rep σ Q) :
    (r.disjunction s).depth = 1 + max r.depth s.depth := by
  simp only [depth, disjunction, Expr.depth, Expr.depth_rename]
@[simp] theorem depth_existsBlock {k : ℕ} {P : (σ ⊕ Fin k → ℕ) → Prop}
    (r : Rep (σ ⊕ Fin k) P) : r.existsBlock.depth = r.depth := by
  simp only [depth, existsBlock, Expr.depth_rename]

@[simp] theorem witnessCount_ofIff (r : Rep σ P) (h : ∀ v, P v ↔ Q v) :
    (r.ofIff h).witnessCount = r.witnessCount := rfl
@[simp] theorem witnessCount_reindex (r : Rep σ P) (f : σ → τ) :
    (r.reindex f).witnessCount = r.witnessCount := rfl
@[simp] theorem witnessCount_equality (p q : Expr σ) :
    (equality p q).witnessCount = 0 := rfl
@[simp] theorem witnessCount_conjunction (r : Rep σ P) (s : Rep σ Q) :
    (r.conjunction s).witnessCount = r.witnessCount + s.witnessCount := rfl
@[simp] theorem witnessCount_disjunction (r : Rep σ P) (s : Rep σ Q) :
    (r.disjunction s).witnessCount = r.witnessCount + s.witnessCount := rfl
@[simp] theorem witnessCount_existsBlock {k : ℕ} {P : (σ ⊕ Fin k → ℕ) → Prop}
    (r : Rep (σ ⊕ Fin k) P) : r.existsBlock.witnessCount = k + r.witnessCount := rfl

/-- Uniform finite-conjunction depth bound. It requires no expression traversal. -/
theorem allFin_depth_le (n h : ℕ) (P : Fin n → (σ → ℕ) → Prop)
    (rs : ∀ i, Rep σ (P i)) (hr : ∀ i, (rs i).depth ≤ h) :
    (allFin n P rs).depth ≤ 2 * n + max 1 h := by
  induction n with
  | zero => simp [allFin, Expr.depth]
  | succ n ih =>
      change ((rs 0).conjunction
        (allFin n (fun i => P i.succ) (fun i => rs i.succ))).depth ≤ _
      rw [depth_conjunction]
      have hh := ih (fun i => P i.succ) (fun i => rs i.succ) (fun i => hr i.succ)
      have h0 := hr 0
      omega

/-- The exact raw count gives a cheap bound for the compacted final count. -/
theorem compacted_variables_le {A : Prop} (r : Rep Empty (fun _ => A)) :
    CompactedJones.witnessCount r ≤ r.rawQuarticVariables := by
  have h := CompactedJones.witnessCount_le r
  simpa only [QuarticCompiler.compile, QuarticCompiler.witnessCount,
    rawQuarticVariables, Expr.splitSize_eq, Nat.add_assoc] using h

/-- A certified variable bound from two small metadata numbers. -/
theorem rawQuarticVariables_le (r : Rep σ P) {m h : ℕ}
    (hm : r.witnessCount ≤ m) (hh : r.depth ≤ h) :
    r.rawQuarticVariables + 1 ≤ m + 2 ^ (2 * h + 2) := by
  have he := r.expression.splitSize_le_pow_depth
  have hp : 2 ^ (2 * r.depth + 2) ≤ 2 ^ (2 * h + 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  change r.witnessCount + r.expression.splitSize + 1 + 1 ≤ _
  change r.expression.splitSize + 2 ≤ 2 ^ (2 * r.depth + 2) at he
  omega

end Rep

namespace GraphRep

variable {σ τ : Type*} {f g : (σ → ℕ) → ℕ}

@[simp] theorem depth_constant (n : ℕ) :
    (constant (σ := σ) n).depth = 1 := rfl
@[simp] theorem depth_coordinate (i : σ) : (coordinate i).depth = 1 := rfl
@[simp] theorem depth_reindex (r : GraphRep f) (f : σ → τ) :
    (r.reindex f).depth = r.depth := by
  simp only [reindex, Rep.depth_ofIff, Rep.depth_reindex]
@[simp] theorem witnessCount_constant (n : ℕ) :
    (constant (σ := σ) n).witnessCount = 0 := rfl
@[simp] theorem witnessCount_coordinate (i : σ) : (coordinate i).witnessCount = 0 := rfl
@[simp] theorem witnessCount_reindex (r : GraphRep f) (f : σ → τ) :
    (r.reindex f).witnessCount = r.witnessCount := rfl

end GraphRep

namespace Rep

variable {σ : Type*} {P : (Option σ → ℕ) → Prop} {f : (σ → ℕ) → ℕ}

@[simp] theorem depth_bindGraph (r : Rep (Option σ) P) (s : GraphRep f) :
    (r.bindGraph s).depth = 2 + max r.depth s.depth := by
  simp only [bindGraph, depth_ofIff, depth_existsBlock, depth_reindex, depth_conjunction]
@[simp] theorem witnessCount_bindGraph (r : Rep (Option σ) P) (s : GraphRep f) :
    (r.bindGraph s).witnessCount = 1 + (r.witnessCount + s.witnessCount) := rfl

end Rep

namespace GraphRep

variable {σ : Type*} {f g : (σ → ℕ) → ℕ}

@[simp] theorem depth_add (r : GraphRep f) (s : GraphRep g) :
    (r.add s).depth = 2 + max (2 + max 2 s.depth) r.depth := by
  simp only [add, Rep.depth_ofIff, Rep.depth_bindGraph, depth_reindex,
    Rep.depth_equality, Expr.depth, max_self]
  congr 3
@[simp] theorem depth_mul (r : GraphRep f) (s : GraphRep g) :
    (r.mul s).depth = 2 + max (2 + max 2 s.depth) r.depth := by
  simp only [mul, Rep.depth_ofIff, Rep.depth_bindGraph, depth_reindex,
    Rep.depth_equality, Expr.depth, max_self]
  congr 3
@[simp] theorem witnessCount_add (r : GraphRep f) (s : GraphRep g) :
    (r.add s).witnessCount = 2 + r.witnessCount + s.witnessCount := by
  simp only [add, Rep.witnessCount_ofIff, Rep.witnessCount_bindGraph,
    witnessCount_reindex, Rep.witnessCount_equality]; omega
@[simp] theorem witnessCount_mul (r : GraphRep f) (s : GraphRep g) :
    (r.mul s).witnessCount = 2 + r.witnessCount + s.witnessCount := by
  simp only [mul, Rep.witnessCount_ofIff, Rep.witnessCount_bindGraph,
    witnessCount_reindex, Rep.witnessCount_equality]; omega

theorem depth_add_le (r : GraphRep f) (s : GraphRep g) {h : ℕ}
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.add s).depth ≤ 6 + h := by
  rw [depth_add]; omega

theorem depth_mul_le (r : GraphRep f) (s : GraphRep g) {h : ℕ}
    (hr : r.depth ≤ h) (hs : s.depth ≤ h) : (r.mul s).depth ≤ 6 + h := by
  rw [depth_mul]; omega

end GraphRep

namespace NatExpr

variable {σ : Type*}

/-- Natural polynomial graph size is computed from its syntax-node count. -/
theorem graphRep_witnessCount (e : NatExpr σ) :
    e.graphRep.witnessCount + 1 = QuarticCompiler.Gates.count e := by
  induction e <;> simp_all [graphRep, GraphRep.witnessCount_add,
    GraphRep.witnessCount_mul, QuarticCompiler.Gates.count] <;> omega

/-- Graph compilation increases depth by at most six per natural syntax level. -/
theorem graphRep_depth_le (e : NatExpr σ) :
    e.graphRep.depth ≤ 6 * e.depth + 1 := by
  induction e with
  | constant a => change 1 ≤ 1; exact le_rfl
  | var i => change 1 ≤ 1; exact le_rfl
  | add p q hp hq =>
      change (p.graphRep.add q.graphRep).depth ≤ 6 * (1 + max p.depth q.depth) + 1
      rw [GraphRep.depth_add]
      omega
  | mul p q hp hq =>
      change (p.graphRep.mul q.graphRep).depth ≤ 6 * (1 + max p.depth q.depth) + 1
      rw [GraphRep.depth_mul]
      omega

end NatExpr

end DiophantineConsistency
