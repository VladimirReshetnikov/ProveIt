import DiophantineConsistency.AffineBudget
import DiophantineConsistency.RepresentationSize
import DiophantineConsistency.PolynomialGraph
import DiophantineConsistency.NativeFormulaGraphs
import DiophantineConsistency.NativeGraphEnumerator
import DiophantineConsistency.BoundedForallSize

/-! # Constructor bounds for graph depth

`Thin C r` is preserved by nonempty graph substitution. Its proof is independent
of the represented function. The fixed polynomial blocks contribute only the
constant `C`; inserted graph witnesses pay for the remaining syntax depth.
-/

namespace DiophantineConsistency

namespace Rep

open scoped BigOperators

variable {σ : Type*} {n : ℕ} {P : (Fin n → ℕ) → Prop}
  {f : Fin n → (σ → ℕ) → ℕ}

theorem compose_depth_le (r : Rep (Fin n) P) (s : ∀ i, GraphRep (f i))
    {h : ℕ} (hh : 1 ≤ h) (hr : r.depth ≤ h) (hs : ∀ i, (s i).depth ≤ h) :
    (r.compose s).depth ≤ 2 * n + 2 + h := by
  simp only [compose, depth_ofIff, depth_existsBlock, depth_conjunction, depth_reindex]
  rw [show 2 * n + 2 + h = 2 + (2 * n + h) by omega]
  apply Nat.add_le_add_left
  apply max_le (by omega : r.depth ≤ 2 * n + h)
  calc
    _ ≤ 2 * n + max 1 h := allFin_depth_le n h _ _ (fun i => by
      erw [depth_reindex]
      exact hs i)
    _ = _ := by rw [max_eq_right hh]


/-- A graph with depth paid for by its witnesses and one fixed block allowance. -/
def Thin (C : ℕ) {σ : Type*} {P : (σ → ℕ) → Prop} (r : Rep σ P) : Prop :=
  r.depth ≤ 6 * r.witnessCount + C

@[simp] theorem thin_ofIff {σ : Type*} {P Q : (σ → ℕ) → Prop}
    (C : ℕ) (r : Rep σ P) (h : ∀ v, P v ↔ Q v) :
    Thin C (r.ofIff h) ↔ Thin C r := Iff.rfl
@[simp] theorem thin_reindex {σ τ : Type*} {P : (σ → ℕ) → Prop}
    (C : ℕ) (r : Rep σ P) (f : σ → τ) :
    Thin C (r.reindex f) ↔ Thin C r := by simp only [Thin, depth_reindex, witnessCount_reindex]

theorem thin_compose (C : ℕ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (r : Rep (Fin n) P) (s : ∀ i, GraphRep (f i))
    (hr : Thin C r) (hs : ∀ i, Thin C (s i)) : Thin C (r.compose s) := by
  exact AffineBudget.compose
    (fun i => (s i).witnessCount) (fun i => (s i).depth) hC hr hs
    (fun _ hh hr hs => compose_depth_le r s hh hr hs)
    (by omega : 2 * n + 2 ≤ 6 * (n))
    (by rw [BoundedForallSize.predicate_compose_count])

end Rep

namespace GraphRep

open scoped BigOperators
open Rep (Thin)

variable {σ : Type*} {n : ℕ} {f : (Fin n → ℕ) → ℕ}
  {g : Fin n → (σ → ℕ) → ℕ}

theorem composeDirect_depth_le (r : GraphRep f) (s : ∀ i, GraphRep (g i))
    {h : ℕ} (hh : 1 ≤ h) (hr : r.depth ≤ h) (hs : ∀ i, (s i).depth ≤ h) :
    (r.composeDirect s).depth ≤ 2 * n + 2 + h := by
  simp only [composeDirect, Rep.depth_ofIff, Rep.depth_existsBlock,
    Rep.depth_conjunction, Rep.depth_reindex]
  rw [show 2 * n + 2 + h = 2 + (2 * n + h) by omega]
  apply Nat.add_le_add_left
  apply max_le (by omega : r.depth ≤ 2 * n + h)
  calc
    _ ≤ 2 * n + max 1 h := Rep.allFin_depth_le n h _ _ (fun i => by
      erw [Rep.depth_reindex]
      exact hs i)
    _ = _ := by rw [max_eq_right hh]

theorem compose_depth_le (r : GraphRep f) (s : ∀ i, GraphRep (g i))
    {h : ℕ} (hh : 1 ≤ h) (hr : r.depth ≤ h) (hs : ∀ i, (s i).depth ≤ h) :
    (r.compose s).depth ≤ 2 * n + 4 + h := by
  let index : Option (Fin n) → Fin (n + 1)
    | none => 0
    | some i => i.succ
  let inputs (j : Fin (n + 1)) (v : Option σ → ℕ) : ℕ :=
    Fin.cases (v none) (fun i => g i (v ∘ some)) j
  let args : ∀ j, GraphRep (inputs j) :=
    Fin.cases (coordinate none) (fun i => (s i).reindex some)
  have hargs : ∀ j, (args j).depth ≤ h := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change 1 ≤ h
      exact hh
    · change ((s i).reindex some).depth ≤ h
      rw [depth_reindex]
      exact hs i
  change ((Rep.reindex r index).compose args).depth ≤ _
  exact (Rep.compose_depth_le _ _ hh (by simpa only [Rep.depth_reindex] using hr)
    hargs).trans (by omega)

theorem thin_composeDirect (C : ℕ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (r : GraphRep f) (s : ∀ i, GraphRep (g i))
    (hr : Thin C r) (hs : ∀ i, Thin C (s i)) : Thin C (r.composeDirect s) := by
  exact AffineBudget.compose
    (fun i => (s i).witnessCount) (fun i => (s i).depth) hC hr hs
    (fun _ hh hr hs => composeDirect_depth_le r s hh hr hs)
    (by omega : 2 * n + 2 ≤ 6 * (n))
    (by rw [composeDirect_witnessCount])

theorem thin_compose (C : ℕ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (r : GraphRep f) (s : ∀ i, GraphRep (g i))
    (hr : Thin C r) (hs : ∀ i, Thin C (s i)) : Thin C (r.compose s) := by
  exact AffineBudget.compose
    (fun i => (s i).witnessCount) (fun i => (s i).depth) hC hr hs
    (fun _ hh hr hs => compose_depth_le r s hh hr hs)
    (by omega : 2 * n + 4 ≤ 6 * (n + 1))
    (by rw [compose_witnessCount])

theorem thin_add {σ : Type*} {f g : (σ → ℕ) → ℕ} (C : ℕ)
    (r : GraphRep f) (s : GraphRep g) (hr : Thin C r) (hs : Thin C s) :
    Thin C (r.add s) := by
  dsimp only [Thin] at *
  rw [depth_add, witnessCount_add]
  omega

theorem thin_mul {σ : Type*} {f g : (σ → ℕ) → ℕ} (C : ℕ)
    (r : GraphRep f) (s : GraphRep g) (hr : Thin C r) (hs : Thin C s) :
    Thin C (r.mul s) := by
  dsimp only [Thin] at *
  rw [depth_mul, witnessCount_mul]
  omega

theorem thin_constant {σ : Type*} (C : ℕ) (hC : 1 ≤ C) (n : ℕ) :
    Thin C (constant (σ := σ) n) := by simpa [Thin] using hC

theorem thin_coordinate {σ : Type*} (C : ℕ) (hC : 1 ≤ C) (i : σ) :
    Thin C (coordinate (σ := σ) i) := by
  unfold Thin
  rw [GraphRep.depth_coordinate, GraphRep.witnessCount_coordinate]
  simpa only [Nat.mul_zero, Nat.zero_add] using hC

@[simp] theorem thin_reindex {σ τ : Type*} {f : (σ → ℕ) → ℕ}
    (C : ℕ) (r : GraphRep f) (h : σ → τ) : Thin C (r.reindex h) ↔ Thin C r := by
  simp only [Thin, depth_reindex, witnessCount_reindex]

end GraphRep

namespace NatExpr

@[simp] theorem depth_toInteger {σ : Type*} (e : NatExpr σ) : e.toInteger.depth = e.depth := by
  induction e <;> simp_all [toInteger, depth]

@[simp] theorem depth_directGraphRep {σ : Type*} (e : NatExpr σ) :
    e.directGraphRep.depth = 1 + e.depth := by
  simp only [directGraphRep, Rep.depth_ofIff, Rep.depth_equality, Expr.depth,
    Expr.depth_rename, depth_toInteger, zero_le, max_eq_right]

end NatExpr

namespace ScaledNatural

@[simp] theorem depth_graphRep {σ : Type*} {f : (σ → ℕ) → ℕ} (p : ScaledNatural f) :
    p.graphRep.depth = 1 + max 1 p.numerator.depth := by
  simp only [graphRep, Rep.depth_ofIff, Rep.depth_equality, Expr.depth,
    Expr.depth_rename, NatExpr.depth_toInteger, max_self]

@[simp] theorem depth_ofNatExpr {σ : Type*} (e : NatExpr σ) :
    (ofNatExpr e).numerator.depth = e.depth := rfl

@[simp] theorem depth_cantorPair {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (p : ScaledNatural f) (q : ScaledNatural g) :
    (p.cantorPair q).numerator.depth = 5 + max p.numerator.depth q.numerator.depth := by
  simp only [cantorPair]
  change 1 + max (1 + max (1 + max (1 + max p.numerator.depth 0)
    (1 + max q.numerator.depth 0)) (1 + max (1 + max
    (1 + max p.numerator.depth 0) (1 + max q.numerator.depth 0)) 0))
    (1 + max (1 + max 0 (1 + max q.numerator.depth 0)) 0) = _
  omega

end ScaledNatural

end DiophantineConsistency
