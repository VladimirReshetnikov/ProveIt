import DiophantineConsistency.ScalarPRCode
import DiophantineConsistency.PairingRepresentation
import DiophantineConsistency.BoundedForallRepresentation

/-!
# Compiling supplied scalar primitive recursive programs

Every constructor supplies finite polynomial syntax. Primitive recursion uses an
explicit beta-function trace, with its transition condition compiled by the CRT
bounded-universal constructor.
-/

namespace DiophantineConsistency.ScalarPRRepresentation

open scoped Vector3

private def equalityGraphs {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) : Rep σ (fun v => f v = g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact (Rep.compose
    (PellRepresentation.NaturalRelation.equality
      (.var (0 : Fin 2)) (.var 1)) arguments).ofIff (fun _ => Iff.rfl)

/-- One entry of the explicit beta-function trace. -/
def entry (a b i : ℕ) : ℕ := a % ((i + 1) * b + 1)

/-- Arithmetic graph data for one trace entry. -/
def entryGraph {σ : Type*} {a b i : (σ → ℕ) → ℕ}
    (ra : GraphRep a) (rb : GraphRep b) (ri : GraphRep i) :
    GraphRep (fun v => entry (a v) (b v) (i v)) :=
  ra.mod (((ri.add (GraphRep.constant 1)).mul rb).add (GraphRep.constant 1))

/-- The checked trace theorem with an ordinary `Fin 2` existential block. -/
theorem trace_iff (f g : ℕ → ℕ) (z k out : ℕ) :
    out = Nat.rec (f z) (fun i acc => g (Nat.pair z (Nat.pair i acc))) k ↔
    ∃ t : Fin 2 → ℕ,
      entry (t 0) (t 1) 0 = f z ∧ entry (t 0) (t 1) k = out ∧
      ∀ i < k, entry (t 0) (t 1) (i + 1) =
        g (Nat.pair z (Nat.pair i (entry (t 0) (t 1) i))) := by
  rw [eq_comm, MRDP.recursionTrace_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨![v.head, v.tail.head], hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨[v 0, v 1], hv⟩

/-- Inputs are the original parameter and recursion length; the extra block
contains the two beta-function encoding parameters. -/
abbrev TraceVar := Option (Fin 2) ⊕ Fin 2

/-- Coordinate graph data for a scalar primitive recursion. -/
def recursionCoordinates {f g : ℕ → ℕ}
    (rf : GraphRep (fun v : Fin 1 → ℕ => f (v 0)))
    (rg : GraphRep (fun v : Fin 1 → ℕ => g (v 0))) :
    GraphRep (fun v : Fin 2 → ℕ =>
      Nat.rec (f (v 0)) (fun i acc => g (Nat.pair (v 0) (Nat.pair i acc))) (v 1)) := by
  let a : GraphRep (fun v : TraceVar → ℕ => v (.inr 0)) :=
    GraphRep.coordinate (Sum.inr (0 : Fin 2) : TraceVar)
  let b : GraphRep (fun v : TraceVar → ℕ => v (.inr 1)) :=
    GraphRep.coordinate (Sum.inr (1 : Fin 2) : TraceVar)
  let z : GraphRep (fun v : TraceVar → ℕ => v (.inl (some 0))) :=
    GraphRep.coordinate (Sum.inl (some (0 : Fin 2)) : TraceVar)
  let k : GraphRep (fun v : TraceVar → ℕ => v (.inl (some 1))) :=
    GraphRep.coordinate (Sum.inl (some (1 : Fin 2)) : TraceVar)
  let out : GraphRep (fun v : TraceVar → ℕ => v (.inl none)) :=
    GraphRep.coordinate (Sum.inl none : TraceVar)
  let base := GraphRep.compose rf (fun _ : Fin 1 => z)
  let initial := equalityGraphs (entryGraph a b (GraphRep.constant 0)) base
  let final := equalityGraphs (entryGraph a b k) out
  let i : GraphRep (fun v : Option TraceVar → ℕ => v none) := GraphRep.coordinate none
  let aa := a.reindex some
  let bb := b.reindex some
  let zz := z.reindex some
  let before := entryGraph aa bb i
  let after := entryGraph aa bb (i.add (GraphRep.constant 1))
  let stepInput := zz.pair (i.pair before)
  let stepOutput := GraphRep.compose rg (fun _ : Fin 1 => stepInput)
  let transitions := (equalityGraphs after stepOutput).boundedForall (.inl (some 1))
  let certificate := (initial.conjunction (final.conjunction transitions)).existsBlock
  refine certificate.ofIff ?_
  intro v
  change (∃ t : Fin 2 → ℕ,
    entry (t 0) (t 1) 0 = f (v (some 0)) ∧
    entry (t 0) (t 1) (v (some 1)) = v none ∧
    ∀ i < v (some 1), entry (t 0) (t 1) (i + 1) =
      g (Nat.pair (v (some 0)) (Nat.pair i (entry (t 0) (t 1) i)))) ↔ _
  exact (trace_iff f g (v (some 0)) (v (some 1)) (v none)).symm

end DiophantineConsistency.ScalarPRRepresentation

namespace DiophantineConsistency.ScalarPRCode

/-- Compile an explicitly supplied scalar primitive recursive program to
finite Diophantine representation data, by structural recursion on the program. -/
def graphRep : (c : ScalarPRCode) → GraphRep (fun v : Fin 1 → ℕ => c.eval (v 0))
  | .zero => GraphRep.constant 0
  | .succ => (GraphRep.coordinate 0).add (GraphRep.constant 1)
  | .left => (GraphRep.coordinate 0).unpairLeft
  | .right => (GraphRep.coordinate 0).unpairRight
  | .pair f g => f.graphRep.pair g.graphRep
  | .comp f g => GraphRep.compose f.graphRep (fun _ : Fin 1 => g.graphRep)
  | .prec f g =>
      let input : GraphRep (fun v : Fin 1 → ℕ => v 0) := GraphRep.coordinate 0
      let arguments : ∀ i : Fin 2, GraphRep
          (![fun v : Fin 1 → ℕ => (v 0).unpair.1,
             fun v : Fin 1 → ℕ => (v 0).unpair.2] i) :=
        Fin.cases input.unpairLeft
          (Fin.cases input.unpairRight (fun i => Fin.elim0 i))
      GraphRep.compose
        (ScalarPRRepresentation.recursionCoordinates f.graphRep g.graphRep) arguments

end DiophantineConsistency.ScalarPRCode

namespace DiophantineConsistency.ScalarPRCode.Realizes

/-- Preserve a supplied program's specification while compiling its syntax. -/
def graphRep {f : ℕ → ℕ} (p : Realizes f) :
    GraphRep (fun v : Fin 1 → ℕ => f (v 0)) :=
  p.val.graphRep.ofIff (fun v => by
    change (v none = p.val.eval (v (some 0))) ↔ v none = f (v (some 0))
    rw [p.property])

end DiophantineConsistency.ScalarPRCode.Realizes
