import Lean

/-!
Core-only verification of iteration-graph preservation and fusion.

`Index` is deliberately not assumed to be Lean's Nat. In the intended
application it is the ambient model domain; `Valid n` means n belongs to
that model's internal omega. The client supplies induction for the EXACT
displayed invariant. This file never assumes external induction for all
predicates of a possibly nonstandard omega.

Integration with ThetaG and construction of the object-language formula
representing the invariant remain production obligations.
-/

namespace IterationGraph

structure IndexDomain (Index : Type) where
  zero : Index
  succ : Index → Index
  Valid : Index → Prop

def InductionFor (D : IndexDomain Index) (P : Index → Prop) : Prop :=
  P D.zero →
    (∀ n, D.Valid n → P n → P (D.succ n)) →
      ∀ n, D.Valid n → P n

structure Graph (D : IndexDomain Index) (Step : State → State) where
  Run : State → State → Index → Prop
  valid : ∀ {a z n}, Run a z n → D.Valid n
  total : ∀ a n, D.Valid n → ∃ z, Run a z n
  initial : ∀ a, Run a a D.zero
  advance : ∀ {a z n}, D.Valid n → Run a z n → Run a (Step z) (D.succ n)
  unique : ∀ {a z z' n}, Run a z n → Run a z' n → z = z'

variable {Index State Target : Type} {D : IndexDomain Index}
  {Step : State → State} {Next : Target → Target}

/-- The exact invariant for which the model must supply definable induction. -/
def PreservedStage (G : Graph D Step) (a : State) (P : State → Prop)
    (n : Index) : Prop := ∀ z, G.Run a z n → P z

theorem preserves (G : Graph D Step) (a : State) (P : State → Prop)
    (ind : InductionFor D (PreservedStage G a P))
    (initial : P a) (closed : ∀ z, P z → P (Step z))
    {n : Index} {z : State} (run : G.Run a z n) : P z := by
  have base : PreservedStage G a P D.zero := by
    intro z hz
    have he : z = a := G.unique hz (G.initial a)
    exact he ▸ initial
  have step : ∀ n, D.Valid n → PreservedStage G a P n →
      PreservedStage G a P (D.succ n) := by
    intro n hn ih z hz
    obtain ⟨w, hw⟩ := G.total a n hn
    have he : z = Step w := G.unique hz (G.advance hn hw)
    rw [he]
    exact closed w (ih w hw)
  exact ind base step n (G.valid run) z run

def FusionStage (G : Graph D Step) (H : Graph D Next)
    (h : State → Target) (a : State) (n : Index) : Prop :=
  ∀ z, G.Run a z n → H.Run (h a) (h z) n

/-- A commuting map transports the whole recursive graph at every admissible
internal index, provided this precise graph predicate has induction. -/
theorem fusion (G : Graph D Step) (H : Graph D Next)
    (h : State → Target) (a : State)
    (ind : InductionFor D (FusionStage G H h a))
    (commute : ∀ z, h (Step z) = Next (h z))
    {n : Index} {z : State} (run : G.Run a z n) : H.Run (h a) (h z) n := by
  have base : FusionStage G H h a D.zero := by
    intro z hz
    have he : z = a := G.unique hz (G.initial a)
    rw [he]
    exact H.initial (h a)
  have step : ∀ n, D.Valid n → FusionStage G H h a n →
      FusionStage G H h a (D.succ n) := by
    intro n hn ih z hz
    obtain ⟨w, hw⟩ := G.total a n hn
    have he : z = Step w := G.unique hz (G.advance hn hw)
    rw [he, commute]
    exact H.advance hn (ih w hw)
  exact ind base step n (G.valid run) z run

#print axioms preserves
#print axioms fusion

end IterationGraph
