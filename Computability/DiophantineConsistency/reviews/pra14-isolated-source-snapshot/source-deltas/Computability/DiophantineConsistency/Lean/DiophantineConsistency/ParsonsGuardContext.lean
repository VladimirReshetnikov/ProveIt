import DiophantineConsistency.ParsonsGuardRewrite
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuardContext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsBlock ParsonsStructure ParsonsRule ParsonsInductionCase
open ParsonsGuardPrefix ParsonsGuardRewrite

def GoodMark : Mark → Prop
  | .side P _ => Guard P
  | .base _ => True
  | .block _ _ _ _ _ => True

def Good (es : List Mark) : Prop := ∀ e ∈ es, GoodMark e

theorem shift_goodMark (e : Mark) (h : GoodMark e) : GoodMark e.shift := by
  cases e with
  | side P hp =>
      have hr : Rew.rewrite (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) = (@Rew.shift ℒₒᵣ 0) := by
        ext i <;> simp
      simpa [GoodMark, Mark.shift, hr] using ParsonsGuardRewrite.rewrite h (fun x => &(x+1))
  | base s => trivial
  | block φ hφ n A hs => trivial

theorem shift_good (es : List Mark) (h : Good es) : Good (es.map Mark.shift) := by
  intro e he
  obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
  exact shift_goodMark e' (h e' he')

def markCost : Mark → ℕ
  | .side P _ => P.complexity
  | .base _ => 0
  | .block _ _ _ _ _ => 0

def cost (es : List Mark) : ℕ := (es.map markCost).sum

theorem cost_shift (es : List Mark) : cost (es.map Mark.shift) = cost es := by
  have he (e : Mark) : markCost e.shift = markCost e := by
    cases e with
    | side P hp => simp [markCost, Mark.shift, Rewriting.shift]
    | base s => rfl
    | block φ hφ n A hs => rfl
  simp [cost, List.map_map, Function.comp_def, he]

theorem cost_append (xs ys : List Mark) : cost (xs ++ ys) = cost xs + cost ys := by
  simp [cost]

theorem cost_cons (x : Mark) (xs : List Mark) : cost (x :: xs) = markCost x + cost xs := rfl

theorem cost_open (left right : List Mark) (A : ArithmeticSemiformula ℕ 1)
    (hp : Hierarchy 𝚷 2 (∀⁰ A)) (ha : Guard A.free) :
    cost (left.map Mark.shift ++ Mark.side A.free ha.pi :: right.map Mark.shift) <
      cost (left ++ Mark.side (∀⁰ A) hp :: right) := by
  simp only [cost_append, cost_cons, cost_shift, markCost, Semiformula.complexity_all,
    Semiformula.complexity_rew]
  omega

/-- If all marked sides have guard descriptors, either the projected side
is Σ₁ or an actual universal occurrence can be selected in place. -/
theorem sigma_or_universal (es : List Mark) (h : Good es) :
    Hierarchy 𝚺 1 (disjoin (es.map Mark.output)) ∨
      ∃ (left right : List Mark) (A : ArithmeticSemiformula ℕ 1)
        (hp : Hierarchy 𝚷 2 (∀⁰ A)) (_ha : Guard A.free),
        es = left ++ Mark.side (∀⁰ A) hp :: right := by
  induction es with
  | nil => left; simp [disjoin]
  | cons e es ih =>
      have he : GoodMark e := h e (by simp)
      have ht : Good es := by intro m hm; exact h m (by simp [hm])
      cases e with
      | side P hp =>
          cases he with
          | sigma hP =>
              rcases ih ht with hs | ⟨left,right,A,hA,ha,heq⟩
              · left; simpa [disjoin, Mark.output, Hierarchy.or_iff] using And.intro hP hs
              · right; exact ⟨.side P hp :: left, right, A,hA,ha,by simp [heq]⟩
          | all A hA ha =>
              right; exact ⟨[],es,A,hA,ha,rfl⟩
      | base s =>
          rcases ih ht with hs | ⟨left,right,A,hA,ha,heq⟩
          · left; simpa [disjoin, Mark.output, Hierarchy.or_iff] using hs
          · right; exact ⟨.base s :: left, right, A,hA,ha,by simp [heq]⟩
      | block φ hφ n A hs =>
          rcases ih ht with hsig | ⟨left,right,C,hC,hc,heq⟩
          · left; simpa [disjoin, Mark.output, Hierarchy.or_iff] using hsig
          · right; exact ⟨.block φ hφ n A hs :: left, right, C,hC,hc,by simp [heq]⟩
end DiophantineConsistency.ParsonsGuardContext
