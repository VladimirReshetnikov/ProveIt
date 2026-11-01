import DiophantineConsistency.ParsonsGuardContext
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuardTree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsStructure ParsonsGuardContext

/-- Positive Boolean trees of universal prefixes terminating in Σ₁. -/
inductive Tree : Proposition ℒₒᵣ → Prop
  | sigma {P} : Hierarchy 𝚺 1 P → Tree P
  | all (A : ArithmeticSemiformula ℕ 1) :
      Hierarchy 𝚷 2 (∀⁰ A) → Tree A.free → Tree (∀⁰ A)
  | or {P Q} : Tree P → Tree Q → Tree (P ⋎ Q)
  | and {P Q} : Tree P → Tree Q → Tree (P ⋏ Q)

theorem Tree.pi {P : Proposition ℒₒᵣ} (h : Tree P) : Hierarchy 𝚷 2 P := by
  induction h with
  | sigma h => exact h.strict_mono _ (by decide)
  | all A h _ _ => exact h
  | or _ _ ih1 ih2 => exact Hierarchy.or ih1 ih2
  | and _ _ ih1 ih2 => exact Hierarchy.and ih1 ih2

theorem rewrite {P : Proposition ℒₒᵣ} (h : Tree P) (f : ℕ → SyntacticTerm ℒₒᵣ) :
    Tree (Rew.rewrite f ▹ P) := by
  induction h generalizing f with
  | sigma h => exact .sigma (Hierarchy.rew _ h)
  | all A hA h ih =>
      have hi := ih (&0 :>ₙ fun x => Rew.shift (f x))
      have hp : Hierarchy 𝚷 2 (∀⁰ ((Rew.rewrite f).q ▹ A)) := by
        simpa using Hierarchy.rew (Rew.rewrite f) hA
      have hb : Tree (((Rew.rewrite f).q ▹ A).free) := by
        have heq : (((Rew.rewrite f).q ▹ A).free) =
            Rew.rewrite (&0 :>ₙ fun x => Rew.shift (f x)) ▹ A.free := by
          simpa only [Rew.q_rewrite, Function.comp_def] using
            (LawfulSyntacticRewriting.free_rewrite_eq f A)
        rw [heq]
        exact hi
      simpa using Tree.all ((Rew.rewrite f).q ▹ A) hp hb
  | or hP hQ ihP ihQ => simpa using Tree.or (ihP f) (ihQ f)
  | and hP hQ ihP ihQ => simpa using Tree.and (ihP f) (ihQ f)

def GoodMark : Mark → Prop
  | .side P _ => Tree P
  | .base _ => True
  | .block _ _ _ _ _ => True

def Good (es : List Mark) : Prop := ∀ e ∈ es, GoodMark e

theorem shift_good (es : List Mark) (h : Good es) : Good (es.map Mark.shift) := by
  intro e he
  obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
  have hs := h e' he'
  cases e' with
  | side P hp =>
      have hr : Rew.rewrite (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) = (@Rew.shift ℒₒᵣ 0) := by
        ext i <;> simp
      simpa [GoodMark, Mark.shift, hr] using rewrite hs (fun x => &(x+1))
  | base s => trivial
  | block φ hφ n A hs => trivial

inductive Choice (es : List Mark) : Prop
  | sigma : Hierarchy 𝚺 1 (disjoin (es.map Mark.output)) → Choice es
  | all (left right : List Mark) (A : ArithmeticSemiformula ℕ 1)
      (hp : Hierarchy 𝚷 2 (∀⁰ A)) (ha : Tree A.free) :
      es = left ++ Mark.side (∀⁰ A) hp :: right → Choice es
  | or (left right : List Mark) (P Q : Proposition ℒₒᵣ)
      (hP : Tree P) (hQ : Tree Q) :
      es = left ++ Mark.side (P ⋎ Q) (Hierarchy.or hP.pi hQ.pi) :: right → Choice es
  | and (left right : List Mark) (P Q : Proposition ℒₒᵣ)
      (hP : Tree P) (hQ : Tree Q) :
      es = left ++ Mark.side (P ⋏ Q) (Hierarchy.and hP.pi hQ.pi) :: right → Choice es

theorem choose (es : List Mark) (h : Good es) : Choice es := by
  induction es with
  | nil => apply Choice.sigma; simp [disjoin]
  | cons e es ih =>
      have he : GoodMark e := h e (by simp)
      have ht : Good es := by intro m hm; exact h m (by simp [hm])
      cases e with
      | side P hp =>
          cases he with
          | sigma hP =>
              cases ih ht with
              | sigma hs => apply Choice.sigma; simpa [disjoin, Mark.output, Hierarchy.or_iff] using And.intro hP hs
              | all left right A hA ha heq => exact .all (.side P hp :: left) right A hA ha (by simp [heq])
              | or left right P' Q hP' hQ heq => exact .or (.side P hp :: left) right P' Q hP' hQ (by simp [heq])
              | and left right P' Q hP' hQ heq => exact .and (.side P hp :: left) right P' Q hP' hQ (by simp [heq])
          | all A hA ha => exact .all [] es A hA ha rfl
          | or hP hQ => exact .or [] es _ _ hP hQ rfl
          | and hP hQ => exact .and [] es _ _ hP hQ rfl
      | base s =>
          cases ih ht with
          | sigma hs => apply Choice.sigma; simpa [disjoin, Mark.output, Hierarchy.or_iff] using hs
          | all left right A hA ha heq => exact .all (.base s :: left) right A hA ha (by simp [heq])
          | or left right P Q hP hQ heq => exact .or (.base s :: left) right P Q hP hQ (by simp [heq])
          | and left right P Q hP hQ heq => exact .and (.base s :: left) right P Q hP hQ (by simp [heq])
      | block φ hφ n A hs =>
          cases ih ht with
          | sigma hsig => apply Choice.sigma; simpa [disjoin, Mark.output, Hierarchy.or_iff] using hsig
          | all left right B hB hb heq => exact .all (.block φ hφ n A hs :: left) right B hB hb (by simp [heq])
          | or left right P Q hP hQ heq => exact .or (.block φ hφ n A hs :: left) right P Q hP hQ (by simp [heq])
          | and left right P Q hP hQ heq => exact .and (.block φ hφ n A hs :: left) right P Q hP hQ (by simp [heq])


/-- Additive logical-node count; unlike max-depth it decreases when a
selected disjunction is split into both branches. -/
def nodes {L : Language} {ξ : Type} {n : ℕ} : Semiformula L ξ n → ℕ
  | ⊤ => 1
  | ⊥ => 1
  | .rel _ _ => 1
  | .nrel _ _ => 1
  | .and P Q => nodes P + nodes Q + 1
  | .or P Q => nodes P + nodes Q + 1
  | .all P => nodes P + 1
  | .exs P => nodes P + 1

@[simp] theorem nodes_rew {L : Language} {ξ ζ : Type} {n m : ℕ}
    (ω : Rew L ξ n ζ m) (P : Semiformula L ξ n) : nodes (ω ▹ P) = nodes P := by
  induction P using Semiformula.rec' generalizing m <;> simp [nodes, *]

def markNodes : Mark → ℕ
  | .side P _ => nodes P
  | .base _ => 0
  | .block _ _ _ _ _ => 0

def nodeCost (es : List Mark) : ℕ := (es.map markNodes).sum

theorem nodes_shift (es : List Mark) : nodeCost (es.map Mark.shift) = nodeCost es := by
  have he (e : Mark) : markNodes e.shift = markNodes e := by
    cases e with
    | side P hp => simp [markNodes, Mark.shift, Rewriting.shift]
    | base s => rfl
    | block φ hφ n A hs => rfl
  simp [nodeCost, List.map_map, Function.comp_def, he]

theorem nodes_append (xs ys : List Mark) : nodeCost (xs ++ ys) = nodeCost xs + nodeCost ys := by simp [nodeCost]
theorem nodes_cons (x : Mark) (xs : List Mark) : nodeCost (x :: xs) = markNodes x + nodeCost xs := rfl

theorem nodes_all (left right : List Mark) (A : ArithmeticSemiformula ℕ 1)
    (hp : Hierarchy 𝚷 2 (∀⁰ A)) (ha : Tree A.free) :
    nodeCost (left.map Mark.shift ++ Mark.side A.free ha.pi :: right.map Mark.shift) <
      nodeCost (left ++ Mark.side (∀⁰ A) hp :: right) := by
  simp only [nodes_append, nodes_cons, nodes_shift, markNodes, nodes, nodes_rew]
  omega

theorem nodes_or (left right : List Mark) (P Q : Proposition ℒₒᵣ) (hp : Hierarchy 𝚷 2 P) (hq : Hierarchy 𝚷 2 Q) :
    nodeCost (left ++ Mark.side P hp :: Mark.side Q hq :: right) <
      nodeCost (left ++ Mark.side (P ⋎ Q) (Hierarchy.or hp hq) :: right) := by
  simp only [nodes_append, nodes_cons, markNodes, nodes]
  omega

theorem nodes_and (left right : List Mark) (P Q : Proposition ℒₒᵣ) (hp : Hierarchy 𝚷 2 P) (hq : Hierarchy 𝚷 2 Q) :
    nodeCost (left ++ Mark.side P hp :: right) <
      nodeCost (left ++ Mark.side (P ⋏ Q) (Hierarchy.and hp hq) :: right) ∧
    nodeCost (left ++ Mark.side Q hq :: right) <
      nodeCost (left ++ Mark.side (P ⋏ Q) (Hierarchy.and hp hq) :: right) := by
  simp only [nodes_append, nodes_cons, markNodes, nodes]
  omega
end DiophantineConsistency.ParsonsGuardTree
