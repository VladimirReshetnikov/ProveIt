import Std

/-! Ground resolution, including pure-resolution pruning of a labelled decision tree.
Literals are (atom index, polarity). Clause lists may repeat literals. -/
namespace FirstOrderIPRA.GroundResolution

abbrev Lit := Nat × Bool
abbrev Clause := List Lit

def literalBit (v : Nat → Bool) (l : Lit) : Bool := v l.1 == l.2

def remove (c : Clause) (l : Lit) : Clause := c.filter (fun x => decide (x ≠ l))

def resolvent (p : Nat) (a b : Clause) : Clause :=
  remove a (p, true) ++ remove b (p, false)

inductive Proof where
  | leaf (i : Nat)
  | resolve (p : Nat) (positive negative : Proof)
  deriving Repr

def check (g : List Clause) : Proof → Option Clause
  | .leaf i => g[i]?
  | .resolve p left right =>
    match check g left, check g right with
    | some a, some b =>
      if (p, true) ∈ a ∧ (p, false) ∈ b then some (resolvent p a b) else none
    | _, _ => none

private theorem keepTrue (v : Nat → Bool) (c : Clause) (q : Lit)
    (hq : literalBit v q = false) (hc : c.any (literalBit v) = true) :
    (remove c q).any (literalBit v) = true := by
  obtain ⟨x, hx, ht⟩ := List.any_eq_true.mp hc
  have hne : x ≠ q := by
    intro h
    subst x
    simp [hq] at ht
  exact List.any_eq_true.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simpa using hne⟩, ht⟩

theorem resolvent_sound (v : Nat → Bool) (p : Nat) (a b : Clause)
    (ha : a.any (literalBit v) = true) (hb : b.any (literalBit v) = true) :
    (resolvent p a b).any (literalBit v) = true := by
  cases hp : v p with
  | false =>
    have ht := keepTrue v a (p, true) (by simp [literalBit, hp]) ha
    simp [resolvent, List.any_append, ht]
  | true =>
    have ht := keepTrue v b (p, false) (by simp [literalBit, hp]) hb
    simp [resolvent, List.any_append, ht]

theorem check_sound {g : List Clause} (v : Nat → Bool)
    (hg : ∀ c ∈ g, c.any (literalBit v) = true)
    (t : Proof) {c : Clause} (h : check g t = some c) :
    c.any (literalBit v) = true := by
  induction t generalizing c with
  | leaf i => exact hg _ (List.mem_of_getElem? h)
  | resolve p left right ihL ihR =>
    cases hl : check g left with
    | none => simp [check, hl] at h
    | some a =>
      cases hr : check g right with
      | none => simp [check, hl, hr] at h
      | some b =>
        by_cases piv : (p, true) ∈ a ∧ (p, false) ∈ b
        · simp [check, hl, hr, piv] at h
          subst c
          exact resolvent_sound v p a b (ihL hl) (ihR hr)
        · simp [check, hl, hr, piv] at h

theorem rejects_model {g : List Clause} {t : Proof} (h : check g t = some [])
    (v : Nat → Bool) : ¬ (∀ c ∈ g, c.any (literalBit v) = true) := by
  intro model
  have impossible := check_sound v model t h
  simp at impossible

/- A Cover records the finite decision tree produced by assigning atoms.
At a leaf the chosen input clause consists only of literals forbidden by the path. -/
inductive Cover (g : List Clause) : Clause → Type where
  | leaf {path} (i : Nat) (c : Clause) (entry : g[i]? = some c)
      (subset : c ⊆ path) : Cover g path
  | split {path} (p : Nat) (left : Cover g ((p, true) :: path))
      (right : Cover g ((p, false) :: path)) : Cover g path

structure Derived (g : List Clause) (path : Clause) where
  clause : Clause
  proof : Proof
  checked : check g proof = some clause
  subset : clause ⊆ path

private theorem discardHead {z : Lit} {c path : Clause} (h : c ⊆ z :: path)
    (missing : z ∉ c) : c ⊆ path := by
  intro x hx
  rcases List.mem_cons.mp (h hx) with he | he
  · exact False.elim (missing (he ▸ hx))
  · exact he

private theorem withoutPivot {z : Lit} {c path : Clause} (h : c ⊆ z :: path) :
    remove c z ⊆ path := by
  intro x hx
  obtain ⟨hc, hne⟩ := List.mem_filter.mp hx
  rcases List.mem_cons.mp (h hc) with he | he
  · simp [he] at hne
  · exact he

def compile {g : List Clause} {path : Clause} : Cover g path → Derived g path
  | .leaf i c entry subset => ⟨c, .leaf i, entry, subset⟩
  | .split p l r => by
    let left := compile l
    let right := compile r
    if hp : (p, true) ∈ left.clause then
      if hn : (p, false) ∈ right.clause then
        refine ⟨resolvent p left.clause right.clause, .resolve p left.proof right.proof, ?_, ?_⟩
        · simp [check, left.checked, right.checked, hp, hn]
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact withoutPivot left.subset hx
          · exact withoutPivot right.subset hx
      else
        exact ⟨right.clause, right.proof, right.checked, discardHead right.subset hn⟩
    else
      exact ⟨left.clause, left.proof, left.checked, discardHead left.subset hp⟩

theorem compile_root_checked {g : List Clause} (tree : Cover g []) :
    check g (compile tree).proof = some [] := by
  have h : (compile tree).clause ⊆ [] := (compile tree).subset
  have empty : (compile tree).clause = [] := by simpa using h
  simpa [empty] using (compile tree).checked

example : check [[(0, true)], [(0, false)]] (.resolve 0 (.leaf 0) (.leaf 1)) = some [] := by decide


/- Find the first falsified input clause by scanning; this avoids choosing a
propositional witness noncomputably. -/
private inductive LeafScan (g : List Clause) (path : Clause) where
  | found (i : Nat) (c : Clause) (hit : g[i]? = some c) (sub : c ⊆ path)
  | missing (miss : ∀ c ∈ g, ¬ c ⊆ path)

private def scanLeaf (path : Clause) : (g : List Clause) → LeafScan g path
  | [] => .missing (by simp)
  | c :: cs => by
    if h : c ⊆ path then exact .found 0 c rfl h
    else
      match scanLeaf path cs with
      | .found i d hit sub => exact .found (i + 1) d (by simpa using hit) sub
      | .missing miss =>
        exact .missing (by
          intro d hd
          rcases List.mem_cons.mp hd with e | e
          · exact e ▸ h
          · exact miss d e)

private abbrev CoversAtoms (g : List Clause) (todo : List Nat) (path : Clause) :=
  ∀ c ∈ g, ∀ l ∈ c, l.1 ∈ todo ∨ (l.1, true) ∈ path ∨ (l.1, false) ∈ path

private theorem advance {g p todo path} (sign : Bool)
    (covered : CoversAtoms g (p :: todo) path) :
    CoversAtoms g todo ((p, sign) :: path) := by
  intro c hc l hl
  rcases covered c hc l hl with h | h | h
  · rcases List.mem_cons.mp h with e | h
    · cases sign <;> simp [e]
    · exact Or.inl h
  · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
  · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

private def pathVal (path : Clause) (p : Nat) : Bool := decide ((p, false) ∈ path)

private theorem recordedIfFalse {path : Clause} {l : Lit}
    (seen : (l.1, true) ∈ path ∨ (l.1, false) ∈ path)
    (isFalse : literalBit (pathVal path) l ≠ true) : l ∈ path := by
  obtain ⟨p, sign⟩ := l
  cases sign with
  | true =>
    rcases seen with hp | hn
    · exact hp
    · exact False.elim (isFalse (by simpa [literalBit, pathVal] using hn))
  | false =>
    by_cases hn : (p, false) ∈ path
    · exact hn
    · exact False.elim (isFalse (by simp [literalBit, pathVal, hn]))

private def completeCover (g : List Clause)
    (noModel : ∀ v, ¬ ∀ c ∈ g, c.any (literalBit v) = true) :
    (todo : List Nat) → (path : Clause) → CoversAtoms g todo path → Cover g path
  | p :: todo, path, covered =>
    .split p (completeCover g noModel todo ((p, true) :: path) (advance true covered))
      (completeCover g noModel todo ((p, false) :: path) (advance false covered))
  | [], path, covered => by
    match scanLeaf path g with
    | .found i c hit sub => exact .leaf i c hit sub
    | .missing miss =>
      exfalso
      apply noModel (pathVal path)
      intro c hc
      cases h : c.any (literalBit (pathVal path)) with
      | true => rfl
      | false =>
        exfalso
        apply miss c hc
        intro l hl
        apply recordedIfFalse (by simpa using covered c hc l hl)
        exact List.any_eq_false.mp h l hl

private def atomList (g : List Clause) := g.flatMap (fun c => c.map Prod.fst)

private theorem allAtoms (g : List Clause) : CoversAtoms g (atomList g) [] := by
  intro c hc l hl
  exact Or.inl (List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)

def refute (g : List Clause) (noModel : ∀ v, ¬ ∀ c ∈ g, c.any (literalBit v) = true) : Proof :=
  (compile (completeCover g noModel (atomList g) [] (allAtoms g))).proof

theorem refute_checked (g : List Clause)
    (noModel : ∀ v, ¬ ∀ c ∈ g, c.any (literalBit v) = true) :
    check g (refute g noModel) = some [] :=
  compile_root_checked _

end FirstOrderIPRA.GroundResolution
