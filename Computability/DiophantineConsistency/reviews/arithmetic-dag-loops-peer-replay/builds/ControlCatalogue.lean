import BusyBeaver.ZFC.SiteCoverage

set_option autoImplicit false

/-!
# Control catalogues of decoder trees, with fast resolution

The numbered control interpreters number the leaves of a decoder tree in
false-first depth-first order (`leafEntries`, the same definition as in
`FiniteControlTable254`). A path is resolved to the leaf it decodes to, and
the leaf's index in that list is its control index.

Looking the leaf up with `List.idxOf` costs time linear in the catalogue; the
kernel would need several minutes to resolve every successor of a 6,460-leaf
tree. This module computes the same index by one descent through a tree whose
nodes record the leaf count of their left subtree (`crank`), and proves that
the ranked slot holds the decoded leaf (`entry_at_crank`). Braun trees (`BT`)
give logarithmic lookup of row and certificate tables. Everything here is
external finite data.
-/

namespace SetTheory.BusyBeaver.ZFC.ControlCatalogue

open RegisterPath RMBisim SiteCoverage

/-- False-first DFS catalogue; paths contain precisely the consumed leaf bits. -/
def leafEntries : Tree → List (List Bool × Edge)
  | .none => []
  | .leaf e => [([], e)]
  | .node a b =>
      (leafEntries a).map (fun entry => (false :: entry.1, entry.2)) ++
      (leafEntries b).map (fun entry => (true :: entry.1, entry.2))

theorem leafEntries_length (t : Tree) : (leafEntries t).length = leafCount t := by
  induction t with
  | none => rfl
  | leaf e => rfl
  | node a b iha ihb =>
    simp only [leafEntries, List.length_append, List.length_map, leafCount, iha, ihb]

theorem prefix_injective (b : Bool) :
    Function.Injective (fun entry : List Bool × Edge => (b :: entry.1, entry.2)) := by
  intro x y h
  have h' : (b :: x.1, x.2) = (b :: y.1, y.2) := h
  rcases x with ⟨xp, xe⟩
  rcases y with ⟨yp, ye⟩
  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h' ⊢
  exact h'

/-- Distinct catalogue slots denote distinct complete source paths/edges. -/
theorem leafEntries_nodup (t : Tree) : (leafEntries t).Nodup := by
  induction t with
  | none => simp [leafEntries]
  | leaf e => simp [leafEntries]
  | node a b iha ihb =>
    apply List.nodup_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map _ (fun x y hxy heq => hxy (prefix_injective false heq)) iha
    · exact List.Pairwise.map _ (fun x y hxy heq => hxy (prefix_injective true heq)) ihb
    · intro x hx y hy hxy
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
      have hh := congrArg (fun z : List Bool × Edge => z.1.head?) hxy
      simp at hh

theorem leafEntries_sound (t : Tree) (P : List Bool) (e : Edge)
    (hm : (P, e) ∈ leafEntries t) : LeafAt t P e := by
  induction t generalizing P e with
  | none => simp [leafEntries] at hm
  | leaf e' =>
    simp only [leafEntries, List.mem_singleton] at hm
    cases hm
    exact .here e'
  | node a b iha ihb =>
    rcases List.mem_append.mp hm with hl | hr
    · obtain ⟨⟨Q, e'⟩, hQ, he⟩ := List.mem_map.mp hl
      cases he
      exact .left (iha Q e' hQ)
    · obtain ⟨⟨Q, e'⟩, hQ, he⟩ := List.mem_map.mp hr
      cases he
      exact .right (ihb Q e' hQ)

/-- A decoder tree whose nodes record the leaf count of their left child. -/
inductive CTree where
  | none
  | leaf (e : Edge)
  | node (n : Nat) (a b : CTree)

def annotate : Tree → CTree
  | .none => .none
  | .leaf e => .leaf e
  | .node a b => .node (leafCount a) (annotate a) (annotate b)

/-- Catalogue index of the leaf decoded from a path, with implicit trailing
zero bits, by one descent. -/
def crank : CTree → List Bool → Nat
  | .node _ a _, [] => crank a []
  | .node _ a _, false :: P => crank a P
  | .node n _ b, true :: P => n + crank b P
  | _, _ => 0

/-- Padding beyond the consumed depth is irrelevant. -/
theorem take_pad (P : List Bool) (k j : Nat) :
    (P ++ List.replicate (k + j) false).take k = (P ++ List.replicate k false).take k := by
  induction P generalizing k j with
  | nil => simp [List.take_replicate]
  | cons x P ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, List.take_succ_cons]
      rw [show k + 1 + j = k + (j + 1) by omega, ih k (j+1), show k + 1 = k + 1 by rfl,
        ← ih k 1]

theorem consume_succ (P : List Bool) (k : Nat) :
    (P ++ false :: List.replicate k false).take k = (P ++ List.replicate k false).take k := by
  rw [← List.replicate_succ, take_pad P k 1]

theorem twalk_le (t : Tree) (P : List Bool) (i : Nat) (e : Edge) (d : Nat)
    (h : twalk t P i = some (e, d)) : i ≤ d := (twalk_leafAt t P i e d h).1

/-- The ranked slot holds exactly the decoded leaf and its consumed bits. -/
theorem entry_at_crank (t : Tree) (P : List Bool) (i : Nat) (e : Edge) (d : Nat)
    (h : twalk t P i = some (e, d)) :
    ∃ hr : crank (annotate t) P < (leafEntries t).length,
      (leafEntries t)[crank (annotate t) P] = (consume P (d - i), e) := by
  induction t generalizing P i with
  | none => simp [twalk] at h
  | leaf e' =>
    change some (e', i) = some (e, d) at h
    cases h
    have hc : crank (annotate (.leaf e)) P = 0 := by cases P <;> rfl
    refine ⟨by simp [leafEntries, hc], ?_⟩
    simp [leafEntries, hc, consume]
  | node a b iha ihb =>
    cases P with
    | nil =>
      change twalk a [] (i+1) = some (e, d) at h
      have hd := twalk_le a [] (i+1) e d h
      obtain ⟨hr, he⟩ := iha [] (i+1) h
      have hr' : crank (annotate (.node a b)) [] < (leafEntries (.node a b)).length := by
        simp only [annotate, crank, leafEntries, List.length_append, List.length_map]
        omega
      refine ⟨hr', ?_⟩
      simp only [annotate, crank, leafEntries]
      rw [List.getElem_append_left (by simpa using hr), List.getElem_map, he]
      have hk : d - i = (d - (i+1)) + 1 := by omega
      simp [consume, hk, List.replicate_succ]
    | cons c P =>
      cases c with
      | false =>
        change twalk a P (i+1) = some (e, d) at h
        have hd := twalk_le a P (i+1) e d h
        obtain ⟨hr, he⟩ := iha P (i+1) h
        have hr' : crank (annotate (.node a b)) (false :: P) <
            (leafEntries (.node a b)).length := by
          simp only [annotate, crank, leafEntries, List.length_append, List.length_map]
          omega
        refine ⟨hr', ?_⟩
        simp only [annotate, crank, leafEntries]
        rw [List.getElem_append_left (by simpa using hr), List.getElem_map, he]
        have hk : d - i = (d - (i+1)) + 1 := by omega
        simp only [consume, hk, List.cons_append, List.take_succ_cons, List.replicate_succ]
        rw [consume_succ]
      | true =>
        change twalk b P (i+1) = some (e, d) at h
        have hd := twalk_le b P (i+1) e d h
        obtain ⟨hr, he⟩ := ihb P (i+1) h
        have hlen : (leafEntries a).length = leafCount a := leafEntries_length a
        have hr' : crank (annotate (.node a b)) (true :: P) <
            (leafEntries (.node a b)).length := by
          simp only [annotate, crank, leafEntries, List.length_append, List.length_map]
          omega
        refine ⟨hr', ?_⟩
        simp only [annotate, crank, leafEntries]
        rw [List.getElem_append_right (by simp [hlen]), List.getElem_map]
        simp only [List.length_map, hlen, Nat.add_sub_cancel_left]
        rw [he]
        have hk : d - i = (d - (i+1)) + 1 := by omega
        simp only [consume, hk, List.cons_append, List.take_succ_cons, List.replicate_succ]
        rw [consume_succ]

/-! ## Balanced lookup trees -/

/-- A Braun tree: index `0` at the root, odd successors left, even right. -/
inductive BT (α : Type) where
  | leaf
  | node (l : BT α) (x : α) (r : BT α)
  deriving DecidableEq

def evens {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evens xs

def odds {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: odds xs

theorem evens_length_le {α : Type} (xs : List α) : (evens xs).length ≤ xs.length := by
  induction xs using evens.induct <;> simp [evens] <;> omega

theorem odds_length_le {α : Type} (xs : List α) : (odds xs).length ≤ xs.length := by
  induction xs using odds.induct <;> simp [odds] <;> omega

/-- Structural recursion on explicit fuel (kernel-fast; no well-founded unfolding). -/
def BT.ofListF {α : Type} : Nat → List α → BT α
  | 0, _ => .leaf
  | _, [] => .leaf
  | f+1, x :: xs => .node (BT.ofListF f (evens xs)) x (BT.ofListF f (odds xs))

def BT.ofList {α : Type} (xs : List α) : BT α := BT.ofListF xs.length xs

def BT.get {α : Type} : BT α → Nat → Option α
  | .leaf, _ => none
  | .node _ x _, 0 => some x
  | .node l _ r, n+1 => if n % 2 = 0 then BT.get l (n / 2) else BT.get r (n / 2)

theorem evens_get {α : Type} (xs : List α) (k : Nat) : (evens xs)[k]? = xs[2*k]? := by
  induction xs using evens.induct generalizing k with
  | case1 => simp [evens]
  | case2 x => cases k <;> simp [evens]
  | case3 x y xs ih =>
    cases k with
    | zero => simp [evens]
    | succ k =>
      rw [show 2*(k+1) = 2*k+1+1 by omega]
      simp [evens, ih]

theorem odds_get {α : Type} (xs : List α) (k : Nat) : (odds xs)[k]? = xs[2*k+1]? := by
  induction xs using odds.induct generalizing k with
  | case1 => simp [odds]
  | case2 x => simp [odds]
  | case3 x y xs ih =>
    cases k with
    | zero => simp [odds]
    | succ k =>
      rw [show 2*(k+1)+1 = 2*k+1+1+1 by omega]
      simp [odds, ih]

theorem BT.get_ofListF {α : Type} (f : Nat) :
    ∀ (xs : List α), xs.length ≤ f → ∀ n, (BT.ofListF f xs).get n = xs[n]? := by
  induction f with
  | zero =>
    intro xs hx n
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [BT.ofListF, BT.get]
  | succ f ih =>
    intro xs hx n
    cases xs with
    | nil => simp [BT.ofListF, BT.get]
    | cons x xs =>
      have hl : xs.length ≤ f := by simpa using hx
      cases n with
      | zero => simp [BT.ofListF, BT.get]
      | succ n =>
        rw [BT.ofListF, BT.get, List.getElem?_cons_succ]
        by_cases h : n % 2 = 0
        · rw [if_pos h, ih (evens xs) (Nat.le_trans (evens_length_le xs) hl) (n / 2), evens_get]
          congr 1
          omega
        · rw [if_neg h, ih (odds xs) (Nat.le_trans (odds_length_le xs) hl) (n / 2), odds_get]
          congr 1
          omega

theorem BT.get_ofList {α : Type} (xs : List α) (n : Nat) : (BT.ofList xs).get n = xs[n]? :=
  BT.get_ofListF xs.length xs (Nat.le_refl _) n

end SetTheory.BusyBeaver.ZFC.ControlCatalogue
