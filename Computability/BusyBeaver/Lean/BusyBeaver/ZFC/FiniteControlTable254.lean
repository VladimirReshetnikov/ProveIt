import BusyBeaver.ZFC.SitesPerm252
import BusyBeaver.ZFC.RegisterPathClean

set_option autoImplicit false

/-!
Derived literal control catalogue and deterministic consumed-path resolver.
The catalogue is constructed from the already bound ActualTree254.tree; it is
not a generated second program. No binary site/guard computation is repeated.
This layer supplies the actual 6,460 source instructions and a deterministic
ranked consumed-path resolver. Arithmetic lookup/runtime binding remains open.
-/
namespace SetTheory.BusyBeaver.ZFC.FiniteControlTable254
open RegisterPath RegisterPathClean RMBisim SiteCoverage
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- False-first DFS catalogue; paths contain precisely the consumed leaf bits. -/
def leafEntries : Tree → List (List Bool × Edge)
  | .none => []
  | .leaf e => [([],e)]
  | .node a b =>
      (leafEntries a).map (fun entry => (false::entry.1,entry.2)) ++
      (leafEntries b).map (fun entry => (true::entry.1,entry.2))

theorem leafEntries_length (t : Tree) : (leafEntries t).length = leafCount t := by
  induction t with
  | none => rfl
  | leaf e => rfl
  | node a b iha ihb =>
    simp only [leafEntries,List.length_append,List.length_map,leafCount,iha,ihb]

theorem leafEntries_sound (t : Tree) (P : List Bool) (e : Edge)
    (hm : (P,e) ∈ leafEntries t) : LeafAt t P e := by
  induction t generalizing P e with
  | none => simp [leafEntries] at hm
  | leaf e' =>
    simp only [leafEntries,List.mem_singleton] at hm
    cases hm
    exact .here e'
  | node a b iha ihb =>
    rcases List.mem_append.mp hm with hl | hr
    · obtain ⟨⟨Q,e'⟩,hQ,he⟩ := List.mem_map.mp hl
      cases he
      exact .left (iha Q e' hQ)
    · obtain ⟨⟨Q,e'⟩,hQ,he⟩ := List.mem_map.mp hr
      cases he
      exact .right (ihb Q e' hQ)

theorem prefix_injective (b : Bool) :
    Function.Injective (fun entry : List Bool × Edge => (b::entry.1,entry.2)) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z : List Bool × Edge => z.1.tail) h
  · have hh := congrArg (fun z : List Bool × Edge => z.2) h
    exact hh

/-- Distinct catalogue slots denote distinct complete source paths/edges. -/
theorem leafEntries_nodup (t : Tree) : (leafEntries t).Nodup := by
  induction t with
  | none => simp [leafEntries]
  | leaf e => simp [leafEntries]
  | node a b iha ihb =>
    apply List.nodup_append.mpr
    refine ⟨?_,?_,?_⟩
    · exact List.Pairwise.map _ (fun x y hxy heq => hxy (prefix_injective false heq)) iha
    · exact List.Pairwise.map _ (fun x y hxy heq => hxy (prefix_injective true heq)) ihb
    · intro x hx y hy hxy
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
      have hh := congrArg (fun z : List Bool × Edge => z.1.head?) hxy
      simp at hh

theorem leafEntries_complete {t : Tree} {P : List Bool} {e : Edge}
    (hl : LeafAt t P e) : (P,e) ∈ leafEntries t := by
  induction hl with
  | here e => simp [leafEntries]
  | left hl ih =>
    exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨_,ih,rfl⟩))
  | right hl ih =>
    exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨_,ih,rfl⟩))

theorem leafAt_twalk {t : Tree} {P : List Bool} {e : Edge}
    (hl : LeafAt t P e) : ∀ i, twalk t P i = some (e,i+P.length) := by
  induction hl with
  | here e => intro i; simp [twalk]
  | left hl ih =>
    intro i
    simpa only [twalk,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using ih (i+1)
  | right hl ih =>
    intro i
    simpa only [twalk,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using ih (i+1)

/-- Directly derived from the actual source tree, with its existing proof of
identity to the 6,459-node literal public program. -/
def actualEntries : List (List Bool × Edge) := leafEntries ActualTree254.tree

theorem actualEntries_length : actualEntries.length = 6460 := by
  rw [actualEntries,leafEntries_length]
  exact SitesPerm252.leaf_count

abbrev Control := Fin 6460

def source (i : Control) : List Bool × Edge :=
  actualEntries[i.val]'(by rw [actualEntries_length]; exact i.isLt)

def number (i : Control) : Nat := i.val+1

theorem source_mem (i : Control) : source i ∈ actualEntries := List.getElem_mem _

theorem source_leaf (i : Control) : LeafAt ActualTree254.tree (source i).1 (source i).2 :=
  leafEntries_sound _ _ _ (source_mem i)

/-- Acceptance is inherited from the existing closed full tree theorem.
It does not evaluate checkSite again, for any individual source instruction. -/
theorem source_accepted (i : Control) :
    SitePerm252.checkSite (source i).1 (source i).2 = true := by
  simpa only [List.reverse_nil,List.nil_append] using
    allSites_sound SitePerm252.checkSite (source_leaf i) [] SitesPerm252.all_sites

theorem source_length (i : Control) : (source i).1.length ≤ 40 :=
  SitePerm252.checkSite_length _ _ (source_accepted i)

theorem source_walk (i : Control) :
    walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root (source i).1 0 =
      some ((source i).2,(source i).1.length) := by
  rw [walk_root,ActualTree254.tree_eq]
  simpa only [Nat.zero_add] using leafAt_twalk (source_leaf i) 0

theorem source_follow (i : Control) :
    follow Prog254.program (.node Prog254.program.root) (source i).1 = some (source i).2 := by
  have hf := walk_follow_consume Prog254.program (source i).1 (source i).2
    (source i).1.length (source_walk i)
  simpa only [consume,List.take_append_length] using hf

theorem actualEntries_nodup : actualEntries.Nodup := leafEntries_nodup _

theorem source_injective : Function.Injective source := by
  intro i j h
  apply Fin.ext
  exact (List.getElem_inj actualEntries_nodup).mp h

theorem consume_self (P : List Bool) : consume P P.length = P := by
  simp only [consume,List.take_append_length]

/-- Existing walk/tree/consume facts place every actually decoded leaf in the
catalogue; implicit trailing zeros and exact consumed depth are retained. -/
theorem walk_entry_mem (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0 = some (e,d)) :
    (consume P d,e) ∈ actualEntries := by
  have ht : twalk ActualTree254.tree P 0 = some (e,d) := by
    simpa only [walk_root,ActualTree254.tree_eq] using hw
  have hl := (twalk_leafAt ActualTree254.tree P 0 e d ht).2
  apply leafEntries_complete
  simpa only [Nat.sub_zero,RMEquiv.consume_eq] using hl

theorem entry_at_index {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (entry : α)
    (hm : entry ∈ xs) :
    xs[xs.idxOf entry]'(List.idxOf_lt_length_of_mem hm) = entry := by
  letI : DecidableEq α := instDecidableEqOfLawfulBEq
  induction xs with
  | nil => simp at hm
  | cons head tail ih =>
    by_cases heq : head = entry
    · subst head
      simp only [List.idxOf_cons_self,List.getElem_cons_zero]
    · have ht : entry ∈ tail := by
        rcases List.mem_cons.mp hm with he | ht
        · exact False.elim (heq he.symm)
        · exact ht
      have hb : (head == entry) = false := by simp [heq]
      simpa only [List.idxOf_cons,hb,cond_false,List.getElem_cons_succ] using ih ht

/-- A deterministic external finite source resolver, computed from the literal
program and its catalogue. The impossible missing-walk branch is discharged by
existing total coverage. No proof-selection function or extra oracle is used.
The returned Control is always in range, including for empty input paths. -/
def resolveControl (P : List Bool) : Control :=
  match hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0 with
  | none => False.elim (by
      obtain ⟨e,d,he⟩ := SitesPerm252.actual_walk_exists P
      rw [hw] at he
      cases he)
  | some (e,d) =>
      ⟨actualEntries.idxOf (consume P d,e),by
        have hm := List.idxOf_lt_length_of_mem (walk_entry_mem P e d hw)
        simpa only [actualEntries_length] using hm⟩

/-- This is the exact source instruction named by the computed next control.
It is a generic catalogue-index proof, not 8,390 separate successor checks. -/
theorem resolve_source (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk Prog254.program (Prog254.program.nnodes+1) Prog254.program.root P 0 = some (e,d)) :
    source (resolveControl P) = (consume P d,e) := by
  unfold resolveControl
  split
  · rename_i hh
    rw [hh] at hw
    cases hw
  · rename_i e' d' hh
    have he : (e',d') = (e,d) := Option.some.inj (hh.symm.trans hw)
    cases he
    change actualEntries[actualEntries.idxOf (consume P d,e)]'
      (List.idxOf_lt_length_of_mem (walk_entry_mem P e d hw)) = (consume P d,e)
    exact entry_at_index actualEntries (consume P d,e) (walk_entry_mem P e d hw)

theorem resolve_source_self (i : Control) : resolveControl (source i).1 = i := by
  apply source_injective
  have h := resolve_source (source i).1 (source i).2 (source i).1.length (source_walk i)
  simpa only [consume_self] using h

theorem resolve_number_valid (P : List Bool) :
    0 < number (resolveControl P) ∧ number (resolveControl P) ≤ 6460 := by
  have h := (resolveControl P).isLt
  simp only [number]
  omega

/-- Index0 is actual live control1. Establishing this costs only the first
three decision choices, not the entire table or a bootstrap replay. -/
theorem first_source : source ⟨0,by decide⟩ = ([false,false,false],.decnz 8) := by rfl

/-- The empty initial pointer decodes to the first actual control, with implicit
trailing zero bits. This finite equality executes no register or binary step. -/
theorem empty_control : resolveControl [] = ⟨0,by decide⟩ := by rfl

end SetTheory.BusyBeaver.ZFC.FiniteControlTable254
