import BusyBeaver.ZFC.RMBisim
import BusyBeaver.ZFC.RMEquiv

/-!
Complete finite decoder-tree coverage for per-leaf binary checks.

The checker carries the complete reverse path to each leaf. Failed decoder
branches are rejected. Its soundness recovers the exact consumed path of
RegisterPath.walk, including zero extension and truncation. No program
well-formedness, no-stray assumption, or register restriction is required.
An actual closed all-sites check and binary execution soundness are separate.
-/

namespace SetTheory.BusyBeaver.ZFC.SiteCoverage

open RegisterPath RMBisim

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

inductive LeafAt : Tree → List Bool → Edge → Prop where
  | here (e : Edge) : LeafAt (.leaf e) [] e
  | left {a b : Tree} {Q : List Bool} {e : Edge} :
      LeafAt a Q e → LeafAt (.node a b) (false :: Q) e
  | right {a b : Tree} {Q : List Bool} {e : Edge} :
      LeafAt b Q e → LeafAt (.node a b) (true :: Q) e

def allSites (test : List Bool → Edge → Bool) : List Bool → Tree → Bool
  | _, .none => false
  | revPrefix, .leaf e => test revPrefix.reverse e
  | revPrefix, .node a b =>
      allSites test (false :: revPrefix) a && allSites test (true :: revPrefix) b

theorem allSites_join (test : List Bool → Edge → Bool) (revPrefix : List Bool)
    (a b : Tree) (ha : allSites test (false :: revPrefix) a = true)
    (hb : allSites test (true :: revPrefix) b = true) :
    allSites test revPrefix (.node a b) = true := Bool.and_eq_true_iff.mpr ⟨ha, hb⟩

theorem allSites_sound (test : List Bool → Edge → Bool)
    {t : Tree} {Q : List Bool} {e : Edge} (hl : LeafAt t Q e) :
    ∀ revPrefix, allSites test revPrefix t = true →
      test (revPrefix.reverse ++ Q) e = true := by
  induction hl with
  | here e =>
      intro revPrefix h
      simpa only [allSites, List.append_nil] using h
  | left hl ih =>
      intro revPrefix h
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (false :: revPrefix) (Bool.and_eq_true_iff.mp h).1
  | right hl ih =>
      intro revPrefix h
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (true :: revPrefix) (Bool.and_eq_true_iff.mp h).2

/-- The path in LeafAt is exactly the bits consumed, rather than the input
list truncated without its implicit trailing zeros. -/
theorem twalk_leafAt (t : Tree) : ∀ (P : List Bool) (i : Nat) (e : Edge) (d : Nat),
    twalk t P i = some (e, d) →
      i ≤ d ∧ LeafAt t (RMEquiv.pre P (d - i)) e := by
  induction t with
  | none => intro P i e d h; simp [twalk] at h
  | leaf e' =>
      intro P i e d h
      change some (e', i) = some (e, d) at h
      cases h
      exact ⟨Nat.le_refl _, by simpa only [Nat.sub_self, RMEquiv.pre] using LeafAt.here e'⟩
  | node a b iha ihb =>
      intro P i e d h
      rcases P with _ | ⟨_ | _, P⟩
      · obtain ⟨hd, hl⟩ := iha [] (i + 1) e d h
        refine ⟨by omega, ?_⟩
        rw [show d - i = (d - (i + 1)) + 1 by omega]
        change LeafAt (.node a b) (false :: RMEquiv.pre [] (d - (i + 1))) e
        exact .left hl
      · obtain ⟨hd, hl⟩ := iha P (i + 1) e d h
        refine ⟨by omega, ?_⟩
        rw [show d - i = (d - (i + 1)) + 1 by omega]
        change LeafAt (.node a b) (false :: RMEquiv.pre P (d - (i + 1))) e
        exact .left hl
      · obtain ⟨hd, hl⟩ := ihb P (i + 1) e d h
        refine ⟨by omega, ?_⟩
        rw [show d - i = (d - (i + 1)) + 1 by omega]
        change LeafAt (.node a b) (true :: RMEquiv.pre P (d - (i + 1))) e
        exact .right hl

theorem allSites_twalk (test : List Bool → Edge → Bool) (t : Tree)
    (h : allSites test [] t = true) (P : List Bool) (e : Edge) (d : Nat)
    (hw : twalk t P 0 = some (e, d)) : test (consume P d) e = true := by
  simpa only [List.reverse_nil, List.nil_append, Nat.sub_zero, RMEquiv.consume_eq] using
    allSites_sound test (twalk_leafAt t P 0 e d hw).2 [] h

/-- Rejecting `.none` also proves that every instruction-pointer input finds
some leaf. This asserts no operation or binary-step correctness. -/
theorem allSites_total (test : List Bool → Edge → Bool) (t : Tree) :
    ∀ revPrefix, allSites test revPrefix t = true →
      ∀ P i, ∃ e d, twalk t P i = some (e, d) := by
  induction t with
  | none => intro revPrefix h; cases h
  | leaf e => intro revPrefix h P i; exact ⟨e, i, rfl⟩
  | node a b iha ihb =>
      intro revPrefix h P i
      have hh := Bool.and_eq_true_iff.mp h
      rcases P with _ | ⟨_ | _, P⟩
      · exact iha (false :: revPrefix) hh.1 [] (i + 1)
      · exact iha (false :: revPrefix) hh.1 P (i + 1)
      · exact ihb (true :: revPrefix) hh.2 P (i + 1)

theorem allSites_walk (test : List Bool → Edge → Bool) (p : Program) (t : Tree)
    (ht : ptree p = t) (h : allSites test [] t = true)
    (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk p (p.nnodes + 1) p.root P 0 = some (e, d)) :
    test (consume P d) e = true := by
  apply allSites_twalk test t h P e d
  simpa only [← ht, ← walk_root] using hw

theorem allSites_walk_total (test : List Bool → Edge → Bool) (p : Program) (t : Tree)
    (ht : ptree p = t) (h : allSites test [] t = true) (P : List Bool) :
    ∃ e d, walk p (p.nnodes + 1) p.root P 0 = some (e, d) := by
  obtain ⟨e, d, hd⟩ := allSites_total test t [] h P 0
  exact ⟨e, d, by simpa only [← ht, ← walk_root] using hd⟩

/-- Descending into a leaf or failed branch with bits left is rejected.
This supports closed subtree chunks without duplicating the literal tree. -/
def descend : Tree → List Bool → Tree
  | t, [] => t
  | .node a _, false :: P => descend a P
  | .node _ b, true :: P => descend b P
  | _, _ :: _ => .none

def leafCount : Tree → Nat
  | .none => 0
  | .leaf _ => 1
  | .node a b => leafCount a + leafCount b

def nodeCount : Tree → Nat
  | .none | .leaf _ => 0
  | .node a b => 1 + nodeCount a + nodeCount b

def guardCount : Tree → Nat
  | .none => 0
  | .leaf (.decnz _) => 2
  | .leaf _ => 1
  | .node a b => guardCount a + guardCount b

def depth : Tree → Nat
  | .none | .leaf _ => 0
  | .node a b => 1 + max (depth a) (depth b)

end SetTheory.BusyBeaver.ZFC.SiteCoverage
