import Init

/-!
Finite observations of Baire names.  This file proves the semantic interfaces
in Lean.  `Reader` is a host-language structure.  Its first-order instances
require fixed PR implementations of the five fields, as specified in the report.
-/
namespace BoundedOracle

abbrev Name := Nat → Nat

/-- A transducer with an input-dependent number of answer slots. -/
structure Reader where
  init : Nat → Nat
  ask : Nat → Nat
  update : Nat → Nat → Nat
  out : Nat → Nat
  slots : Nat → Nat

namespace Reader

def state (p : Reader) (a : Name) (n : Nat) : Nat → Nat
  | 0 => p.init n
  | i + 1 =>
    let s := p.state a n i
    p.update s (a (p.ask s))

def query (p : Reader) (a : Name) (n i : Nat) : Nat := p.ask (p.state a n i)

def observe (p : Reader) (a : Name) (n : Nat) : Nat :=
  p.out (p.state a n (p.slots n))

/-- Agreement on the first run's actual queries suffices, including for an
adaptive reader. No hypothesis on the second query schedule is required. -/
theorem replay (p : Reader) (a b : Name) (n t : Nat)
    (h : ∀ i, i < t → a (p.query a n i) = b (p.query a n i)) :
    p.state a n t = p.state b n t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self t)))
    have ha := h t (Nat.lt_succ_self t)
    change a (p.ask (p.state a n t)) = b (p.ask (p.state a n t)) at ha
    simp only [state]
    rw [ha, hs]

/-- A finite word, extended by a deterministic default outside its length. -/
def lookup (w : List Nat) (q : Nat) : Nat := w[q]?.getD 0

def sample (a : Name) (u : Nat) : List Nat := List.ofFn (fun i : Fin u => a i.val)

theorem lookup_sample (a : Name) (u j : Nat) (hj : j < u) :
    lookup (sample a u) j = a j := by
  simp [lookup, sample, hj]

/-- The window length is an exclusive bound on all indices that are read. -/
def Uses (p : Reader) (u : Nat → Nat) : Prop :=
  ∀ (a : Name) (n i : Nat), i < p.slots n → p.query a n i < u n

/-- This obligation quantifies only over finite words and natural numbers. -/
def TableGuard (p : Reader) (u : Nat → Nat) : Prop :=
  ∀ (w : List Nat) (n i : Nat), w.length = u n → i < p.slots n →
    p.query (lookup w) n i < u n

theorem tableGuard_iff_uses (p : Reader) (u : Nat → Nat) :
    p.TableGuard u ↔ p.Uses u := by
  constructor
  · intro hg a n i hi
    let w := sample a (u n)
    have hw : w.length = u n := by simp [w, sample]
    have hq := hg w n i hw hi
    have hs : p.state (lookup w) n i = p.state a n i := by
      apply p.replay
      intro j hj
      exact lookup_sample a (u n) _ (hg w n j hw (Nat.lt_trans hj hi))
    change p.ask (p.state a n i) < u n
    rw [← hs]
    exact hq
  · intro hu w n i _ hi
    exact hu (lookup w) n i hi

theorem read_sample (p : Reader) (u : Nat → Nat) (hu : p.Uses u)
    (a : Name) (n : Nat) :
    p.observe (lookup (sample a (u n))) n = p.observe a n := by
  apply congrArg p.out
  symm
  apply p.replay
  intro i hi
  exact (lookup_sample a (u n) _ (hu a n i hi)).symm

end Reader

/-- The representation-independent part of a modulus certificate. -/
structure WindowMap where
  observe : Name → Name
  window : Nat → Nat
  monotone : ∀ {i j : Nat}, i ≤ j → window i ≤ window j
  stable : ∀ (a b : Name) (n : Nat),
    (∀ j, j < window n → a j = b j) → observe a n = observe b n

def Reader.toWindowMap (p : Reader) (u : Nat → Nat) (hu : p.Uses u)
    (hm : ∀ {i j : Nat}, i ≤ j → u i ≤ u j) : WindowMap where
  observe := p.observe
  window := u
  monotone := hm
  stable := by
    intro a b n h
    apply congrArg p.out
    exact p.replay a b n _ (fun i hi => h _ (hu a n i hi))

/-- `f` is run first, and its output oracle supplies the requests of `g`. -/
def WindowMap.thenMap (f g : WindowMap) : WindowMap where
  observe a := g.observe (f.observe a)
  window n := f.window (g.window n)
  monotone h := f.monotone (g.monotone h)
  stable := by
    intro a b n h
    apply g.stable
    intro k hk
    apply f.stable
    intro j hj
    exact h j (Nat.lt_of_lt_of_le hj (f.monotone (Nat.le_of_lt hk)))

/-- Compatibility with equality of represented points is a separate duty. -/
def Respects (f : Name → Name) (r s : Name → Name → Prop) : Prop :=
  ∀ a b, r a b → s (f a) (f b)

theorem respects_comp {r s t : Name → Name → Prop} {f g : Name → Name}
    (hf : Respects f r s) (hg : Respects g s t) :
    Respects (fun a => g (f a)) r t := by
  intro a b h
  exact hg _ _ (hf _ _ h)

/-- A two-query operation exhibiting the need for local size parameters. -/
def jump (a : Name) : Nat := a (a 0 + 1)

theorem jump_local (a b : Name) (h₀ : a 0 = b 0)
    (h₁ : a (a 0 + 1) = b (a 0 + 1)) : jump a = jump b := by
  unfold jump
  rw [h₁, h₀]

theorem jump_no_window (m : Nat) :
    ∃ a b : Name, (∀ j, j < m → a j = b j) ∧ jump a ≠ jump b := by
  let a : Name := fun _ => m
  let b : Name := fun j => if j = m + 1 then m + 1 else m
  refine ⟨a, b, ?_, ?_⟩
  · intro j hj
    have hne : j ≠ m + 1 := Nat.ne_of_lt (Nat.lt_trans hj (Nat.lt_succ_self m))
    exact (if_neg hne).symm
  · have hb₀ : b 0 = m := if_neg (Nat.zero_ne_add_one m)
    have hjb : jump b = m + 1 := calc
      b (b 0 + 1) = b (m + 1) := congrArg (fun k => b (k + 1)) hb₀
      _ = m + 1 := if_pos rfl
    intro heq
    exact (Nat.ne_of_lt (Nat.lt_succ_self m)) (heq.trans hjb)

end BoundedOracle
