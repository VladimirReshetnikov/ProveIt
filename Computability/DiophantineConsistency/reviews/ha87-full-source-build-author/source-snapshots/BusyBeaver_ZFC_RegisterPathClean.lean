import BusyBeaver.ZFC.RMEquiv

/-!
No stray instruction-pointer bits in Wade's path semantics.

This is an attributed Lean development of the argument in
`ZF/m254/coq/tm/RMEquiv.v`, especially lines 585–700, in Jeff's verification
of Mira-Cult's machine at upstream commit
297ab8df7e5de329605c3875b4934643b371a5e3. Wade supplied the compiler
framework. The upstream snapshot retains its own licensing status.

The main statements are generic in RegisterPath.Program. A successful step
produces a path whose bits at and beyond any subsequent successful walk's
depth are false. Consequently every configuration reached from the empty
path has this property. No acyclicity, well-formedness, or register-value
assumption is used. These statements do not assert that a walk succeeds;
walk existence is a separate obligation.

In particular, increment overflow does not erase the path: it returns an
all-false path of the same length. Both its length and its complete bit
contents are retained in the arithmetic lemmas below.
-/

namespace SetTheory.BusyBeaver.ZFC.RegisterPathClean

open RegisterPath

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def child (p : Program) (n : Nat) (b : Bool) : Edge :=
  if b then (p.nodes n).2 else (p.nodes n).1

/-- Follow exactly the supplied finite bits, without decoder fuel. -/
def follow (p : Program) : Edge → List Bool → Option Edge
  | e, [] => some e
  | .node n, b :: Q => follow p (child p n b) Q
  | _, _ :: _ => none

def nodeCost : Edge → Nat
  | .node _ => 1
  | _ => 0

theorem follow_append (p : Program) (e : Edge) (A B : List Bool) :
    follow p e (A ++ B) = (follow p e A).bind (fun e' => follow p e' B) := by
  induction A generalizing e with
  | nil => rfl
  | cons b A ih => cases e <;> simp [follow, ih]

theorem walk_succ (p : Program) (f n : Nat) (P : List Bool) (i : Nat) :
    walk p (f + 1) n P i =
      match child p n (bit P i) with
      | .node n' => walk p f n' P (i + 1)
      | e => some (e, i + 1) := by
  cases hb : bit P i
  · simp only [walk, child, hb, Bool.false_eq_true, if_false]
    generalize (p.nodes n).1 = e
    cases e <;> rfl
  · simp only [walk, child, hb, if_true]
    generalize (p.nodes n).2 = e
    cases e <;> rfl

theorem walk_gt (p : Program) (f n : Nat) (P : List Bool) (i : Nat)
    (e : Edge) (d : Nat) (hw : walk p f n P i = some (e, d)) :
    i < d ∧ ∀ m, e ≠ .node m := by
  induction f generalizing n i with
  | zero => simp [walk] at hw
  | succ f ih =>
    rw [walk_succ] at hw
    cases hc : child p n (bit P i) with
    | node m =>
      rw [hc] at hw
      obtain ⟨hd, he⟩ := ih m (i + 1) hw
      exact ⟨by omega, he⟩
    | inc r | decnz r | brk k | cont k | halt =>
      rw [hc] at hw
      cases hw
      exact ⟨by omega, by intro m; simp⟩

theorem bit_drop (P : List Bool) (i j : Nat) :
    bit (P.drop i) j = bit P (i + j) := by
  simp [bit, List.getElem?_drop]

/-- A successful walk follows precisely the finite bits it consumed. -/
theorem walk_follow (p : Program) (f n : Nat) (P : List Bool) (i : Nat)
    (e : Edge) (d : Nat) (hw : walk p f n P i = some (e, d)) :
    follow p (.node n) (RMEquiv.pre (P.drop i) (d - i)) = some e := by
  induction f generalizing n i with
  | zero => simp [walk] at hw
  | succ f ih =>
    have hd := (walk_gt p (f + 1) n P i e d hw).1
    rw [show d - i = (d - (i + 1)) + 1 by omega]
    simp only [RMEquiv.pre, follow, bit_drop, Nat.add_zero,
      ← List.drop_add_one_eq_tail_drop]
    rw [walk_succ] at hw
    cases hc : child p n (bit P i) with
    | node m =>
      rw [hc] at hw
      exact ih m (i + 1) hw
    | inc r | decnz r | brk k | cont k | halt =>
      rw [hc] at hw
      cases hw
      simp [RMEquiv.pre, follow]

theorem walk_follow_consume (p : Program) (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk p (p.nnodes + 1) p.root P 0 = some (e, d)) :
    follow p (.node p.root) (consume P d) = some e := by
  simpa only [RMEquiv.consume_eq, List.drop_zero, Nat.sub_zero] using
    walk_follow p (p.nnodes + 1) p.root P 0 e d hw

/-- Agreement with a followable prefix bounds every successful walk's depth.
A prefix ending at a node requires at least one further bit. -/
theorem walk_ge (p : Program) (f n : Nat) (P : List Bool) (i : Nat)
    (e : Edge) (d : Nat) (T : List Bool) (e' : Edge)
    (hw : walk p f n P i = some (e, d))
    (hf : follow p (.node n) T = some e')
    (ha : ∀ j, j < T.length → bit P (i + j) = bit T j) :
    i + T.length + nodeCost e' ≤ d := by
  induction T generalizing f n i e' with
  | nil =>
    simp only [follow, Option.some.injEq] at hf
    subst e'
    have hd := (walk_gt p f n P i e d hw).1
    simp only [List.length_nil, nodeCost]
    omega
  | cons b T ih =>
    cases f with
    | zero => simp [walk] at hw
    | succ f =>
      have hb : bit P i = b := by
        simpa only [Nat.add_zero, RMEquiv.bit_cons_zero] using ha 0 (by simp)
      rw [walk_succ, hb] at hw
      change follow p (child p n b) T = some e' at hf
      cases hc : child p n b with
      | node m =>
        rw [hc] at hw hf
        have hg := ih f m (i + 1) e' hw hf (fun j hj => by
          simpa only [RMEquiv.bit_cons_succ,
            show i + (j + 1) = i + 1 + j by omega] using ha (j + 1) (by simp; omega))
        simp only [List.length_cons]
        omega
      | inc r | decnz r | brk k | cont k | halt =>
        rw [hc] at hw hf
        cases T with
        | nil =>
          simp only [follow, Option.some.injEq] at hf
          subst e'
          cases hw
          simp [nodeCost]
        | cons _ _ => simp [follow] at hf

theorem incRev_shape (P : List Bool) :
    (∃ m, P = List.replicate m true ∧ incRev P = List.replicate m false) ∨
    (∃ m A, P = List.replicate m true ++ false :: A ∧
      incRev P = List.replicate m false ++ true :: A) := by
  induction P with
  | nil => exact Or.inl ⟨0, rfl, rfl⟩
  | cons b P ih =>
    cases b with
    | false => exact Or.inr ⟨0, P, rfl, rfl⟩
    | true =>
      rcases ih with ⟨m, hp, hi⟩ | ⟨m, A, hp, hi⟩
      · exact Or.inl ⟨m + 1, by simpa [List.replicate_succ] using congrArg (List.cons true) hp,
          by simp [incRev, hi, List.replicate_succ]⟩
      · exact Or.inr ⟨m + 1, A,
          by simpa [List.replicate_succ] using congrArg (List.cons true) hp,
          by simp [incRev, hi, List.replicate_succ]⟩

/-- Overflow keeps the original length and sets every bit to false. -/
theorem incPath_shape (P : List Bool) :
    (∃ m, P = List.replicate m true ∧ incPath P = List.replicate m false) ∨
    (∃ m A, P = A ++ false :: List.replicate m true ∧
      incPath P = A ++ true :: List.replicate m false) := by
  rcases incRev_shape P.reverse with ⟨m, hp, hi⟩ | ⟨m, A, hp, hi⟩
  · exact Or.inl ⟨m, by simpa using congrArg List.reverse hp,
      by simp [incPath, hi]⟩
  · refine Or.inr ⟨m, A.reverse, ?_, ?_⟩
    · simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
        congrArg List.reverse hp
    · simp [incPath, hi, List.reverse_append, List.reverse_cons, List.append_assoc]

theorem stripRev_suffix (b : Bool) (k : Nat) (P : List Bool) :
    ∃ A, P = A ++ stripRev b k P := by
  induction P generalizing k with
  | nil => cases k <;> exact ⟨[], rfl⟩
  | cons x P ih =>
    cases k with
    | zero => exact ⟨[], rfl⟩
    | succ k =>
      by_cases hx : x = b
      · obtain ⟨A, ha⟩ := ih k
        exact ⟨x :: A, by simpa [stripRev, hx] using congrArg (List.cons x) ha⟩
      · obtain ⟨A, ha⟩ := ih (k + 1)
        exact ⟨x :: A, by simpa [stripRev, hx] using congrArg (List.cons x) ha⟩

theorem stripPath_prefix (b : Bool) (k : Nat) (P : List Bool) :
    ∃ T, P = stripPath b k P ++ T := by
  obtain ⟨A, ha⟩ := stripRev_suffix b k P.reverse
  refine ⟨A.reverse, ?_⟩
  simpa [stripPath, List.reverse_append] using congrArg List.reverse ha

def Clean (p : Program) (P : List Bool) : Prop :=
  ∀ e d, walk p (p.nnodes + 1) p.root P 0 = some (e, d) →
    ∀ i, d ≤ i → bit P i = false

private theorem bit_overflow (P : List Bool) (i : Nat) (hi : P.length ≤ i) :
    bit P i = false := by
  simp [bit, List.getElem?_eq_none hi]

private theorem bit_false_replicate (m i : Nat) :
    bit (List.replicate m false) i = false := by
  by_cases hi : i < m <;> simp [bit, hi]

private theorem bit_append_left (A B : List Bool) (i : Nat) (hi : i < A.length) :
    bit (A ++ B) i = bit A i := by
  simp [bit, List.getElem?_append_left hi]

private theorem bit_append_right (A B : List Bool) (i : Nat) (hi : A.length ≤ i) :
    bit (A ++ B) i = bit B (i - A.length) := by
  simp [bit, List.getElem?_append_right hi]

theorem clean_prefix (p : Program) (Q : List Bool) (e : Edge) (S T : List Bool)
    (hf : follow p (.node p.root) Q = some e) (he : Q = S ++ T) : Clean p S := by
  rw [he, follow_append] at hf
  cases hs : follow p (.node p.root) S with
  | none => simp [hs] at hf
  | some eS =>
    intro e' d hw i hi
    have hg := walk_ge p (p.nnodes + 1) p.root S 0 e' d S eS hw hs
      (by intro j hj; simp)
    exact bit_overflow S i (by omega)

theorem clean_inc (p : Program) (Q : List Bool) (e : Edge) (S T : List Bool)
    (hf : follow p (.node p.root) Q = some e) (he : Q = S ++ T) :
    Clean p (incPath S) := by
  rcases incPath_shape S with ⟨m, _, hi⟩ | ⟨m, A, hs, hi⟩
  · rw [hi]
    exact fun _ _ _ i _ => bit_false_replicate m i
  · have hf' : follow p (.node p.root)
        (A ++ (false :: List.replicate m true ++ T)) = some e := by
      simpa only [he, hs, List.append_assoc] using hf
    rw [follow_append] at hf'
    cases hA : follow p (.node p.root) A with
    | none => simp [hA] at hf'
    | some eA =>
      rw [hA] at hf'
      cases eA with
      | node n =>
        rw [hi]
        intro e' d hw i hd
        have hg := walk_ge p (p.nnodes + 1) p.root
          (A ++ true :: List.replicate m false) 0 e' d A (.node n) hw hA
          (fun j hj => by
            simpa only [Nat.zero_add] using bit_append_left A _ j hj)
        simp only [Nat.zero_add, nodeCost] at hg
        rw [bit_append_right A _ i (by omega)]
        cases hk : i - A.length with
        | zero => omega
        | succ j =>
          simp only [RMEquiv.bit_cons_succ]
          exact bit_false_replicate m j
      | inc _ | decnz _ | brk _ | cont _ | halt => simp [Option.bind, follow] at hf'

theorem execute_clean (p : Program) (e : Edge) (Q : List Bool) (R : Registers)
    (c' : Configuration) (hf : follow p (.node p.root) Q = some e)
    (hs : execute e Q R = some c') : Clean p c'.path := by
  cases e with
  | node _ | halt => simp [execute] at hs
  | inc r =>
    simp only [execute, Option.some.injEq] at hs
    subst c'
    exact clean_inc p Q (.inc r) Q [] hf (by simp)
  | decnz r =>
    cases hv : R r with
    | zero =>
      simp only [execute, hv, Option.some.injEq] at hs
      subst c'
      obtain ⟨T, ht⟩ := stripPath_prefix false 1 Q
      exact clean_inc p Q (.decnz r) _ T hf ht
    | succ v =>
      simp only [execute, hv, Option.some.injEq] at hs
      subst c'
      exact clean_inc p Q (.decnz r) Q [] hf (by simp)
  | brk k =>
    simp only [execute, Option.some.injEq] at hs
    subst c'
    obtain ⟨T, ht⟩ := stripPath_prefix false k Q
    exact clean_inc p Q (.brk k) _ T hf ht
  | cont k =>
    simp only [execute, Option.some.injEq] at hs
    subst c'
    obtain ⟨T, ht⟩ := stripPath_prefix true k Q
    exact clean_prefix p Q (.cont k) _ T hf ht

/-- Successful execution removes stray bits even if its input was not clean. -/
theorem step_clean (p : Program) (c c' : Configuration)
    (hs : step p c = some c') : Clean p c'.path := by
  rcases hw : walk p (p.nnodes + 1) p.root c.path 0 with _ | ⟨e, d⟩
  · simp [step, hw] at hs
  · exact execute_clean p e (consume c.path d) c.registers c' (walk_follow_consume p c.path e d hw)
      (by simpa only [step, hw] using hs)

theorem run_reach (p : Program) (N : Nat) (c c' : Configuration)
    (hr : run p N c = some c') : c' = c ∨ ∃ c0, step p c0 = some c' := by
  induction N generalizing c with
  | zero =>
    simp only [run, Option.some.injEq] at hr
    exact Or.inl hr.symm
  | succ N ih =>
    cases hs : step p c with
    | none => simp [run, hs] at hr
    | some c1 =>
      rcases ih c1 (by simpa only [run, hs] using hr) with he | he
      · exact Or.inr ⟨c, by simpa only [he] using hs⟩
      · exact Or.inr he

theorem clean_nil (p : Program) : Clean p [] := fun _ _ _ _ _ => rfl

theorem run_clean (p : Program) (N : Nat) (c c' : Configuration)
    (hc : Clean p c.path) (hr : run p N c = some c') : Clean p c'.path := by
  rcases run_reach p N c c' hr with he | ⟨c0, hs⟩
  · simpa only [he] using hc
  · exact step_clean p c0 c' hs

/-- No initial register values or program-well-formedness premises occur. -/
theorem no_stray_bits (p : Program) (R0 : Registers) (N : Nat)
    (c : Configuration) (e : Edge) (d : Nat)
    (hr : run p N ⟨[], R0⟩ = some c)
    (hw : walk p (p.nnodes + 1) p.root c.path 0 = some (e, d)) :
    ∀ i, d ≤ i → bit c.path i = false :=
  run_clean p N ⟨[], R0⟩ c (clean_nil p) hr e d hw

/-- The represented suffix after the next leaf depth consists only of zeros. -/
theorem no_stray (p : Program) (R0 : Registers) (N : Nat)
    (c : Configuration) (e : Edge) (d : Nat)
    (hr : run p N ⟨[], R0⟩ = some c)
    (hw : walk p (p.nnodes + 1) p.root c.path 0 = some (e, d)) :
    ∀ b ∈ c.path.drop d, b = false := by
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  have hv : bit (c.path.drop d) i = b := by simp [bit, hi]
  exact hv.symm.trans ((bit_drop c.path d i).trans
    (no_stray_bits p R0 N c e d hr hw (d + i) (by omega)))

/-- Consuming a path always produces exactly the decoder's depth, including
zero extension when that depth exceeds the stored path length. -/
theorem consume_length (P : List Bool) (d : Nat) : (consume P d).length = d := by
  simp only [consume, List.length_take, List.length_append, List.length_replicate]
  exact Nat.min_eq_left (by omega)

/-- The complete physical PC/gap region can be rebased at its consumed
prefix. The depth may exceed the stored path length; only the total budget
must suffice. No tape cell is discarded. -/
theorem gap_consume (P : List Bool) (gap d : Nat)
    (hb : d ≤ P.length + gap) (hz : ∀ b ∈ P.drop d, b = false) :
    P ++ List.replicate gap false =
      consume P d ++ List.replicate (P.length + gap - d) false := by
  by_cases hd : d ≤ P.length
  · have hc : consume P d = P.take d :=
      List.take_append_of_le_length hd
    have ht : P.drop d = List.replicate (P.length - d) false :=
      List.eq_replicate_iff.mpr ⟨List.length_drop, hz⟩
    calc
      P ++ List.replicate gap false =
          (P.take d ++ P.drop d) ++ List.replicate gap false := by
        rw [List.take_append_drop]
      _ = P.take d ++ List.replicate ((P.length - d) + gap) false := by
        rw [ht, List.append_assoc, List.replicate_append_replicate]
      _ = consume P d ++ List.replicate (P.length + gap - d) false := by
        rw [hc]
        congr 2
        omega
  · have hpd : P.length ≤ d := by omega
    have hc : consume P d = P ++ List.replicate (d - P.length) false := by
      simp only [consume, List.take_append, List.take_of_length_le hpd,
        List.take_replicate, Nat.min_eq_left (Nat.sub_le d P.length)]
    rw [hc, List.append_assoc, List.replicate_append_replicate]
    congr 2
    omega

theorem reachable_gap_consume (p : Program) (R0 : Registers) (N : Nat)
    (c : Configuration) (e : Edge) (d gap : Nat)
    (hr : run p N ⟨[], R0⟩ = some c)
    (hw : walk p (p.nnodes + 1) p.root c.path 0 = some (e, d))
    (hb : d ≤ c.path.length + gap) :
    c.path ++ List.replicate gap false =
      consume c.path d ++ List.replicate (c.path.length + gap - d) false :=
  gap_consume c.path gap d hb (no_stray p R0 N c e d hr hw)

end SetTheory.BusyBeaver.ZFC.RegisterPathClean
