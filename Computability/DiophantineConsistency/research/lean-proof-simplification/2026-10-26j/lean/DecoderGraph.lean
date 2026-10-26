import Lean

/-!
A core-only prototype of fused decoder correctness.

This file is not a compiled replacement for ProveIt's AnnotatedProofCode.
It proves the generic binary-decoder result from explicit one-step coding
laws, with no Mathlib dependency and no claim about the production imports.
-/

namespace DecoderGraph

inductive Tree where
  | atom : Nat → Tree
  | fork : Tree → Tree → Tree
  deriving DecidableEq, Repr

def Tree.depth : Tree → Nat
  | .atom _ => 1
  | .fork a b => max a.depth b.depth + 1

inductive View (Code : Type) where
  | atom : Nat → View Code
  | fork : Code → Code → View Code

structure Coding (Code : Type) where
  atom : Nat → Code
  fork : Code → Code → Code
  inspect : Code → Option (View Code)
  inspect_atom : ∀ n, inspect (atom n) = some (.atom n)
  inspect_fork : ∀ a b, inspect (fork a b) = some (.fork a b)
  atom_sound : ∀ c n, inspect c = some (.atom n) → atom n = c
  fork_sound : ∀ c a b, inspect c = some (.fork a b) → fork a b = c

def quote (K : Coding Code) : Tree → Code
  | .atom n => K.atom n
  | .fork a b => K.fork (quote K a) (quote K b)

def decode (K : Coding Code) : Nat → Code → Option Tree
  | 0, _ => none
  | fuel + 1, c =>
    match K.inspect c with
    | none => none
    | some (.atom n) => some (.atom n)
    | some (.fork a b) => do
      let ta ← decode K fuel a
      let tb ← decode K fuel b
      pure (.fork ta tb)

theorem decode_quote (K : Coding Code) (t : Tree) (fuel : Nat)
    (h : t.depth ≤ fuel) : decode K fuel (quote K t) = some t := by
  induction t generalizing fuel with
  | atom n =>
    cases fuel with
    | zero => simp [Tree.depth] at h
    | succ fuel => simp [decode, quote, K.inspect_atom]
  | fork a b ha hb =>
    cases fuel with
    | zero => simp [Tree.depth] at h
    | succ fuel =>
      have hfa : a.depth ≤ fuel := by simp only [Tree.depth] at h; omega
      have hfb : b.depth ≤ fuel := by simp only [Tree.depth] at h; omega
      simp [decode, quote, K.inspect_fork, ha fuel hfa, hb fuel hfb]

/-- One induction supplies both facts that the production source currently
proves through two identical parser case trees. -/
theorem decode_sound (K : Coding Code) {fuel : Nat} {c : Code} {t : Tree}
    (h : decode K fuel c = some t) : quote K t = c ∧ t.depth ≤ fuel := by
  induction fuel generalizing c t with
  | zero => simp [decode] at h
  | succ fuel ih =>
    cases hv : K.inspect c with
    | none => simp [decode, hv] at h
    | some v =>
      cases v with
      | atom n =>
        simp only [decode, hv, Option.some.injEq] at h
        subst t
        exact ⟨K.atom_sound c n hv, by simp [Tree.depth]⟩
      | fork a b =>
        cases ha : decode K fuel a with
        | none => simp [decode, hv, ha] at h
        | some ta =>
          cases hb : decode K fuel b with
          | none => simp [decode, hv, ha, hb] at h
          | some tb =>
            simp only [decode, hv, ha, hb] at h
            have ht : Tree.fork ta tb = t := Option.some.inj h
            subst t
            obtain ⟨hqa, hda⟩ := ih ha
            obtain ⟨hqb, hdb⟩ := ih hb
            constructor
            · simpa only [quote, hqa, hqb] using K.fork_sound c a b hv
            · simp only [Tree.depth]
              omega

theorem decode_eq_some_iff (K : Coding Code) (fuel : Nat) (c : Code) (t : Tree) :
    decode K fuel c = some t ↔ quote K t = c ∧ t.depth ≤ fuel := by
  constructor
  · exact decode_sound K
  · rintro ⟨hq, hd⟩
    rw [← hq]
    exact decode_quote K t fuel hd

theorem decoded_depth_le (K : Coding Code) {fuel : Nat} {c : Code} {t : Tree}
    (h : decode K fuel c = some t) : t.depth ≤ fuel :=
  (decode_sound K h).2

theorem quote_of_decode (K : Coding Code) {fuel : Nat} {c : Code} {t : Tree}
    (h : decode K fuel c = some t) : quote K t = c :=
  (decode_sound K h).1

#print axioms decode_sound
#print axioms decode_eq_some_iff

end DecoderGraph
