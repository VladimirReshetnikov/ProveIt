import Lean

/-!
Production-shaped decoder fusion test.

The Tree, quote, depth, decode, and decode_sound proof are transplanted from
the pinned production source/proposed patch. Mathlib's Nat.pair and Nat.unpair
are replaced by explicit operations K.pair and K.unpair. The sole pairing law
used by the production forward proof is an explicit parameter of PairOps.
This tests the actual arithmetic offsets and Option proof branches, while
remaining independent of the unavailable Mathlib build products.
-/

namespace ExactDecoderFusion

structure PairOps where
  pair : Nat → Nat → Nat
  unpair : Nat → Nat × Nat
  pair_unpair : ∀ n, pair (unpair n).1 (unpair n).2 = n

inductive Tree where
  | atom (n : Nat)
  | fork (left right : Tree)
  deriving DecidableEq, Repr

namespace Tree

def quote (K : PairOps) : Tree → Nat
  | atom n => K.pair 0 n+1
  | fork a b => K.pair (quote K a+1) (quote K b)+1

def depth : Tree → Nat
  | atom _ => 1
  | fork a b => max a.depth b.depth+1

def decode (K : PairOps) : Nat → Nat → Option Tree
  | 0, _ => none
  | _+1, 0 => none
  | fuel+1, code+1 =>
    let p := K.unpair code
    match p.1 with
    | 0 => some (atom p.2)
    | left+1 => do
      let a ← decode K fuel left
      let b ← decode K fuel p.2
      pure (fork a b)

theorem decode_sound (K : PairOps) {fuel code : Nat} {t : Tree}
    (h : decode K fuel code=some t) : t.quote K=code ∧ t.depth≤fuel := by
  induction fuel generalizing code t with
  | zero => simp [decode] at h
  | succ fuel ih =>
    cases code with
    | zero => simp [decode] at h
    | succ code =>
      have hp := K.pair_unpair code
      simp only [decode] at h
      cases he : (K.unpair code).1 with
      | zero =>
        simp only [he] at h hp
        cases h
        exact ⟨by simp only [quote,hp],by simp [depth]⟩
      | succ left =>
        simp only [he] at h hp
        cases ha : decode K fuel left with
        | none => simp [ha] at h
        | some a =>
          cases hb : decode K fuel (K.unpair code).2 with
          | none => simp [ha,hb] at h
          | some b =>
            simp only [ha,hb,Option.pure_def] at h
            cases h
            obtain ⟨hqa,hda⟩ := ih ha
            obtain ⟨hqb,hdb⟩ := ih hb
            constructor
            · simp only [quote,hqa,hqb,hp]
            · simp only [depth]; omega

theorem decoded_depth_le (K : PairOps) {fuel code : Nat} {t : Tree}
    (h : decode K fuel code=some t) : t.depth≤fuel := (decode_sound K h).2

theorem quote_of_decode (K : PairOps) {fuel code : Nat} {t : Tree}
    (h : decode K fuel code=some t) : t.quote K=code := (decode_sound K h).1

#print axioms decode_sound
#print axioms decoded_depth_le
#print axioms quote_of_decode

end Tree
end ExactDecoderFusion
