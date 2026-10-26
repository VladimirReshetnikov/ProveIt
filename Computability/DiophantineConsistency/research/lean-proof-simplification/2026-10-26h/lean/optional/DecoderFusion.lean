import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

namespace ProofSimplification.Decoder

inductive Tree where
  | atom (n : Nat)
  | fork (left right : Tree)
  deriving DecidableEq, Repr

namespace Tree

def quote : Tree → Nat
  | atom n => Nat.pair 0 n+1
  | fork a b => Nat.pair (quote a+1) (quote b)+1

def depth : Tree → Nat
  | atom _ => 1
  | fork a b => max a.depth b.depth+1

/-- Fuel zero and code zero are rejected. Every recursive code is smaller. -/
def decode : Nat → Nat → Option Tree
  | 0, _ => none
  | _+1, 0 => none
  | fuel+1, code+1 =>
    let p := Nat.unpair code
    match p.1 with
    | 0 => some (atom p.2)
    | left+1 => do
      let a ← decode fuel left
      let b ← decode fuel p.2
      pure (fork a b)

theorem depth_le_quote (t : Tree) : t.depth≤t.quote := by
  induction t with
  | atom n => simp only [depth,quote]; omega
  | fork a b ha hb =>
    have hl := Nat.left_le_pair (a.quote+1) b.quote
    have hr := Nat.right_le_pair (a.quote+1) b.quote
    simp only [depth,quote]
    omega

theorem decode_quote (t : Tree) (fuel : Nat) (hf : t.depth≤fuel) :
    decode fuel t.quote=some t := by
  induction t generalizing fuel with
  | atom n =>
    cases fuel with
    | zero => simp [depth] at hf
    | succ fuel => simp [quote,decode]
  | fork a b ha hb =>
    cases fuel with
    | zero => simp [depth] at hf
    | succ fuel =>
      have hfa : a.depth≤fuel := by simp only [depth] at hf; omega
      have hfb : b.depth≤fuel := by simp only [depth] at hf; omega
      simp [quote,decode,ha fuel hfa,hb fuel hfb]

/-- A fixed, total parser; the input itself supplies a sufficient fuel bound. -/
def parse (code : Nat) : Option Tree := decode code code

@[simp] theorem parse_quote (t : Tree) : parse t.quote=some t :=
  decode_quote t t.quote (depth_le_quote t)

/-- A single decoder induction establishes both canonicality and the fuel bound. -/
theorem decode_sound {fuel code : Nat} {t : Tree} (h : decode fuel code=some t) :
    t.quote=code ∧ t.depth≤fuel := by
  induction fuel generalizing code t with
  | zero => simp [decode] at h
  | succ fuel ih =>
    cases code with
    | zero => simp [decode] at h
    | succ code =>
      have hp := Nat.pair_unpair code
      simp only [decode] at h
      cases he : (Nat.unpair code).1 with
      | zero =>
        simp only [he] at h hp
        cases h
        exact ⟨by simp only [quote,hp], by simp [depth]⟩
      | succ left =>
        simp only [he] at h hp
        cases ha : decode fuel left with
        | none => simp [ha] at h
        | some a =>
          cases hb : decode fuel (Nat.unpair code).2 with
          | none => simp [ha,hb] at h
          | some b =>
            simp only [ha,hb,Option.pure_def] at h
            cases h
            have h1 := ih ha
            have h2 := ih hb
            exact ⟨by simp only [quote,h1.1,h2.1,hp], by simp only [depth]; omega⟩

theorem decoded_depth_le {fuel code : Nat} {t : Tree} (h : decode fuel code=some t) :
    t.depth≤fuel := (decode_sound h).2

theorem quote_of_decode {fuel code : Nat} {t : Tree} (h : decode fuel code=some t) :
    t.quote=code := (decode_sound h).1

theorem quote_injective : Function.Injective quote := by
  intro a b h
  have hh := congrArg parse h
  simpa only [parse_quote,Option.some.injEq] using hh

theorem decode_quote_iff (t u : Tree) (fuel : Nat) :
    decode fuel t.quote=some u ↔ u=t ∧ t.depth≤fuel := by
  constructor
  · intro h
    have hu : u=t := quote_injective (quote_of_decode h)
    exact ⟨hu,hu ▸ decoded_depth_le h⟩
  · rintro ⟨hu,hf⟩
    rw [hu]
    exact decode_quote t fuel hf

theorem decode_quote_none_of_lt (t : Tree) (fuel : Nat) (h : fuel<t.depth) :
    decode fuel t.quote=none := by
  cases hh : decode fuel t.quote with
  | none => rfl
  | some u =>
    have hf := (decode_quote_iff t u fuel).mp hh
    omega


#print axioms decode_sound
#print axioms decoded_depth_le
#print axioms quote_of_decode
end Tree
end ProofSimplification.Decoder

