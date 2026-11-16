module
public import M6.Source.Cantor
@[expose] public section

/-! Pure command-field enumeration, with the same fresh/positive-pointer
convention proved by Fetch. AX/MP execution and global credit are separate. -/
namespace M6.Source.Enumeration
open Cantor

theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [triangle]; omega

theorem pair_bounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b := by
  have h := triangle_ge (a+b)
  simp only [pair]
  omega

theorem decode_bounds (n : Nat) : (decode n).1 ≤ n ∧ (decode n).2 ≤ n := by
  have h := pair_bounds (decode n).1 (decode n).2
  rw [pair_decode] at h
  exact h

inductive Command where
  | shift
  | mp (offset : Nat)
  | ax (selector x y : Nat)
  deriving DecidableEq, Repr

structure Parsed where
  command : Command
  next : Nat
  deriving DecidableEq, Repr

def parse (n : Nat) : Parsed :=
  let p := decode n
  match p.1 with
  | 0 => ⟨.shift,p.2⟩
  | 1 => let q := decode p.2; ⟨.mp q.1,q.2⟩
  | c+2 => let q := decode p.2; let r := decode q.2; ⟨.ax c r.1 q.1,r.2⟩

theorem parse_next_le (n : Nat) : (parse n).next ≤ n := by
  have h1 := (decode_bounds n).2
  have h2 := (decode_bounds (decode n).2).2
  have h3 := (decode_bounds (decode (decode n).2).2).2
  simp only [parse]
  split <;> simp_all <;> omega

def residual : Nat → List Command
  | 0 => []
  | n+1 => (parse n).command :: residual (parse n).next
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (parse_next_le n)

def word (n : Nat) : List Command := (parse n).command :: residual (parse n).next

theorem residual_succ (n : Nat) : residual (n+1) = word n := by rw [residual]; rfl

theorem residual_length_le (n : Nat) : (residual n).length ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [residual]
    | succ n =>
      have h := ih (parse n).next (Nat.lt_succ_of_le (parse_next_le n))
      rw [residual]
      simp only [List.length_cons]
      have := parse_next_le n
      omega

def encodeCommand : Command → Nat → Nat
  | .shift,t => pair 0 t
  | .mp x,t => pair 1 (pair x t)
  | .ax c x y,t => pair (c+2) (pair y (pair x t))

theorem parse_encode (c : Command) (tail : Nat) : parse (encodeCommand c tail) = ⟨c,tail⟩ := by
  cases c <;> simp [encodeCommand,parse,decode_pair]

def encodeWord : List Command → Nat → Nat
  | [],tail => tail
  | c::cs,tail => encodeCommand c (encodeWord cs tail) + 1

/-- Every finite command word is an exact prefix of a positive residual code.
The arbitrary terminal pointer remains explicit, not silently discarded. -/
theorem residual_encodeWord (cs : List Command) (tail : Nat) :
    residual (encodeWord cs tail) = cs ++ residual tail := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [encodeWord,residual,parse_encode]
    simp only [ih,List.cons_append]

theorem encodeWord_positive (cs : List Command) (tail : Nat) (ht : 0 < tail) :
    0 < encodeWord cs tail := by
  cases cs with
  | nil => exact ht
  | cons c cs => simp only [encodeWord]; omega

/-- Fresh candidate encoding differs by exactly one from positive residual
encoding. This is the concrete candidate used by a finite refutation compiler. -/
theorem word_candidate (c : Command) (cs : List Command) (tail : Nat) :
    word (encodeWord (c::cs) tail - 1) = (c::cs) ++ residual tail := by
  simp only [encodeWord,Nat.add_sub_cancel,word,parse_encode,residual_encodeWord,List.cons_append]

def commandWeight : Command → Int
  | .shift => -1
  | .mp _ => 0
  | .ax _ _ _ => 10

def weight : List Command → Int
  | [] => 0
  | c::cs => commandWeight c + weight cs

theorem weight_lower (cs : List Command) : -(cs.length : Int) ≤ weight cs := by
  induction cs with
  | nil => simp [weight]
  | cons c cs ih =>
    cases c <;> simp only [weight,commandWeight,List.length_cons,Int.natCast_add,Int.natCast_one] <;> omega

theorem residual_weight_lower (n : Nat) : -(n : Int) ≤ weight (residual n) := by
  have h1 := weight_lower (residual n)
  have h2 := residual_length_le n
  omega

#print axioms word_candidate
#print axioms residual_weight_lower
#print axioms residual_length_le
#print axioms residual_encodeWord
end M6.Source.Enumeration

