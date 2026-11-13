import DiophantineConsistency.Sign14PrefixParser

/-! SOURCE-ONLY: compositional symbolic prefix-code reflection. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14PrefixReflection
open Sign14Prefix

inductive Code where
  | var (i : Fin 15)
  | port (i : Fin 4)
  | one | two | three | four
  | add (a b : Code) | sub (a b : Code) | mul (a b : Code)
  deriving DecidableEq, Repr

def varChar (i : Fin 15) : Char := Char.ofNat (97 + i.val)
def portChar (i : Fin 4) : Char :=
  match i.val with | 0 => 'B' | 1 => 'K' | 2 => 'C' | _ => 'F'

def encode : Code → List Char
  | .var i => [varChar i]
  | .port i => [portChar i]
  | .one => ['1'] | .two => ['2'] | .three => ['3'] | .four => ['4']
  | .add a b => '+' :: (encode a ++ encode b)
  | .sub a b => '-' :: (encode a ++ encode b)
  | .mul a b => '*' :: (encode a ++ encode b)

def interpret (p : Fin 4 → ℤ) : Code → Expr (Fin 15)
  | .var i => Expr.var i
  | .port i => Expr.constant (p i)
  | .one => Expr.constant 1 | .two => Expr.constant 2
  | .three => Expr.constant 3 | .four => Expr.constant 4
  | .add a b => Expr.add (interpret p a) (interpret p b)
  | .sub a b => Expr.sub (interpret p a) (interpret p b)
  | .mul a b => Expr.mul (interpret p a) (interpret p b)

def depth : Code → ℕ
  | .var _ | .port _ | .one | .two | .three | .four => 1
  | .add a b | .sub a b | .mul a b => 1 + max (depth a) (depth b)

/-- Decoding a canonical code followed by an arbitrary suffix recovers its
interpretation and leaves that suffix unchanged. -/
theorem decode_encode (p : Fin 4 → ℤ) (e : Code) :
    ∀ n : ℕ, depth e ≤ n → ∀ tail,
      decode p n (encode e ++ tail) = some (interpret p e, tail) := by
  induction e with
  | var i =>
      intro n hn tail
      cases n with
      | zero => simp [depth] at hn
      | succ n => fin_cases i <;> rfl
  | port i =>
      intro n hn tail
      cases n with
      | zero => simp [depth] at hn
      | succ n => fin_cases i <;> rfl
  | one | two | three | four =>
      intro n hn tail
      cases n with
      | zero => simp [depth] at hn
      | succ n => rfl
  | add a b ha hb =>
      intro n hn tail
      cases n with
      | zero => simp [depth] at hn
      | succ n =>
          have hA : depth a ≤ n := by simp [depth] at hn; omega
          have hB : depth b ≤ n := by simp [depth] at hn; omega
          simp only [encode, List.cons_append, List.append_assoc, decode]
          rw [ha n hA, hb n hB]
          rfl
  | sub a b ha hb =>
      intro n hn tail
      cases n with
      | zero => simp [depth] at hn
      | succ n =>
          have hA : depth a ≤ n := by simp [depth] at hn; omega
          have hB : depth b ≤ n := by simp [depth] at hn; omega
          simp only [encode, List.cons_append, List.append_assoc, decode]
          rw [ha n hA, hb n hB]
          rfl
  | mul a b ha hb =>
      intro n hn tail
      cases n with
      | zero => simp [depth] at hn
      | succ n =>
          have hA : depth a ≤ n := by simp [depth] at hn; omega
          have hB : depth b ≤ n := by simp [depth] at hn; omega
          simp only [encode, List.cons_append, List.append_assoc, decode]
          rw [ha n hA, hb n hB]
          rfl
end DiophantineConsistency.Sign14PrefixReflection
#print axioms DiophantineConsistency.Sign14PrefixReflection.decode_encode
