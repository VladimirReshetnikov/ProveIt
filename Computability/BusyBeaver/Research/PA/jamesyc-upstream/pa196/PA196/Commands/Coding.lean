module
public import PA196.Commands.Store
@[expose] public section

namespace PA196.Commands
open M6.Source.Cantor

/-- Source command atoms: AX reads its `y` field before its `x` field. -/
def atom : Command → Nat
  | .shift => 0
  | .mp x => pair 1 (pair x 0)
  | .ax c x y => pair (c + 2) (pair y (pair x 0))

def atoms (xs : List Command) : List Nat := xs.map atom

def decodeAtom (n : Nat) : Command :=
  let p := decode n
  if p.1 = 0 then .shift
  else if p.1 = 1 then .mp (decode p.2).1
  else .ax (p.1 - 2) (decode (decode p.2).2).1 (decode p.2).1

theorem decode_atom (c : Command) : decodeAtom (atom c) = c := by
  cases c with
  | shift => rfl
  | mp x => simp [decodeAtom, atom, decode_pair]
  | ax c x y => simp [decodeAtom, atom, decode_pair]

theorem atom_injective {a b : Command} (h : atom a = atom b) : a = b := by
  have h' := congrArg decodeAtom h
  simpa only [decode_atom] using h'

#print axioms decode_atom
end PA196.Commands
