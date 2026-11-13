module
public import M6.Source.Enumeration
@[expose] public section
namespace M6.Source.CommandAtomEncoding
open Cantor Enumeration

/-- Standalone command atom uses the exact source command-field code at tail0.
The surrounding List Nat is not itself a source residual code or HFS vector. -/
def atom (c : Command) : Nat := encodeCommand c 0

def splice (a tail : Nat) : Nat :=
  let p:=decode a
  match p.1 with
  | 0 => pair 0 tail
  | 1 => pair 1 (pair (decode p.2).1 tail)
  | c+2 => let q:=decode p.2; pair (c+2) (pair q.1 (pair (decode q.2).1 tail))

theorem parse_atom (c : Command) : (parse (atom c)).command=c := by
  simp only [atom,parse_encode]
theorem atom_injective : Function.Injective atom := by
  intro a b h
  have hh:=congrArg (fun n => (parse n).command) h
  simpa only [parse_atom] using hh

theorem splice_atom (c : Command) (tail : Nat) : splice (atom c) tail=encodeCommand c tail := by
  cases c <;> simp [splice,atom,encodeCommand,decode_pair]

def atoms (cs : List Command) : List Nat := cs.map atom

def encodeAtoms : List Nat → Nat
  | [] => 0
  | a::as => splice a (encodeAtoms as)+1

theorem encodeAtoms_atoms (cs : List Command) : encodeAtoms (atoms cs)=encodeWord cs 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [atoms,List.map_cons,encodeAtoms,splice_atom,encodeWord] at *; rw [ih]

theorem candidate_atoms (c : Command) (cs : List Command) :
    word (encodeAtoms (atoms (c::cs))-1)=c::cs := by
  rw [encodeAtoms_atoms,word_candidate]
  simp [residual]

#print axioms splice_atom
#print axioms encodeAtoms_atoms
#print axioms candidate_atoms
end M6.Source.CommandAtomEncoding

