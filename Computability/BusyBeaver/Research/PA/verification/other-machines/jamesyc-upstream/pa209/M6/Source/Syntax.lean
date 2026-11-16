module
public import Std

/-! Literal source syntax and the prefix-path control convention. Register order
is N,T,W,A,D,H,X,Y,L. A missing destination is normal source-root exit, which is
kept distinct from the explicit halt instruction. -/
@[expose] public section

namespace M6.Source

abbrev Path := List Bool

inductive Op where
  | inc (register : Fin 9)
  | dec (register : Fin 9)
  | breakTo (depth : Nat)
  | continueTo (depth : Nat)
  | halt
  deriving DecidableEq, Repr

structure Site where
  path : Path
  op : Op
  deriving DecidableEq, Repr

inductive Instruction where
  | inc (register : Fin 9) (next : Option Nat)
  | dec (register : Fin 9) (zero positive : Option Nat)
  | jump (next : Option Nat)
  | halt
  deriving DecidableEq, Repr

/-- Binary successor, acting first on the least significant (reversed) bit. -/
def incrementRev : Path → Option Path
  | [] => none
  | false :: xs => some (true :: xs)
  | true :: xs => (false :: ·) <$> incrementRev xs

def successor (p : Path) : Option Path := List.reverse <$> incrementRev p.reverse

/-- Remove the suffix through the `depth`-th selected bit counted from the end.
Failure remains explicit instead of manufacturing a target for malformed input. -/
def cutRev (bit : Bool) : Nat → Path → Option Path
  | 0, xs => some xs
  | _ + 1, [] => none
  | k + 1, b :: xs =>
      if b = bit then cutRev bit k xs else cutRev bit (k + 1) xs

def cut (p : Path) (bit : Bool) (depth : Nat) : Option Path :=
  List.reverse <$> cutRev bit depth p.reverse

/-- Leftmost leaf below a prefix, also accepting zero extension of a leaf.
The site list is in left-to-right leaf order. -/
def findSite (p : Path) : List Site → Option Nat
  | [] => none
  | s :: rest =>
      if p.isPrefixOf s.path ||
          (s.path.isPrefixOf p && (p.drop s.path.length).all (· == false)) then some 0
      else Nat.succ <$> findSite p rest

def locate (sites : Array Site) (p : Path) : Option Nat :=
  findSite p sites.toList

/-- Outer `none` is malformed/unresolved input; inner `none` is genuine root exit. -/
def after (sites : Array Site) (p : Path) : Option (Option Nat) :=
  match successor p with
  | none => some none
  | some q => some <$> locate sites q

def resolve (sites : Array Site) (s : Site) : Option Instruction :=
  match s.op with
  | .inc r => do
      let n ← after sites s.path
      return .inc r n
  | .dec r => do
      let p ← cut s.path false 1
      let z ← after sites p
      let n ← after sites s.path
      return .dec r z n
  | .breakTo k => do
      let p ← cut s.path false k
      let n ← after sites p
      return .jump n
  | .continueTo k => do
      let p ← cut s.path true k
      let target ← locate sites p
      return .jump (some target)
  | .halt => some .halt

def resolveAt (sites : Array Site) (i : Nat) : Option Instruction :=
  sites[i]? >>= resolve sites

end M6.Source

