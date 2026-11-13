module
public import M6.Source.PathTrie
@[expose] public section
namespace M6.Legacy213.FastResolve
open M6.Source M6.Source.PathTrie

def afterTree (t : Tree) (p : Path) : Option (Option Nat) :=
  match successor p with
  | none => some none
  | some q => some <$> lookup t q

def resolveTree (t : Tree) (s : Site) : Option Instruction :=
  match s.op with
  | .inc r => do
      let n ← afterTree t s.path
      return .inc r n
  | .dec r => do
      let p ← cut s.path false 1
      let z ← afterTree t p
      let n ← afterTree t s.path
      return .dec r z n
  | .breakTo k => do
      let p ← cut s.path false k
      let n ← afterTree t p
      return .jump n
  | .continueTo k => do
      let p ← cut s.path true k
      let target ← lookup t p
      return .jump (some target)
  | .halt => some .halt

theorem afterTree_eq (t : Tree) (sites : Array Site) (ht : flatten t = sites.toList) (p : Path) :
    afterTree t p = after sites p := by
  simp only [afterTree, after, lookup_eq, ht, locate]
  rfl

theorem resolveTree_eq (t : Tree) (sites : Array Site) (ht : flatten t = sites.toList) (s : Site) :
    resolveTree t s = resolve sites s := by
  cases h : s.op <;> simp only [resolveTree, resolve, h, afterTree_eq t sites ht, lookup_eq, ht, locate]
end M6.Legacy213.FastResolve
