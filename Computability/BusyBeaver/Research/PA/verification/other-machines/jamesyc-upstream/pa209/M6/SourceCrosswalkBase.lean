module
public import M6.CheckCoverage
public import M6.OriginalProgram
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.SourceCrosswalk
open M6.Source M6.Source.PathTrie

def originalSites : Array Site := (flatten OriginalProgram.trie).toArray
def originalCodeAt (i : Nat) : Option Instruction :=
  (nthSite OriginalProgram.trie i).bind (FastResolve.resolveTree OriginalProgram.trie)

/-- New order F,G,A,B,C,D,E,return mapped to old order A,B,C,D,E,F,G.
    The inserted return and first F instruction both map to old F entry3922. -/
def collapse (i : Nat) : Nat :=
  if i = 3947 then 3922 else if i < 25 then i+3922 else i-25

/-- Make the primitive scheduler's normal-root restart explicit. -/
def normalize : Instruction → Instruction
  | .inc r n => .inc r (some (n.getD 0))
  | .dec r z p => .dec r (some (z.getD 0)) (some (p.getD 0))
  | .jump n => .jump (some (n.getD 0))
  | .halt => .halt

def collapseInstruction : Instruction → Instruction
  | .inc r n => .inc r (some (collapse (n.getD 0)))
  | .dec r z p => .dec r (some (collapse (z.getD 0))) (some (collapse (p.getD 0)))
  | .jump n => .jump (some (collapse (n.getD 0)))
  | .halt => .halt

def codeCheck (i : Nat) : Bool := decide
  ((CheckCoverage.codeAt i).map collapseInstruction =
    (originalCodeAt (collapse i)).map normalize)
def blockCheck (base count : Nat) : Bool :=
  (List.range count).all (fun j => codeCheck (base+j))

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base+count) :
    (CheckCoverage.codeAt i).map collapseInstruction =
      (originalCodeAt (collapse i)).map normalize := by
  have hh := List.all_eq_true.mp h (i-base) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le lo] at hh
  exact of_decide_eq_true hh

theorem inserted_return : CheckCoverage.codeAt 3947 = some (.jump (some 0)) := by decide +kernel

theorem collapse_bound (i : Nat) (hi : i < 3948) : collapse i < 3947 := by
  unfold collapse
  split
  · omega
  · split <;> omega

theorem original_resolve (i : Nat) : resolveAt originalSites i = originalCodeAt i := by
  have hf : FastResolve.resolveTree OriginalProgram.trie = resolve originalSites :=
    funext (FastResolve.resolveTree_eq _ _ (by simp [originalSites]))
  unfold originalCodeAt
  rw [hf,nthSite_eq]
  simp only [resolveAt,originalSites,List.getElem?_toArray]
  rfl

#print axioms inserted_return
end M6.SourceCrosswalk
