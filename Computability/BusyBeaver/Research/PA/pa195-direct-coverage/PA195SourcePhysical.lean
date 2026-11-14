import PA195SourceTree
import PA195Symbolic
import M6.Source.PhysicalRegisters

/-! Generate the actual physical obligations directly from the formal source
trie and its upstream resolver. No archived source.json claims are used. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195SourcePhysical
open M6.Source M6.Source.PathTrie M6.FastResolve PA195.SourceTree
open M6.Zip M6.Runtime PA195RuntimeEngine PA195Symbolic

abbrev physical (r : Fin 9) : Nat := M6.Source.physicalRegister r

def sourceCases (i : Nat) : Option (List Contract) := do
  let site ← nthSite trie i
  let instr ← resolveTree trie site
  let start := frame site.path 0 .none
  match instr with
  | .inc r (some j) =>
      let next ← nthSite trie j
      pure [⟨none, start, some (frame next.path 0 (.inc (physical r)))⟩]
  | .dec r (some z) (some p) =>
      let zero ← nthSite trie z
      let pos ← nthSite trie p
      pure [⟨some (physical r, true), start, some (frame zero.path 0 .none)⟩,
            ⟨some (physical r, false), start, some (frame pos.path 1 (.dec (physical r)))⟩]
  | .jump (some j) =>
      let next ← nthSite trie j
      pure [⟨none, start, some (frame next.path 0 .none)⟩]
  | .halt => pure [⟨none, start, none⟩]
  | _ => none

def acceptedSite (i : Nat) : Bool :=
  match sourceCases i with
  | none => false
  | some cs => cs.all (accepted machine)

theorem site_cases_sound (i : Nat) (cs : List Contract)
    (hcases : sourceCases i = some cs) (haccept : acceptedSite i = true)
    (c : Contract) (hc : c ∈ cs) (n : Nat) (vs : List Nat) (hv : Valid c.branch vs) :
    ∃ s, targetPredicate c.target s = true ∧ Reach1 machine (conc n vs c.start) (conc n vs s) := by
  have hall : cs.all (accepted machine) = true := by simpa [acceptedSite, hcases] using haccept
  exact accepted_sound machine box_lemmas c ((List.all_eq_true.mp hall) c hc) n vs hv

def branchCount : Tree → Nat
  | .leaf (.dec _) => 2
  | .leaf _ => 1
  | .node l r => branchCount l + branchCount r

theorem source_site_count : size trie = 3700 := by decide +kernel

theorem source_branch_count : branchCount trie = 4815 := by decide +kernel

example : acceptedSite 25 = true := by decide +kernel
#print axioms source_site_count
#print axioms source_branch_count
#print axioms site_cases_sound
end PA195SourcePhysical
