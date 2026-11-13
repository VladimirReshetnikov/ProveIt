module
public import M6.Source.ExactTrie
@[expose] public section
namespace M6.Source.PathTrie

def fastAfter (p : Path) : Option (Option Nat) :=
  match successor p with
  | none => some none
  | some q => some <$> lookup exactTrie q

def fastResolve (s : Site) : Option Instruction :=
  match s.op with
  | .inc r => do
      let n ← fastAfter s.path
      return .inc r n
  | .dec r => do
      let p ← cut s.path false 1
      let z ← fastAfter p
      let n ← fastAfter s.path
      return .dec r z n
  | .breakTo k => do
      let p ← cut s.path false k
      let n ← fastAfter p
      return .jump n
  | .continueTo k => do
      let p ← cut s.path true k
      let target ← lookup exactTrie p
      return .jump (some target)
  | .halt => some .halt

theorem fastAfter_eq (p : Path) : fastAfter p = after exactSites p := by
  simp only [fastAfter,after,exact_lookup]
  rfl
theorem fastResolve_eq (s : Site) : fastResolve s = resolve exactSites s := by
  cases h : s.op <;> simp only [fastResolve,resolve,h,fastAfter_eq,exact_lookup]

def fastResolveAt (i : Nat) : Option Instruction := exactSites[i]? >>= fastResolve

theorem fastResolveAt_eq (i : Nat) : fastResolveAt i = resolveAt exactSites i := by
  have hf : fastResolve = resolve exactSites := funext fastResolve_eq
  simp only [fastResolveAt,resolveAt,hf]
#print axioms fastResolveAt_eq
end M6.Source.PathTrie

