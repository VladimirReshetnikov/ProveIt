import DiophantineConsistency.PRAFiniteFunctionCodes
import Mathlib.Data.Nat.Pairing
import Lean.Elab.Tactic.Omega

/-! An explicit numerical representation of finite primitive-recursive codes.
A tagged binary tree records constructors, arities and projection indices.
The structural parser checks every arity before constructing indexed syntax;
Cantor pairing gives a total numeric tree decoder and an exact roundtrip.
This proves encodability, not a primitive-recursive bound on the decoder,
a PRA axiom recognizer, or a conservation theorem. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRACodeEncoding
inductive Tree where
 | leaf : ℕ → Tree
 | node : Tree → Tree → Tree
 deriving DecidableEq, Repr

def encode : Tree → ℕ
 | .leaf n => Nat.pair 0 n
 | .node a b => Nat.pair (encode a + 1) (encode b)

def decode (n : ℕ) : Tree :=
  let p := Nat.unpair n
  if h : p.1 = 0 then .leaf p.2
  else .node (decode (p.1-1)) (decode p.2)
termination_by n
decreasing_by
  · change (Nat.unpair n).1 ≠ 0 at h
    have hle := Nat.unpair_left_le n
    omega
  · change (Nat.unpair n).1 ≠ 0 at h
    have hle := Nat.unpair_add_le n
    omega

theorem decode_encode : ∀ t, decode (encode t) = t
 | .leaf n => by simp [encode, decode, Nat.unpair_pair]
 | .node a b => by
   simp [encode, decode, decode_encode]
end DiophantineConsistency.PRACodeEncoding
namespace DiophantineConsistency.PRACodeEncoding
open DiophantineConsistency.PRAFiniteFunctionCodes

inductive Packed where
 | code : (n : ℕ) → Code n → Packed
 | codes : (n m : ℕ) → Codes n m → Packed

mutual
 def codeTree : {n : ℕ} → Code n → Tree
  | _, .zero n => .node (.leaf 0) (.leaf n)
  | _, .succ => .leaf 1
  | n, .proj i => .node (.leaf 2) (.node (.leaf n) (.leaf i.val))
  | _, .comp f g => .node (.leaf 3) (.node (codeTree f) (codesTree g))
  | _, .prec f g => .node (.leaf 4) (.node (codeTree f) (codeTree g))
 def codesTree : {n m : ℕ} → Codes n m → Tree
  | n, _, .nil _ => .node (.leaf 5) (.leaf n)
  | _, _, .cons h t => .node (.leaf 6) (.node (codeTree h) (codesTree t))
end

def parse : Tree → Option Packed
 | .leaf 1 => some (.code 1 .succ)
 | .node (.leaf 0) (.leaf n) => some (.code n (.zero n))
 | .node (.leaf 2) (.node (.leaf n) (.leaf i)) =>
    if h : i < n then some (.code n (.proj ⟨i,h⟩)) else none
 | .node (.leaf 3) (.node f g) =>
    match parse f, parse g with
    | some (.code m f'), some (.codes n k g') =>
      if h : m = k then some (.code n (.comp (h ▸ f') g')) else none
    | _, _ => none
 | .node (.leaf 4) (.node f g) =>
    match parse f, parse g with
    | some (.code n f'), some (.code k g') =>
      if h : k = n + 2 then some (.code (n+1) (.prec f' (h ▸ g'))) else none
    | _, _ => none
 | .node (.leaf 5) (.leaf n) => some (.codes n 0 (.nil n))
 | .node (.leaf 6) (.node a b) =>
    match parse a, parse b with
    | some (.code n a'), some (.codes k m b') =>
      if h : n = k then some (.codes k (m+1) (.cons (h ▸ a') b')) else none
    | _, _ => none
 | _ => none

mutual
 theorem parse_code : ∀ {n : ℕ} (c : Code n), parse (codeTree c) = some (.code n c)
  | _, .zero _ => by simp [codeTree, parse]
  | _, .succ => by simp [codeTree, parse]
  | _, .proj i => by simp [codeTree, parse, i.isLt]
  | _, .comp f g => by simp [codeTree, parse, parse_code f, parse_codes g]
  | _, .prec f g => by simp [codeTree, parse, parse_code f, parse_code g]
 theorem parse_codes : ∀ {n m : ℕ} (cs : Codes n m), parse (codesTree cs) = some (.codes n m cs)
  | _, _, .nil _ => by simp [codesTree, parse]
  | _, _, .cons a b => by simp [codesTree, parse, parse_code a, parse_codes b]
end
def encodeCode {n : ℕ} (c : Code n) : ℕ := encode (codeTree c)

def decodeCode (n x : ℕ) : Option (Code n) :=
  match parse (decode x) with
  | some (.code m c) => if h : m = n then some (h ▸ c) else none
  | _ => none

theorem decodeCode_encodeCode {n : ℕ} (c : Code n) :
    decodeCode n (encodeCode c) = some c := by
  simp [decodeCode, encodeCode, decode_encode, parse_code]

instance {n : ℕ} : Encodable (Code n) where
  encode := encodeCode
  decode := decodeCode n
  encodek := decodeCode_encodeCode
end DiophantineConsistency.PRACodeEncoding
