module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualProofCompiler
@[expose] public section
open M6.Arithmetic.PA

/-! Version 1 of the actual-basis numeric certificate format. This is not
Foundation's PA proof predicate or its HFS sequence coding. -/
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor

def pack2 (a b : Nat) := pair a (pair b 0)
def pack3 (a b c : Nat) := pair a (pack2 b c)
def pack4 (a b c d : Nat) := pair a (pack3 b c d)
def unpack2 (n : Nat) : Option (Nat × Nat) :=
  let p := decode n
  let q := decode p.2
  if q.2=0 then some (p.1,q.1) else none
def unpack3 (n : Nat) : Option (Nat × Nat × Nat) := do
  let p := decode n
  let q ← unpack2 p.2
  pure (p.1,q)
def unpack4 (n : Nat) : Option (Nat × Nat × Nat × Nat) := do
  let p := decode n
  let q ← unpack3 p.2
  pure (p.1,q)

@[simp] theorem unpack_pack2 (a b : Nat) : unpack2 (pack2 a b) = some (a,b) := by
  simp [unpack2,pack2,decode_pair]
@[simp] theorem unpack_pack3 (a b c : Nat) : unpack3 (pack3 a b c) = some (a,b,c) := by
  simp [unpack3,pack3,decode_pair]
@[simp] theorem unpack_pack4 (a b c d : Nat) : unpack4 (pack4 a b c d) = some (a,b,c,d) := by
  simp [unpack4,pack4,decode_pair]

/-- Tags MP0, GEN1, R1..R8=2..9, guarded bundle10; all other tags reject.
Every fixed-arity payload has a checked zero tail. MP explicitly stores its
conclusion, while both premise conclusions are independently checked. -/
def ruleCheck (rec : Nat → Option Nat) (tag data : Nat) : Option Nat :=
  match tag with
  | 0 => do
    let (b,p,q) ← unpack3 data
    let a ← rec p
    let i ← rec q
    if i=AXCode.wim a b then some b else none
  | 1 => do
    let (a,p) ← unpack2 data
    let b ← rec p
    pure (AXCode.wal a b)
  | 2 => do
    let (a,b) ← unpack2 data
    pure (ActualAXCode.rho1 a b)
  | 3 => do
    let (a,b,c) ← unpack3 data
    pure (ActualAXCode.rho2 a b c)
  | 4 => do
    let (a,b,c) ← unpack3 data
    pure (ActualAXCode.rho3 a b c)
  | 5 => do
    let (a,b,c) ← unpack3 data
    pure (ActualAXCode.rho4 a b c)
  | 6 => do
    let (a,b,c) ← unpack3 data
    pure (ActualAXCode.rho5 a b c)
  | 7 => do
    let (a,b) ← unpack2 data
    pure (ActualAXCode.rho6 a b)
  | 8 => do
    let (a,b,c) ← unpack3 data
    pure (ActualAXCode.rho7 a b c)
  | 9 => do
    let (a,b,c,u) ← unpack4 data
    if u≤a then some (ActualAXCode.rho8 a b c u) else none
  | 10 => do
    let (a,b,c) ← unpack3 data
    if c≠a ∧ c≠b then some (ActualAXCode.bundle a b c) else none
  | _ => none

def check : Nat → Nat → Option Nat
  | 0,_ => none
  | fuel+1,n => let p := decode n; ruleCheck (check fuel) p.1 p.2

/-- The external certificate carries an explicit depth budget. `some 0` is a
successful proof of code zero; it is never conflated with rejection. -/
def verify (certificate : Nat) : Option Nat :=
  let p := decode certificate
  check p.1 p.2

def encode {a : Nat} : Proof a → Nat
  | .mp (b := b) p q => pair 0 (pack3 b (encode p) (encode q))
  | .all a p => pair 1 (pack2 a (encode p))
  | .r1 a b => pair 2 (pack2 a b)
  | .r2 a b c => pair 3 (pack3 a b c)
  | .r3 a b c => pair 4 (pack3 a b c)
  | .r4 a b c => pair 5 (pack3 a b c)
  | .r5 a b c => pair 6 (pack3 a b c)
  | .r6 a b => pair 7 (pack2 a b)
  | .r7 a b c => pair 8 (pack3 a b c)
  | .r8 a b c u _ => pair 9 (pack4 a b c u)
  | .bundle a b c _ _ => pair 10 (pack3 a b c)

def depth {a : Nat} : Proof a → Nat
  | .mp p q => max (depth p) (depth q) + 1
  | .all _ p => depth p + 1
  | .r1 _ _ => 1
  | .r2 _ _ _ => 1
  | .r3 _ _ _ => 1
  | .r4 _ _ _ => 1
  | .r5 _ _ _ => 1
  | .r6 _ _ => 1
  | .r7 _ _ _ => 1
  | .r8 _ _ _ _ _ => 1
  | .bundle _ _ _ _ _ => 1

def certificate {a : Nat} (p : Proof a) := pair (depth p) (encode p)
end M6.PA.NativeCalculus.ActualBasis.Code

