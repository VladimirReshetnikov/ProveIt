module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualProofCodeComplete
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor M6.Source.Enumeration
open M6.Source.ActualCommandMacros

/-- Deterministic syntax-directed compilation. Malformed fields/invalid tags
produce the empty word. Recursive acceptance is checked separately by `check`;
this compiler never selects or assumes a Proof witness. -/
def ruleCompile (rec : Nat → List Command) (tag data : Nat) : List Command :=
  match tag with
  | 0 => match unpack3 data with
    | some (b,p,q) => rec q ++ PUSH ++ rec p ++ PUSH ++ mpTail b
    | none => []
  | 1 => match unpack2 data with
    | some (a,p) => rec p ++ genTail a
    | none => []
  | 2 => match unpack2 data with
    | some (a,b) => headWord 1 a b 0
    | none => []
  | 3 => match unpack3 data with
    | some (a,b,c) => headWord 2 a b c
    | none => []
  | 4 => match unpack3 data with
    | some (a,b,c) => headWord 3 a b c
    | none => []
  | 5 => match unpack3 data with
    | some (a,b,c) => headWord 4 a b c
    | none => []
  | 6 => match unpack3 data with
    | some (a,b,c) => headWord 5 a b c
    | none => []
  | 7 => match unpack2 data with
    | some (a,b) => headWord 6 a b 0
    | none => []
  | 8 => match unpack3 data with
    | some (a,b,c) => headWord 7 a b c
    | none => []
  | 9 => match unpack4 data with
    | some (a,b,c,u) => if u≤a then head8Word a b c u else []
    | none => []
  | 10 => match unpack3 data with
    | some (a,b,c) => if c≠a ∧ c≠b then gateWord a b c else []
    | none => []
  | _ => []

def compileTree : Nat → Nat → List Command
  | 0,_ => []
  | fuel+1,tree => let p:=decode tree; ruleCompile (compileTree fuel) p.1 p.2

def compileCertificate (code : Nat) : List Command :=
  let p:=decode code; compileTree p.1 p.2

theorem compileTree_pair (fuel tag data : Nat) :
    compileTree (fuel+1) (pair tag data) = ruleCompile (compileTree fuel) tag data := by
  simp only [compileTree,decode_pair]

end M6.PA.NativeCalculus.ActualBasis.Code

