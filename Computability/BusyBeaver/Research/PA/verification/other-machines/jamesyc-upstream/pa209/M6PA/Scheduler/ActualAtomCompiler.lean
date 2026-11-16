module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCodeCompilerSound
public import M6PA.Scheduler.ActualProofCodeLocality
public import M6.Source.CommandAtomEncoding
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor M6.Source.Enumeration
open M6.Source.ActualCommandMacros M6.Source.CommandAtomEncoding

def ruleCompileAtoms (rec : Nat → List Nat) (tag data : Nat) : List Nat :=
  match tag with
  | 0 => match unpack3 data with
    | some (b,p,q) => rec q ++ atoms PUSH ++ rec p ++ atoms PUSH ++ atoms (mpTail b)
    | none => []
  | 1 => match unpack2 data with
    | some (a,p) => rec p ++ atoms (genTail a)
    | none => []
  | 2 => match unpack2 data with
    | some (a,b) => atoms (headWord 1 a b 0)
    | none => []
  | 3 => match unpack3 data with
    | some (a,b,c) => atoms (headWord 2 a b c)
    | none => []
  | 4 => match unpack3 data with
    | some (a,b,c) => atoms (headWord 3 a b c)
    | none => []
  | 5 => match unpack3 data with
    | some (a,b,c) => atoms (headWord 4 a b c)
    | none => []
  | 6 => match unpack3 data with
    | some (a,b,c) => atoms (headWord 5 a b c)
    | none => []
  | 7 => match unpack2 data with
    | some (a,b) => atoms (headWord 6 a b 0)
    | none => []
  | 8 => match unpack3 data with
    | some (a,b,c) => atoms (headWord 7 a b c)
    | none => []
  | 9 => match unpack4 data with
    | some (a,b,c,u) => if u≤a then atoms (head8Word a b c u) else []
    | none => []
  | 10 => match unpack3 data with
    | some (a,b,c) => if c≠a ∧ c≠b then atoms (gateWord a b c) else []
    | none => []
  | _ => []

/-- Each fuel round stores actual finite lists of natural command atoms. -/
def compilerAtomTable (bound : Nat) : Nat → List (List Nat)
  | 0 => List.replicate (bound+1) []
  | fuel+1 => let previous:=compilerAtomTable bound fuel
      (List.range (bound+1)).map fun n => let p:=decode n
        ruleCompileAtoms (fun k => previous.getD k []) p.1 p.2

def compiledAtoms (code : Nat) : List Nat :=
  let p:=decode code
  (compilerAtomTable p.2 p.1).getD p.2 []

end M6.PA.NativeCalculus.ActualBasis.Code

