import DiophantineConsistency.AnnotatedRuleCoordinates
import DiophantineConsistency.ArithmeticFiniteSwitch
import Mathlib.Tactic.FinCases

/-! # Literal output and premise schedules for all seventeen original rules -/
namespace DiophantineConsistency.AnnotatedRuleSchedules
open SetTheory SetTheory.Form AnnotatedProofChecker AnnotatedProofCode AnnotatedCodeArithmetic
open AnnotatedRename (forkCode variableCode binaryCode unaryCode bottomCode)
open AnnotatedRuleCoordinates (Coordinates encode quote Good)
open ScalarPRCode DirectScalar
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

/-- Rule tags agree with the order of the frozen original constructors. -/
def rule (tag : Fin 17) (G : List Form) (a b c : Form) (i j : Nat) : Rule :=
  match tag.val with
  | 0 => .ass G a
  | 1 => .impI G a b
  | 2 => .impE G a b
  | 3 => .botE G a
  | 4 => .lem G a
  | 5 => .andI G a b
  | 6 => .andE1 G a b
  | 7 => .andE2 G a b
  | 8 => .orI1 G a b
  | 9 => .orI2 G a b
  | 10 => .orE G a b c
  | 11 => .allI G a
  | 12 => .allE G a i
  | 13 => .exI G a i
  | 14 => .exE G a c
  | 15 => .eqRefl G i
  | 16 => .eqElim G i j a
  | _ => .ass G a

def outputBody (tag : Nat) (r : Coordinates) : Nat :=
  match tag with
  | 0 | 3 | 6 => forkCode r.context r.a
  | 1 => forkCode r.context (binaryCode 3 r.a r.b)
  | 2 | 7 => forkCode r.context r.b
  | 4 => forkCode r.context (binaryCode 5 r.a (binaryCode 3 r.a bottomCode))
  | 5 => forkCode r.context (binaryCode 4 r.a r.b)
  | 8 | 9 => forkCode r.context (binaryCode 5 r.a r.b)
  | 10 | 14 => forkCode r.context r.c
  | 11 => forkCode r.context (unaryCode 6 r.a)
  | 12 => forkCode r.context r.instI
  | 13 => forkCode r.context (unaryCode 7 r.a)
  | 15 => forkCode r.context (variableCode 1 r.i r.i)
  | 16 => forkCode r.context r.instJ
  | _ => 0

def outputCode (tag : Nat) (r : Coordinates) : Nat := if tag<17 then outputBody tag r else 0

def premiseBodies (tag : Nat) (r : Coordinates) : List Nat :=
  match tag with
  | 0 | 4 | 15 => []
  | 1 => [forkCode (forkCode r.a r.context) r.b]
  | 2 => [forkCode r.context (binaryCode 3 r.a r.b),forkCode r.context r.a]
  | 3 => [forkCode r.context bottomCode]
  | 5 => [forkCode r.context r.a,forkCode r.context r.b]
  | 6 | 7 => [forkCode r.context (binaryCode 4 r.a r.b)]
  | 8 => [forkCode r.context r.a]
  | 9 => [forkCode r.context r.b]
  | 10 => [forkCode r.context (binaryCode 5 r.a r.b),
      forkCode (forkCode r.a r.context) r.c,forkCode (forkCode r.b r.context) r.c]
  | 11 => [forkCode r.shifted r.a]
  | 12 => [forkCode r.context (unaryCode 6 r.a)]
  | 13 => [forkCode r.context r.instI]
  | 14 => [forkCode r.context (unaryCode 7 r.a),forkCode (forkCode r.a r.shifted) r.shiftC]
  | 16 => [forkCode r.context (variableCode 1 r.i r.j),forkCode r.context r.instI]
  | _ => []

def premiseCode (tag : Nat) (r : Coordinates) : Nat :=
  if tag<17 then listCode (premiseBodies tag r) else 0

def tagValue (tag : Nat) : Nat := if tag<17 then 1 else 0

theorem tagValue_eq_one (tag : Nat) : tagValue tag=1 ↔ tag<17 := by simp [tagValue]

def tagProgram : R tagValue := by
  refine (ifZero (sub identity (constant 16)) (constant 1) Realizes.zero).ofEq ?_
  intro n
  have h : n-16=0 ↔ n<17 := by omega
  simp only [tagValue,id_eq,h]

theorem output_quote (tag : Fin 17) (G : List Form) (a b c : Form) (i j : Nat) :
    outputCode tag.val (quote G a b c i j)=judgmentCode (rule tag G a b c i j).output := by
  fin_cases tag <;> rfl

theorem premises_quote (tag : Fin 17) (G : List Form) (a b c : Form) (i j : Nat) :
    premiseBodies tag.val (quote G a b c i j)=
      (rule tag G a b c i j).premises.map judgmentCode := by
  fin_cases tag <;> rfl

/-- A validated raw coordinate packet gives an actual original rule with
exactly these output/premise codes. Side and parent checks remain separate. -/
theorem schedules_sound (tag : Fin 17) (r : Coordinates) (h : Good r) :
    ∃ original : Rule,outputCode tag.val r=judgmentCode original.output ∧
      premiseBodies tag.val r=original.premises.map judgmentCode := by
  obtain ⟨G,a,b,c,hr⟩ := h
  rw [hr]
  exact ⟨rule tag G a b c r.i r.j,output_quote tag G a b c r.i r.j,
    premises_quote tag G a b c r.i r.j⟩

/-- Literal inverse embedding of every original rule, with bottom in unused
formula coordinates. This is finite Type-valued data, not proof selection. -/
def ofRule : Rule → Fin 17 × Coordinates
  | .ass G a => (0,quote G a fBot fBot 0 0)
  | .impI G a b => (1,quote G a b fBot 0 0)
  | .impE G a b => (2,quote G a b fBot 0 0)
  | .botE G a => (3,quote G a fBot fBot 0 0)
  | .lem G a => (4,quote G a fBot fBot 0 0)
  | .andI G a b => (5,quote G a b fBot 0 0)
  | .andE1 G a b => (6,quote G a b fBot 0 0)
  | .andE2 G a b => (7,quote G a b fBot 0 0)
  | .orI1 G a b => (8,quote G a b fBot 0 0)
  | .orI2 G a b => (9,quote G a b fBot 0 0)
  | .orE G a b c => (10,quote G a b c 0 0)
  | .allI G a => (11,quote G a fBot fBot 0 0)
  | .allE G a i => (12,quote G a fBot fBot i 0)
  | .exI G a i => (13,quote G a fBot fBot i 0)
  | .exE G a c => (14,quote G a fBot c 0 0)
  | .eqRefl G i => (15,quote G fBot fBot fBot i 0)
  | .eqElim G i j a => (16,quote G a fBot fBot i j)

theorem ofRule_good (original : Rule) : Good (ofRule original).2 := by
  cases original <;> simp only [ofRule,AnnotatedRuleCoordinates.Good,
    AnnotatedRuleCoordinates.quote] <;> exact ⟨_,_,_,_,rfl⟩

theorem ofRule_output (original : Rule) :
    outputCode (ofRule original).1.val (ofRule original).2=judgmentCode original.output := by
  cases original <;> rfl

theorem ofRule_premises (original : Rule) :
    premiseBodies (ofRule original).1.val (ofRule original).2=original.premises.map judgmentCode := by
  cases original <;> rfl

namespace P
open AnnotatedRenameLocal.Program (tag depth first second input output)

def context : R (fun n => (AnnotatedRuleCoordinates.decode n).context) := tag identity
def shifted : R (fun n => (AnnotatedRuleCoordinates.decode n).shifted) := depth identity
def a : R (fun n => (AnnotatedRuleCoordinates.decode n).a) := first identity
def b : R (fun n => (AnnotatedRuleCoordinates.decode n).b) := second identity
def c : R (fun n => (AnnotatedRuleCoordinates.decode n).c) := input identity
def instI : R (fun n => (AnnotatedRuleCoordinates.decode n).instI) := tag (output identity)
def instJ : R (fun n => (AnnotatedRuleCoordinates.decode n).instJ) := depth (output identity)
def shiftC : R (fun n => (AnnotatedRuleCoordinates.decode n).shiftC) := first (output identity)
def i : R (fun n => (AnnotatedRuleCoordinates.decode n).i) := second (output identity)
def j : R (fun n => (AnnotatedRuleCoordinates.decode n).j) := input (output identity)

def fork {f g : Nat → Nat} (p : R f) (q : R g) : R (fun n => forkCode (f n) (g n)) :=
  AnnotatedRenameArithmetic.fork p q

def binary {f g : Nat → Nat} (label : Nat) (p : R f) (q : R g) :
    R (fun n => binaryCode label (f n) (g n)) :=
  AnnotatedRenameArithmetic.binary (constant label) p q

def unary {f : Nat → Nat} (label : Nat) (p : R f) : R (fun n => unaryCode label (f n)) :=
  AnnotatedRenameArithmetic.unary (constant label) p

def bottom : R (fun _ => bottomCode) :=
  fork (AnnotatedRenameArithmetic.atom (constant 2)) (AnnotatedRenameArithmetic.atom (constant 0))

def equality : R (fun n => variableCode 1 (AnnotatedRuleCoordinates.decode n).i (AnnotatedRuleCoordinates.decode n).j) :=
  AnnotatedRenameArithmetic.variableNode (constant 1) i j

def outputBodyProgram : (label : Nat) → R (fun n => outputBody label (AnnotatedRuleCoordinates.decode n))
  | 0 | 3 | 6 => fork context a
  | 1 => fork context (binary 3 a b)
  | 2 | 7 => fork context b
  | 4 => fork context (binary 5 a (binary 3 a bottom))
  | 5 => fork context (binary 4 a b)
  | 8 | 9 => fork context (binary 5 a b)
  | 10 | 14 => fork context c
  | 11 => fork context (unary 6 a)
  | 12 => fork context instI
  | 13 => fork context (unary 7 a)
  | 15 => fork context (AnnotatedRenameArithmetic.variableNode (constant 1) i i)
  | 16 => fork context instJ
  | _+17 => Realizes.zero

def cons {f g : Nat → Nat} (p : R f) (q : R g) :
    R (fun n => Nat.pair (f n) (g n)+1) := successor (p.pair q)

def one {f : Nat → Nat} (p : R f) : R (fun n => listCode [f n]) := cons p Realizes.zero

def two {f g : Nat → Nat} (p : R f) (q : R g) : R (fun n => listCode [f n,g n]) := cons p (one q)

def three {f g h : Nat → Nat} (p : R f) (q : R g) (r : R h) :
    R (fun n => listCode [f n,g n,h n]) := cons p (two q r)

def premiseBodyProgram : (label : Nat) → R (fun n => listCode (premiseBodies label (AnnotatedRuleCoordinates.decode n)))
  | 0 | 4 | 15 => Realizes.zero
  | 1 => one (fork (fork a context) b)
  | 2 => two (fork context (binary 3 a b)) (fork context a)
  | 3 => one (fork context bottom)
  | 5 => two (fork context a) (fork context b)
  | 6 | 7 => one (fork context (binary 4 a b))
  | 8 => one (fork context a)
  | 9 => one (fork context b)
  | 10 => three (fork context (binary 5 a b)) (fork (fork a context) c) (fork (fork b context) c)
  | 11 => one (fork shifted a)
  | 12 => one (fork context (unary 6 a))
  | 13 => one (fork context instI)
  | 14 => two (fork context (unary 7 a)) (fork (fork a shifted) shiftC)
  | 16 => two (fork context equality) (fork context instI)
  | _+17 => Realizes.zero

def outputProgram : R (fun n => outputCode n.unpair.1 (AnnotatedRuleCoordinates.decode n.unpair.2)) :=
  ArithmeticFiniteSwitch.program (fun label n => outputBody label (AnnotatedRuleCoordinates.decode n)) outputBodyProgram 17

def premiseProgram : R (fun n => premiseCode n.unpair.1 (AnnotatedRuleCoordinates.decode n.unpair.2)) :=
  ArithmeticFiniteSwitch.program (fun label n => listCode (premiseBodies label (AnnotatedRuleCoordinates.decode n)))
    premiseBodyProgram 17

end P

theorem outputProgram_input (tag : Nat) (r : Coordinates) :
    P.outputProgram.val.eval (Nat.pair tag (encode r))=outputCode tag r := by
  rw [P.outputProgram.property]
  simp only [Nat.unpair_pair,AnnotatedRuleCoordinates.decode_encode]

theorem premiseProgram_input (tag : Nat) (r : Coordinates) :
    P.premiseProgram.val.eval (Nat.pair tag (encode r))=premiseCode tag r := by
  rw [P.premiseProgram.property]
  simp only [Nat.unpair_pair,AnnotatedRuleCoordinates.decode_encode]

theorem outputProgram_primrec : Nat.Primrec P.outputProgram.val.eval := P.outputProgram.val.primrec

theorem premiseProgram_primrec : Nat.Primrec P.premiseProgram.val.eval := P.premiseProgram.val.primrec

/-- The supplied programs agree with an actual original rule even for raw,
noncanonical coordinate packet codes, once coordinate validation succeeds. -/
theorem programs_sound (tag : Fin 17) (coordinates evidence : Nat)
    (h : AnnotatedRuleCoordinates.P.program.val.eval (Nat.pair coordinates evidence)=1) :
    ∃ original : Rule,
      P.outputProgram.val.eval (Nat.pair tag.val coordinates)=judgmentCode original.output ∧
      P.premiseProgram.val.eval (Nat.pair tag.val coordinates)=
        listCode (original.premises.map judgmentCode) := by
  have hg := AnnotatedRuleCoordinates.program_sound (Nat.pair coordinates evidence) h
  simp only [Nat.unpair_pair] at hg
  obtain ⟨original,ho,hp⟩ := schedules_sound tag (AnnotatedRuleCoordinates.decode coordinates) hg
  refine ⟨original,?_,?_⟩
  · rw [P.outputProgram.property]
    simpa only [Nat.unpair_pair] using ho
  · rw [P.premiseProgram.property]
    simp only [Nat.unpair_pair,premiseCode,tag.isLt,if_true,hp]

theorem programs_complete (original : Rule) :
    ∃ coordinates evidence : Nat,
      AnnotatedRuleCoordinates.P.program.val.eval (Nat.pair coordinates evidence)=1 ∧
      P.outputProgram.val.eval (Nat.pair (ofRule original).1.val coordinates)=
        judgmentCode original.output ∧
      P.premiseProgram.val.eval (Nat.pair (ofRule original).1.val coordinates)=
        listCode (original.premises.map judgmentCode) := by
  obtain ⟨evidence,he⟩ := (AnnotatedRuleCoordinates.exists_program_iff (ofRule original).2).mpr
    (ofRule_good original)
  refine ⟨encode (ofRule original).2,evidence,he,?_,?_⟩
  · rw [outputProgram_input,ofRule_output]
  · rw [premiseProgram_input,premiseCode,if_pos (ofRule original).1.isLt,ofRule_premises]

theorem outputProgram_nodeCount : P.outputProgram.val.nodeCount=2537 := by decide
theorem optimizedOutputProgram_nodeCount : P.outputProgram.optimize.val.nodeCount=2377 := by decide
theorem premiseProgram_nodeCount : P.premiseProgram.val.nodeCount=2683 := by decide
theorem optimizedPremiseProgram_nodeCount : P.premiseProgram.optimize.val.nodeCount=2483 := by decide

end DiophantineConsistency.AnnotatedRuleSchedules
