import DiophantineConsistency.AnnotatedParents
import DiophantineConsistency.AnnotatedRuleSide

/-! # Literal numeric validation of every original parent-index proof line -/
namespace DiophantineConsistency.AnnotatedLine
open SetTheory SetTheory.Form AnnotatedProofChecker AnnotatedProofCode AnnotatedCodeArithmetic
open AnnotatedRename (Row rowCode decodeRow decodeRow_rowCode)
open ScalarPRCode DirectScalar
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedRuleCoordinates.check AnnotatedParents.check

def equal (a b : Nat) : Nat := if a=b then 1 else 0
@[simp] theorem equal_one (a b : Nat) : equal a b=1 ↔ a=b := by simp [equal]

/-- The six fields are tag, coordinates, coordinate evidence, side witness,
parent-list code, and claimed output. The last field allows the scanner to
append the already checked output without recomputing its schedule. -/
def rowCheck (history : Nat) (r : Row) : Nat :=
  AnnotatedRuleSchedules.tagValue r.tag *
    (AnnotatedRuleCoordinates.P.value (Nat.pair r.depth r.first) *
      (AnnotatedRuleSide.value r.tag (AnnotatedRuleCoordinates.decode r.depth) r.second *
        (AnnotatedParents.check 3 history
          (AnnotatedRuleSchedules.premiseCode r.tag (AnnotatedRuleCoordinates.decode r.depth)) r.input *
            equal r.output (AnnotatedRuleSchedules.outputCode r.tag (AnnotatedRuleCoordinates.decode r.depth)))))

def check (history line : Nat) : Nat := rowCheck history (decodeRow line)

theorem premises_length (original : Rule) : original.premises.length≤3 := by
  cases original <;> simp [Rule.premises]

/-- Relative to the actual history maintained by the scanner, every accepted
raw row recovers an exact old line, its parent list, and its output judgment. -/
theorem rowCheck_sound (history : List Judgment) (r : Row)
    (h : rowCheck (listCode (history.map judgmentCode)) r=1) :
    ∃ original : Line,r.output=judgmentCode original.rule.output ∧
      r.input=listCode original.parents ∧ original.valid history=true := by
  simp only [rowCheck,AnnotatedSchemaMaps.mul_eq_one_nat,equal_one] at h
  rcases h with ⟨ht,hc,hs,hp,ho⟩
  have htag := (AnnotatedRuleSchedules.tagValue_eq_one r.tag).mp ht
  let tag : Fin 17 := ⟨r.tag,htag⟩
  let coordinates := AnnotatedRuleCoordinates.decode r.depth
  have hg : AnnotatedRuleCoordinates.Good coordinates := by
    apply AnnotatedRuleCoordinates.check_sound _ (decodeRow r.first)
    simpa only [AnnotatedRuleCoordinates.P.value,Nat.unpair_pair] using hc
  obtain ⟨G,a,b,c,hr⟩ := hg
  let original := AnnotatedRuleSchedules.rule tag G a b c coordinates.i coordinates.j
  change AnnotatedRuleSide.value tag.val coordinates r.second=1 at hs
  rw [hr] at hs
  have hside : original.side=true := AnnotatedRuleSide.quote_sound tag G a b c
    coordinates.i coordinates.j r.second hs
  change AnnotatedParents.check 3 (listCode (history.map judgmentCode))
    (AnnotatedRuleSchedules.premiseCode tag.val coordinates) r.input=1 at hp
  rw [hr,AnnotatedRuleSchedules.premiseCode,if_pos tag.isLt,
    AnnotatedRuleSchedules.premises_quote] at hp
  obtain ⟨parents,hwire,hlookups⟩ := (AnnotatedParents.check_judgments_raw 3 history
    original.premises r.input (premises_length original)).mp hp
  change r.output=AnnotatedRuleSchedules.outputCode tag.val coordinates at ho
  rw [hr,AnnotatedRuleSchedules.output_quote] at ho
  refine ⟨⟨original,parents⟩,ho,hwire,?_⟩
  simp only [Line.valid,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨hside,hlookups⟩

theorem check_sound (history : List Judgment) (line : Nat)
    (h : check (listCode (history.map judgmentCode)) line=1) :
    ∃ original : Line,(decodeRow line).output=judgmentCode original.rule.output ∧
      (decodeRow line).input=listCode original.parents ∧ original.valid history=true :=
  rowCheck_sound history (decodeRow line) h

/-- Every original valid line has a numeric certificate, with exactly its
original parent-list code and output judgment code. -/
theorem rowCheck_complete (history : List Judgment) (original : Line)
    (h : original.valid history=true) :
    ∃ r : Row,r.output=judgmentCode original.rule.output ∧ r.input=listCode original.parents ∧
      rowCheck (listCode (history.map judgmentCode)) r=1 := by
  simp only [Line.valid,Bool.and_eq_true,decide_eq_true_eq] at h
  let tag := (AnnotatedRuleSchedules.ofRule original.rule).1
  let coordinates := (AnnotatedRuleSchedules.ofRule original.rule).2
  obtain ⟨evidence,he⟩ := (AnnotatedRuleCoordinates.exists_program_iff coordinates).mpr
    (AnnotatedRuleSchedules.ofRule_good original.rule)
  rw [AnnotatedRuleCoordinates.P.program.property] at he
  obtain ⟨membership,hm⟩ := (AnnotatedRuleSide.exists_ofRule_iff original.rule).mpr h.1
  have hp : AnnotatedRuleSchedules.premiseCode tag.val coordinates=
      listCode (original.rule.premises.map judgmentCode) := by
    simp only [tag,coordinates,AnnotatedRuleSchedules.premiseCode,
      (AnnotatedRuleSchedules.ofRule original.rule).1.isLt,if_true,
      AnnotatedRuleSchedules.ofRule_premises]
  have hparents := (AnnotatedParents.check_judgments 3 history original.rule.premises
    original.parents (premises_length original.rule)).mpr h.2
  refine ⟨⟨tag.val,AnnotatedRuleCoordinates.encode coordinates,evidence,membership,
    listCode original.parents,judgmentCode original.rule.output⟩,rfl,rfl,?_⟩
  simp only [rowCheck,AnnotatedRuleCoordinates.decode_encode,AnnotatedSchemaMaps.mul_eq_one_nat,equal_one]
  refine ⟨(AnnotatedRuleSchedules.tagValue_eq_one tag.val).mpr tag.isLt,he,hm,?_,?_⟩
  · rw [hp]
    exact hparents
  · exact (AnnotatedRuleSchedules.ofRule_output original.rule).symm

theorem check_complete (history : List Judgment) (original : Line)
    (h : original.valid history=true) :
    ∃ line : Nat,(decodeRow line).output=judgmentCode original.rule.output ∧
      (decodeRow line).input=listCode original.parents ∧ check (listCode (history.map judgmentCode)) line=1 := by
  obtain ⟨r,ho,hp,hc⟩ := rowCheck_complete history original h
  exact ⟨rowCode r,by simpa only [decodeRow_rowCode] using ho,
    by simpa only [decodeRow_rowCode] using hp,
    by simpa only [check,decodeRow_rowCode] using hc⟩

attribute [local irreducible] rowCheck check

namespace P
open AnnotatedRenameLocal.Program (tag depth first second input output)

def equalityProgram : R (fun n => equal n.unpair.1 n.unpair.2) :=
  ifEq Realizes.left Realizes.right (constant 1) Realizes.zero

def tagProgram : R (fun n => AnnotatedRuleSchedules.tagValue (decodeRow n.unpair.2).tag) :=
  AnnotatedRuleSchedules.tagProgram.comp (tag Realizes.right)

def coordinatesProgram : R (fun n => AnnotatedRuleCoordinates.P.value
    (Nat.pair (decodeRow n.unpair.2).depth (decodeRow n.unpair.2).first)) :=
  AnnotatedRuleCoordinates.P.program.comp ((depth Realizes.right).pair (first Realizes.right))

def sideProgram : R (fun n => AnnotatedRuleSide.value (decodeRow n.unpair.2).tag
    (AnnotatedRuleCoordinates.decode (decodeRow n.unpair.2).depth) (decodeRow n.unpair.2).second) :=
  (AnnotatedRuleSide.P.program.comp ((tag Realizes.right).pair
    ((depth Realizes.right).pair (second Realizes.right)))).ofEq
      (fun _ => by simp only [AnnotatedRuleSide.P.inputValue,Nat.unpair_pair])

def parentsProgram : R (fun n => AnnotatedParents.check 3 n.unpair.1
    (AnnotatedRuleSchedules.premiseCode (decodeRow n.unpair.2).tag
      (AnnotatedRuleCoordinates.decode (decodeRow n.unpair.2).depth)) (decodeRow n.unpair.2).input) :=
  ((AnnotatedParents.P.program 3).comp (Realizes.left.pair
    ((AnnotatedRuleSchedules.P.premiseProgram.comp ((tag Realizes.right).pair
      (depth Realizes.right))).pair (input Realizes.right)))).ofEq
        (fun _ => by simp only [AnnotatedParents.P.value,Nat.unpair_pair])

def outputProgram : R (fun n => equal (decodeRow n.unpair.2).output
    (AnnotatedRuleSchedules.outputCode (decodeRow n.unpair.2).tag
      (AnnotatedRuleCoordinates.decode (decodeRow n.unpair.2).depth))) :=
  (equalityProgram.comp ((output Realizes.right).pair
    (AnnotatedRuleSchedules.P.outputProgram.comp ((tag Realizes.right).pair
      (depth Realizes.right))))).ofEq (fun _ => by simp only [Nat.unpair_pair])

def value (n : Nat) : Nat := check n.unpair.1 n.unpair.2

def program : R value := by
  refine (mul tagProgram (mul coordinatesProgram (mul sideProgram (mul parentsProgram outputProgram)))).ofEq ?_
  intro n
  simp only [value,check,rowCheck]

end P

theorem program_input (history line : Nat) :
    P.program.val.eval (Nat.pair history line)=check history line := by
  rw [P.program.property]
  simp only [P.value,Nat.unpair_pair]

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.value := P.program.optimize

end DiophantineConsistency.AnnotatedLine
