import BusyBeaver.ZFC.ArithmeticCommandBlocks254

/-!
Unconditional numeric word row for the unchanged twelve C254 proof tags.
Inputs u,v are earlier WORD codes, not validator results. Tag0 emits discard
for every payload and tag11 emits the bundle leaf without a freshness gate.
The one public validity gate belongs to the later history module.

Neither internal execution nor PA consistency transport is
asserted. All circuit syntax is fixed external finite data.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofWordRow254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandBlocks254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def mpCircuit : Circuit := Circuit.mpBlock .input0 .input1 .input2
def genCircuit : Circuit := Circuit.genBlock .input0 .input1
def bundleCircuit : Circuit := Circuit.bundleLeaf .input0 .input1 .input2

noncomputable def rowValue (tag payload u v : V) : V := by
  classical
  let a := first payload
  let t := second payload
  let b := first t
  let c := second t
  exact if tag = 0 then Circuit.discard.eval 0 0 0 0
    else if tag = 1 then mpCircuit.eval a u v 0
    else if tag = 2 then genCircuit.eval a u 0 0
    else if tag = 3 then Circuit.leaf1.eval a t 0 0
    else if tag = 4 then Circuit.leaf2.eval a b c 0
    else if tag = 5 then Circuit.leaf3.eval a b c 0
    else if tag = 6 then Circuit.leaf4.eval a b c 0
    else if tag = 7 then Circuit.leaf5.eval a b c 0
    else if tag = 8 then Circuit.leaf6.eval a t 0 0
    else if tag = 9 then Circuit.leaf7.eval a b c 0
    else if tag = 10 then Circuit.leaf8.eval a b (first c) (second c)
    else if tag = 11 then bundleCircuit.eval a b c 0
    else 0

/-- Order(out,tag,payload,minorWord,majorWord); GEN's u was selected using
its whole-tail child before this row. No old field is bounded by its output. -/
def rowDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out tag payload u v.
    ∃ a, !ArithmeticCantor.firstDef a payload ∧
    ∃ t, !ArithmeticCantor.secondDef t payload ∧
    ∃ b, !ArithmeticCantor.firstDef b t ∧
    ∃ c, !ArithmeticCantor.secondDef c t ∧
    ∃ x, !ArithmeticCantor.firstDef x c ∧
    ∃ y, !ArithmeticCantor.secondDef y c ∧
    ((tag = 0 ∧ !(Circuit.discard.graph) out 0 0 0 0) ∨
     (tag = 1 ∧ !(mpCircuit.graph) out a u v 0) ∨
     (tag = 2 ∧ !(genCircuit.graph) out a u 0 0) ∨
     (tag = 3 ∧ !(Circuit.leaf1.graph) out a t 0 0) ∨
     (tag = 4 ∧ !(Circuit.leaf2.graph) out a b c 0) ∨
     (tag = 5 ∧ !(Circuit.leaf3.graph) out a b c 0) ∨
     (tag = 6 ∧ !(Circuit.leaf4.graph) out a b c 0) ∨
     (tag = 7 ∧ !(Circuit.leaf5.graph) out a b c 0) ∨
     (tag = 8 ∧ !(Circuit.leaf6.graph) out a t 0 0) ∨
     (tag = 9 ∧ !(Circuit.leaf7.graph) out a b c 0) ∨
     (tag = 10 ∧ !(Circuit.leaf8.graph) out a b x y) ∨
     (tag = 11 ∧ !(bundleCircuit.graph) out a b c 0) ∨
     ((tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3 ∧ tag ≠ 4 ∧ tag ≠ 5 ∧
       tag ≠ 6 ∧ tag ≠ 7 ∧ tag ≠ 8 ∧ tag ≠ 9 ∧ tag ≠ 10 ∧ tag ≠ 11) ∧ out = 0))”

instance row_defined : 𝚺₁-Function₄[V] rowValue via rowDef := .mk fun e => by
  classical
  simp [rowDef, numeral_eq_natCast]
  by_cases h0 : e 1 = 0
  · simp_all [rowValue]
  by_cases h1 : e 1 = 1
  · simp_all [rowValue]
  by_cases h2 : e 1 = 2
  · simp_all [rowValue]
  by_cases h3 : e 1 = 3
  · simp_all [rowValue]
  by_cases h4 : e 1 = 4
  · simp_all [rowValue]
  by_cases h5 : e 1 = 5
  · simp_all [rowValue]
  by_cases h6 : e 1 = 6
  · simp_all [rowValue]
  by_cases h7 : e 1 = 7
  · simp_all [rowValue]
  by_cases h8 : e 1 = 8
  · simp_all [rowValue]
  by_cases h9 : e 1 = 9
  · simp_all [rowValue]
  by_cases h10 : e 1 = 10
  · simp_all [rowValue]
  by_cases h11 : e 1 = 11
  · simp_all [rowValue]
  simp_all [rowValue]

def rowDeltaDef : 𝚫₁.Semisentence 5 := rowDef.graphDelta

instance row_defined_delta : 𝚫₁-Function₄[V] rowValue via rowDeltaDef := row_defined.graph_delta

theorem row_total (tag payload u v : V) :
    ∃! out, rowDef.val.Evalb ![out,tag,payload,u,v] := by simp

end SetTheory.BusyBeaver.ZFC.ArithmeticProofWordRow254
