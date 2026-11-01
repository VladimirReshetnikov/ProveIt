import DiophantineConsistency.ArithmeticCommandRho8CircuitPerm222
import BusyBeaver.ZFC.ArithmeticRow222

/-! Unconditional numeric word row for the actual C222 validator. A fixed
rho8 circuit is selected before all Type0 models, enough for arithmetic
completeness. The row graph itself is literal model-independent syntax.
No internal proof history or full proof-compiler correctness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticProofWordRowPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254
open ArithmeticCommandCircuitPerm222 ArithmeticCommandLeafPerm222 ArithmeticCommandRulePerm222
open ArithmeticCommandRho8CircuitPerm222 (mpCircuit eval_mpCircuit)

/-- The fixed choice is made before any Type0 model or numeric inputs. -/
noncomputable def rho8Circuit : Circuit :=
  Classical.choose ArithmeticCommandRho8CircuitPerm222.exists_rho8_circuit.{0}

theorem rho8_contract {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b c u : V) : Contract (rho8Circuit.eval a b c u) (ArithmeticTemplates254.rho8 a b c u) :=
  Classical.choose_spec ArithmeticCommandRho8CircuitPerm222.exists_rho8_circuit.{0} a b c u

def genCircuit : Circuit := .append .input1 (Circuit.consDrop (.append (.load .input0)
  (Circuit.consNip (Circuit.consAx .input0 .zero .zero
    (.append (Circuit.nips 9) Circuit.terminator)))))
def bundleCircuit : Circuit := .append Circuit.discard (.append (.load .zero)
  (Circuit.consAx .input2 .input0 .input1 (Circuit.nips 10)))
def leaf1 : Circuit := Circuit.leaf 1 .input0 .input1 .zero .zero
def leaf2 : Circuit := Circuit.leaf 2 .input0 .input1 .input2 .zero
def leaf3 : Circuit := Circuit.leaf 3 .input0 .input1 .input2 .zero
def leaf4 : Circuit := Circuit.leaf 4 .input0 .input1 .input2 .zero
def leaf5 : Circuit := Circuit.leaf 5 .input0 .input1 .input2 .zero
def leaf6 : Circuit := Circuit.leaf 6 .input0 .zero .input1 .zero
def leaf7 : Circuit := Circuit.leaf 7 .input0 .input1 .input2 .zero

section Graph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_genCircuit (i p z w : V) : genCircuit.eval i p z w=genBlockWord i p := by
  simp only [genCircuit,Circuit.eval,Circuit.eval_consDrop,Circuit.eval_consNip,
    Circuit.eval_consAx,Circuit.eval_nips,Circuit.eval_terminator,genBlockWord,genTail]
theorem eval_bundleCircuit (a b c u : V) : bundleCircuit.eval a b c u=bundleWord a b c := by
  simp only [bundleCircuit,Circuit.eval,Circuit.eval_discard,Circuit.eval_consAx,
    Circuit.eval_nips,bundleWord]

noncomputable def rowValue (tag payload u v : V) : V := by
  classical
  let a := first payload
  let t := second payload
  let b := first t
  let c := second t
  exact if tag=0 then Circuit.discard.eval 0 0 0 0
    else if tag=1 then (mpCircuit .input0 .input1 .input2).eval a u v 0
    else if tag=2 then genCircuit.eval a u 0 0
    else if tag=3 then leaf1.eval a t 0 0
    else if tag=4 then leaf2.eval a b c 0
    else if tag=5 then leaf3.eval a b c 0
    else if tag=6 then leaf4.eval a b c 0
    else if tag=7 then leaf5.eval a b c 0
    else if tag=8 then leaf6.eval a t 0 0
    else if tag=9 then leaf7.eval a b c 0
    else if tag=10 then rho8Circuit.eval a b (first c) (second c)
    else if tag=11 then bundleCircuit.eval a b c 0
    else 0

/-- Inputs u/v are earlier words; rejected data still has a defined row. -/
noncomputable def rowDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out tag payload u v.
    ∃ a, !ArithmeticCantor.firstDef a payload ∧
    ∃ t, !ArithmeticCantor.secondDef t payload ∧
    ∃ b, !ArithmeticCantor.firstDef b t ∧
    ∃ c, !ArithmeticCantor.secondDef c t ∧
    ∃ x, !ArithmeticCantor.firstDef x c ∧
    ∃ y, !ArithmeticCantor.secondDef y c ∧
    ((tag = 0 ∧ !(Circuit.discard.graph) out 0 0 0 0) ∨
     (tag = 1 ∧ !((mpCircuit .input0 .input1 .input2).graph) out a u v 0) ∨
     (tag = 2 ∧ !(genCircuit.graph) out a u 0 0) ∨
     (tag = 3 ∧ !(leaf1.graph) out a t 0 0) ∨
     (tag = 4 ∧ !(leaf2.graph) out a b c 0) ∨
     (tag = 5 ∧ !(leaf3.graph) out a b c 0) ∨
     (tag = 6 ∧ !(leaf4.graph) out a b c 0) ∨
     (tag = 7 ∧ !(leaf5.graph) out a b c 0) ∨
     (tag = 8 ∧ !(leaf6.graph) out a t 0 0) ∨
     (tag = 9 ∧ !(leaf7.graph) out a b c 0) ∨
     (tag = 10 ∧ !(rho8Circuit.graph) out a b x y) ∨
     (tag = 11 ∧ !(bundleCircuit.graph) out a b c 0) ∨
     ((tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3 ∧ tag ≠ 4 ∧ tag ≠ 5 ∧
       tag ≠ 6 ∧ tag ≠ 7 ∧ tag ≠ 8 ∧ tag ≠ 9 ∧ tag ≠ 10 ∧ tag ≠ 11) ∧ out = 0))”

instance row_defined : 𝚺₁-Function₄[V] rowValue via rowDef := .mk fun e => by
  classical
  simp [rowDef,numeral_eq_natCast]
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

noncomputable def rowDeltaDef : 𝚫₁.Semisentence 5 := rowDef.graphDelta
instance row_defined_delta : 𝚫₁-Function₄[V] rowValue via rowDeltaDef := row_defined.graph_delta

theorem row_total (tag payload u v : V) :
    ∃! out, rowDef.val.Evalb ![out,tag,payload,u,v] := by simp
end Graph

section Correctness
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticRow254 (MPGate mpValue genValue)

/-- Only accepted rows consume child contracts; GEN uses its whole-tail
child, and MP retains all saved-stack inputs. -/
theorem row_contract (tag payload u v p q : V)
    (hp : u≠0 → Contract p (u-1)) (hq : v≠0 → Contract q (v-1))
    (hr : ArithmeticRow222.rowKernel tag payload u v≠0) :
    Contract (rowValue tag payload p q) (ArithmeticRow222.rowKernel tag payload u v-1) := by
  classical
  by_cases h0 : tag=0
  · subst tag
    by_cases he : payload=0
    · simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
        Circuit.eval_discard,he] using (truth_contract (V := V))
    · exact False.elim (hr (by simp [ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,he]))
  by_cases h1 : tag=1
  · subst tag
    have hg : MPGate (first payload) u v := by
      by_contra hn
      exact hr (by simp [ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,mpValue,hn])
    have hg' := hg
    rcases hg' with ⟨x,_,m,_,hu,hv,hm⟩
    have hun : u≠0 := by rw [hu]; simp
    have hvn : v≠0 := by rw [hv]; simp
    have hux : u-1=x := by rw [hu]; simp
    have hvm : v-1=wim x (first payload) := by rw [hv]; simpa using hm
    have hc := mp_contract (hux ▸ hp hun) (hvm ▸ hq hvn)
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      eval_mpCircuit,Circuit.eval,mpValue,hg] using hc
  by_cases h2 : tag=2
  · subst tag
    have hun : u≠0 := by
      intro hz
      exact hr (by simp [ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,genValue,hz])
    have hc := gen_contract (first payload) (hp hun)
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      eval_genCircuit,genValue,hun] using hc
  by_cases h3 : tag=3
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      leaf1,Circuit.eval_leaf,Circuit.eval] using (ArithmeticCommandLeafPerm222.leaf1 (first payload) (second payload))
  by_cases h4 : tag=4
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      leaf2,Circuit.eval_leaf,Circuit.eval] using (ArithmeticCommandLeafPerm222.leaf2 (first payload) (first (second payload)) (second (second payload)))
  by_cases h5 : tag=5
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      leaf3,Circuit.eval_leaf,Circuit.eval] using (ArithmeticCommandLeafPerm222.leaf3 (first payload) (first (second payload)) (second (second payload)))
  by_cases h6 : tag=6
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      leaf4,Circuit.eval_leaf,Circuit.eval] using (ArithmeticCommandLeafPerm222.leaf4 (first payload) (first (second payload)) (second (second payload)))
  by_cases h7 : tag=7
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      leaf5,Circuit.eval_leaf,Circuit.eval] using (ArithmeticCommandLeafPerm222.leaf5 (first payload) (first (second payload)) (second (second payload)))
  by_cases h8 : tag=8
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      leaf6,Circuit.eval_leaf,Circuit.eval] using (ArithmeticCommandLeafPerm222.leaf6 (first payload) (second payload))
  by_cases h9 : tag=9
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
      leaf7,Circuit.eval_leaf,Circuit.eval] using (ArithmeticCommandLeafPerm222.leaf7 (first payload) (first (second payload)) (second (second payload)))
  by_cases h10 : tag=10
  · subst tag
    simpa [rowValue,ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel] using
      rho8_contract (first payload) (first (second payload))
        (first (second (second payload))) (second (second (second payload)))
  by_cases h11 : tag=11
  · subst tag
    have hg : second (second payload)≠first payload ∧
        second (second payload)≠first (second payload) := by
      by_contra hn
      exact hr (by simp [ArithmeticRow222.rowKernel,hn])
    simpa [rowValue,ArithmeticRow222.rowKernel,eval_bundleCircuit,hg] using
      bundle_contract (first payload) (first (second payload)) (second (second payload)) hg.1 hg.2
  exact False.elim (hr (by simp [ArithmeticRow222.rowKernel,ArithmeticRow254.rowKernel,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]))
end Correctness
end DiophantineConsistency.ArithmeticProofWordRowPerm222
