#!/usr/bin/env python3
"""Generate the literal integer 66-row expression and its model/iPRA client."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
GRAPH=HERE.parent/'current2011-unscaled66/polynomial.json'
raw=GRAPH.read_bytes()
if hashlib.sha256(raw).hexdigest()!='bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75':raise RuntimeError('graph hash')
g=json.loads(raw)
if len(g['source'])!=66 or g['fixed_numerals']!=['beta','K0','MC','MF']:raise RuntimeError('graph metadata')
code=['import DiophantineConsistency.ModelCarrierCurrent','',
 '/-! Literal 66-row integer graph and all-model/iPRA transfer. -/',
 'set_option autoImplicit false','set_option Elab.async false','noncomputable section',
 'namespace DiophantineConsistency.Current2011Unscaled66',
 'open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment',
 'open scoped LO.FirstOrder LO.FirstOrder.Arithmetic',
 'open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic',
 'open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation',
 '', 'def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=']
code += [f'  let {name} : Expr (Fin 14) := .var {i}' for i,name in enumerate(g['witnesses'])]
code += [f'  let {name} : Expr (Fin 14) := .constant (p {i})' for i,name in enumerate(g['fixed_numerals'])]
code += [f'  let {name} := {a} {op} {b}' for name,op,a,b in g['source']]
code += ['  polynomial','',
 'section Eval','variable {R : Type*} [CommRing R]','',
 'def unscaledValue (p : Fin 4 → R) (v : Fin 14 → R) : R :=',
 '  let d := Carrier65.core p v',
 '  d.P * d.Q * d.U * d.W * Carrier65.strong d - 1','',
 'theorem strong_factor (d i c : R) :',
 '    (i*i)*(d*(c*c))*(c*c) = d*((i*(c*c))*(i*(c*c))) := by ring','',
 'theorem aux_factor (d i c : R) :',
 '    d * (d*((i*(c*c))*(i*(c*c)))) = ((i*d)*(c*c))*((i*d)*(c*c)) := by ring','',
 'theorem evalRing_expressionAt (p : Fin 4 → ℤ) (v : Fin 14 → R) :',
 '    (expressionAt p).evalRing v = unscaledValue (fun j => (p j : R)) v := by',
 '  simp only [expressionAt, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,',
 '    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,',
 '    unscaledValue, Carrier65.strong, Carrier65.core, pow_succ, pow_zero, one_mul,',
 '    strong_factor, aux_factor]',
 '  simp only [mul_assoc]','',
 'theorem scaled_identity (p : Fin 4 → R) (v : Fin 14 → R) :',
 '    Carrier65.value p v = (Carrier65.core p v).delta * unscaledValue p v :=',
 '  Carrier65.scaled_identity p v','',
 'end Eval','',
 'section Model',
 'variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','',
 'theorem sameZero138 (v : Fin 14 → V) :',
 '    InternalZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) v ↔',
 '      InternalZero ObjectCurrentEquation2011.naturalExpression v := by',
 '  change InternalZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) v ↔',
 '    InternalZero (positiveShift ObjectCurrentEquation2011.expression) v',
 '  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,',
 '    evalRing_expressionAt, ObjectCurrentEquation2011.expression, ModelCarrierCurrent.evalRing_expressionAt65]',
 '  have hd := (ModelCarrierScaled.delta_pos model_discrete _ _',
 '    ModelCarrierCurrent.beta_pos (ModelCarrierCurrent.shifted_pos v)).ne\'',
 '  rw [scaled_identity, mul_eq_zero]',
 '  simp only [hd, false_or]','',
 'end Model','',
 'theorem bridge138 : HAExpressionAssembly.PolynomialBridge',
 '    (positiveShift (expressionAt CurrentWindowCarry2011.ports)) :=',
 '  HAExpressionSameZero.bridge _ _ (fun _ _ _ v => sameZero138 v) ModelCarrierCurrent.currentBridge','',
 'theorem native_equivalence138 : nativeTheory ⊢',
 '    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) 🡘',
 '      ∼mappedNativeRefutation embedding :=',
 '  IPRAExpressionNative.equivalence_of_bridge _ bridge138','',
 'theorem standard_equivalence138 : IPRAStandardTheory.standardTheory ⊢',
 '    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt CurrentWindowCarry2011.ports)) 🡘',
 '      ∼mappedNativeRefutation embedding :=',
 '  (IPRAStandardTheory.provable_iff _).2 native_equivalence138','',
 '#print axioms evalRing_expressionAt','#print axioms scaled_identity','#print axioms sameZero138',
 '#print axioms bridge138','#print axioms standard_equivalence138','',
 'end DiophantineConsistency.Current2011Unscaled66','']
out=HERE/'Current2011Unscaled66.lean'
if out.exists():raise RuntimeError('refusing to overwrite source')
out.write_text('\n'.join(code))
print(hashlib.sha256(out.read_bytes()).hexdigest())
