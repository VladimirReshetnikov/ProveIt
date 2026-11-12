#!/usr/bin/env python3
"""Generate inert natural-164 literal and all-ring proof proposal; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
parent=json.loads(pin(D/'research/adaptive-square-sums33/candidate.json','a7934aac8f72dc632ebc86f15fa4300106b6af2e6ab5cd73e94f8bdd4c11e735'))
child=json.loads(pin(D/'research/adaptive-named33-natural164-signed-cancel/candidate.json','b42bb4501265b3dfac592b74d0950b79c322064d3febe38aeec56e741112e121'))
oldsrc=pin(D/'Lean/DiophantineConsistency/AdaptiveNamedValues33.lean','0c6bde076f2cc77e2d4d08f7542abb6bf469b6062e0ab7d1276250da1b06abbb')
pin(D/'Lean/DiophantineConsistency/IPRANamedValues33Native.lean','c6c072f16c436d8e4608753684f1afceda523b2789c33ff4c192e5fdb624f8ce')
res=['A0','A1','auxResidual','g72','squareDifference','scaleDifference','mainScaleDifference','rankDifference','cDifference','aDifference','ellDifference','wDifference','cubeDifference','productDifference','fSquareDifference','cSquareDifference','zDifference','dDifference','vDifference','deltaDifference']
assert len(parent['source'])==139 and len(child['source'])==164 and len(res)==20 and len(child['witnesses'])==len(parent['witnesses'])==33
# Both literal sums are exactly left-associated sums of the listed squares.
for g in (parent,child):
 env={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
 def v(x):return ('constant',x) if type(x)==int else env[x]
 for n,o,a,b in g['source']:env[n]=(o,v(a),v(b))
 total=None
 for n in res:
  z=('*',env[n],env[n]);total=z if total is None else ('+',total,z)
 assert total==env[g['output']]
start=oldsrc.index('def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n');end=oldsrc.index('\ndef embed ',start)
expected=['def literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=']+[f'  let {n} : Expr (Fin 33) := .var ({i})' for i,n in enumerate(parent['witnesses'])]+[f'  let {n} : Expr (Fin 33) := .constant (p {i})' for i,n in enumerate(parent['fixed_numerals'])]+[f'  let {n} := {a} {o} {b}' for n,o,a,b in parent['source']]+['  '+parent['output']]
assert oldsrc[start:end].splitlines()==expected
def body(g):
 return '\n'.join(['  let '+n+' : Expr (Fin 33) := .var '+str(i) for i,n in enumerate(g['witnesses'])]+['  let '+n+' : Expr (Fin 33) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]+['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']])
pre='''/-! Generated inert source; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
'''
lit='import DiophantineConsistency.AdaptiveNamedValues33\n\n'+pre+'namespace DiophantineConsistency.Named33Natural164LiteralDraft\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 33) :=\n'+body(child)+'\n  '+child['output']+'\n\nend DiophantineConsistency.Named33Natural164LiteralDraft\n'
(P/'Named33Natural164Literal.lean.src').write_text(lit)
def residual_source(which,g,importName,litName):
 sumexpr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(20))
 return 'import '+importName+'\n\n'+pre+f'namespace DiophantineConsistency.Named33{which}ResidualsDraft\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 20 → Expr (Fin 33) :=\n'+body(g)+'\n  !['+','.join(res)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 33) := '+sumexpr+f'\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = {litName}.literal p := by rfl\nend DiophantineConsistency.Named33{which}ResidualsDraft\n#print axioms DiophantineConsistency.Named33{which}ResidualsDraft.sum_eq_literal\n'
for name,data in [('Parent',residual_source('Parent',parent,'DiophantineConsistency.AdaptiveNamedValues33','AdaptiveNamedValues33')),('Natural164',residual_source('Natural164',child,'Named33Natural164Literal','Named33Natural164LiteralDraft'))]:(P/f'Named33{name}Residuals.lean.src').write_text(data)
bridge='''import Named33ParentResiduals
import Named33Natural164Residuals
import DiophantineConsistency.IPRANamedValues33Native
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ModelJonesSyntax
import Mathlib.Tactic.Ring

/-! Source-only proposed all-port evaluation identity and conditional endpoint.
The literal, residual proofs, sums, tactics and all axiom reports remain
unelaborated. The historical matched endpoint retains its provider boundaries. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.Named33Natural164BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open ModelDifferenceRing PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem signed_shift_cancel {R : Type*} [CommRing R] (a b : R) :
    (a+1)-(b+1)=a-b := by ring

'''
for name,i,j in [('w',20,21),('z',26,27),('d',28,29),('v',30,31)]:bridge+=f'''theorem {name}_cancel {{R : Type*}} [CommRing R] (v : Fin 33 → R) :
    (v {i}+1)-(v {j}+1)=v {i}-v {j} := signed_shift_cancel _ _

'''
for j,n in enumerate(res):
 bridge+=f'''/-- Candidate residual {j}: {n}. -/
theorem residual{j:02d} {{R : Type*}} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 33 → R) :
    (Named33Natural164ResidualsDraft.residuals p {j}).evalRing v =
      (Named33ParentResidualsDraft.residuals p {j}).evalRing (fun i => v i+1) := by
  simp [Named33Natural164ResidualsDraft.residuals, Named33ParentResidualsDraft.residuals,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, signed_shift_cancel] <;> ring

'''
bridge+='''/-- Proposed all-port evaluation identity, as yet unchecked by Lean. -/
theorem evaluation_identity_candidate {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 33 → R) :
    (Named33Natural164LiteralDraft.literal p).evalRing v =
      (positiveShift (AdaptiveNamedValues33.literal p)).evalRing v := by
  rw [positiveShift, ModelJonesSyntax.evalRing_subst]
  simp only [Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one]
  rw [← Named33ParentResidualsDraft.sum_eq_literal,
    ← Named33Natural164ResidualsDraft.sum_eq_literal]
  simp only [Named33Natural164ResidualsDraft.sum, Named33ParentResidualsDraft.sum,
    Expr.evalRing_add, Expr.evalRing_mul]
'''
for j in range(20):bridge+=f'  have h{j:02d} := residual{j:02d} p v\n'
bridge+='  simp only ['+', '.join(f'h{j:02d}' for j in range(20))+']\n\n'
bridge+='''def EvaluationIdentity : Prop :=
  ∀ (R : Type) [CommRing R] (p : Fin 4 → ℤ) (v : Fin 33 → R),
    (Named33Natural164LiteralDraft.literal p).evalRing v =
      (positiveShift (AdaptiveNamedValues33.literal p)).evalRing v

theorem evaluationIdentity_candidate : EvaluationIdentity := by
  intro R _ p v
  exact evaluation_identity_candidate p v

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem internalZero_iff (h : EvaluationIdentity) (p : Fin 4 → ℤ) (v : Fin 33 → V) :
    InternalZero (Named33Natural164LiteralDraft.literal p) v ↔
      InternalZero (positiveShift (AdaptiveNamedValues33.literal p)) v := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    h (DiffRing V) p (fun i => ι (v i))]

def expression : Expr (Fin 33) :=
  Named33Natural164LiteralDraft.literal CurrentWindowCarry2011.ports

theorem sameNoZero (h : EvaluationIdentity) :
    SameNoZero expression IPRANamedValues33Native.literalNatural := by
  intro V _ _
  apply forall_congr'
  intro v
  exact not_congr (internalZero_iff h CurrentWindowCarry2011.ports v)

theorem polynomialBridge (h : EvaluationIdentity) : PolynomialBridge expression :=
  HAExpressionNoZeroEquiv.bridge expression IPRANamedValues33Native.literalNatural
    (sameNoZero h) IPRANamedValues33Native.bridge33

theorem native_equivalence (h : EvaluationIdentity) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge expression (polynomialBridge h)

theorem standard_equivalence (h : EvaluationIdentity) : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 (native_equivalence h)

theorem reference_equivalence (h : EvaluationIdentity) : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero expression) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference (native_equivalence h)

end DiophantineConsistency.Named33Natural164BridgeDraft
#print axioms DiophantineConsistency.Named33Natural164BridgeDraft.signed_shift_cancel
#print axioms DiophantineConsistency.Named33Natural164BridgeDraft.evaluation_identity_candidate
#print axioms DiophantineConsistency.Named33Natural164BridgeDraft.evaluationIdentity_candidate
#print axioms DiophantineConsistency.Named33Natural164BridgeDraft.native_equivalence
#print axioms DiophantineConsistency.Named33Natural164BridgeDraft.standard_equivalence
#print axioms DiophantineConsistency.Named33Natural164BridgeDraft.reference_equivalence
'''
(P/'Named33Natural164Bridge.lean.src').write_text(bridge)
outputs=['Named33Natural164Literal.lean.src','Named33Natural164Residuals.lean.src','Named33ParentResiduals.lean.src','Named33Natural164Bridge.lean.src']
print(json.dumps({'scope':'inert generated literal, residual and all-ring bridge source; no Lean','parent_rows':139,'child_rows':164,'residuals':20,'variables':33,'both_sum_exact_DAG':True,'source_hashes':{n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in outputs}},indent=2,sort_keys=True))
