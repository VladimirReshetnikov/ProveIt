#!/usr/bin/env python3
"""Generate inert AQ34 natural literal/residual/bridge source; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
g=json.loads(pin(D/'research/adaptive-aq34-natural172-signed-cancel/candidate.json','2bc8d1be1d3e4ca72dd84255816bda819bd75423447c6799c3aa52b8583d8f23'))
old=pin(D/'Lean/DiophantineConsistency/AdaptiveAQ34Context.lean','2f581a4dcd732d0f4b5f1c2f39a183dba00d5f7cca37c725009dd505f98291cd')
pin(D/'Lean/DiophantineConsistency/AdaptiveAQ34Literal.lean','30e3a0e4bc8199bcb62d27bcc0cc6a73697027f9c0066d24cbaad340eb2df38b')
pin(D/'Lean/DiophantineConsistency/IPRAAQ34Native.lean','857f4eb24f59efabfb49b9e6ba038bc43d1ffd81af70b21827f4b68153f5a31d')
start=old.index('def residuals (p : Fin 4 → ℤ) : Fin 22 → Expr (Fin 2 ⊕ Fin 32) :=');end=old.index('\ndef sum (p : Fin 4 → ℤ)',start)
x=re.findall(r'  !\[([^\n]+)\]',old[start:end]);assert len(x)==1;res=x[0].split(',');assert len(res)==22
assert len(g['witnesses'])==34 and len(g['source'])==g['operations']==172
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']];assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
L=['  let '+n+' : Expr (Fin 34) := .var '+str(i) for i,n in enumerate(g['witnesses'])]
L+=['  let '+n+' : Expr (Fin 34) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]
L+=['  let '+n+' := '+str(a)+' '+o+' '+str(b) for n,o,a,b in g['source']];body='\n'.join(L)
node={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
def v(x):return ('constant',x) if type(x)==int else node[x]
for n,o,a,b in g['source']:node[n]=(o,v(a),v(b))
total=None
for n in res:
 sq=('*',node[n],node[n]);total=sq if total is None else ('+',total,sq)
assert total==node[g['output']]
pre='''/-! Generated inert source; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
'''
lit='import DiophantineConsistency.AdaptiveAQ34Literal\n\n'+pre+'namespace DiophantineConsistency.AQ34Natural172LiteralDraft\nopen AdaptiveEquationSyntax2011\n\ndef literal (p : Fin 4 → ℤ) : Expr (Fin 34) :=\n'+body+'\n  '+g['output']+'\n\nend DiophantineConsistency.AQ34Natural172LiteralDraft\n'
(P/'AQ34Natural172Literal.lean.src').write_text(lit)
sumexpr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(22))
resfile='import AQ34Natural172Literal\n\n'+pre+'namespace DiophantineConsistency.AQ34Natural172ResidualsDraft\nopen AdaptiveEquationSyntax2011\n\ndef residuals (p : Fin 4 → ℤ) : Fin 22 → Expr (Fin 34) :=\n'+body+'\n  !['+','.join(res)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 34) := '+sumexpr+'''\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AQ34Natural172LiteralDraft.literal p := by rfl
end DiophantineConsistency.AQ34Natural172ResidualsDraft
#print axioms DiophantineConsistency.AQ34Natural172ResidualsDraft.sum_eq_literal
'''
(P/'AQ34Natural172Residuals.lean.src').write_text(resfile)
bridge='''import AQ34Natural172Residuals
import DiophantineConsistency.IPRAAQ34Native
import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ModelJonesSyntax
import Mathlib.Tactic.Ring

/-! Source-only proposed all-port evaluation identity and conditional endpoint.
The literal, residual proofs, sums, tactics and all axiom reports remain
unelaborated. The historical AQ34 endpoint retains its provider boundaries. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AQ34Natural172BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv
open ModelDifferenceRing PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

/-- The three canceled shifts all use this elementary ring identity. -/
theorem signed_shift_cancel {R : Type*} [CommRing R] (a b : R) :
    (a+1)-(b+1)=a-b := by ring

theorem w_cancel {R : Type*} [CommRing R] (v : Fin 34 → R) :
    (v 18+1)-(v 19+1)=v 18-v 19 := signed_shift_cancel _ _

theorem d_cancel {R : Type*} [CommRing R] (v : Fin 34 → R) :
    (v 23+1)-(v 24+1)=v 23-v 24 := signed_shift_cancel _ _

theorem v_cancel {R : Type*} [CommRing R] (v : Fin 34 → R) :
    (v 25+1)-(v 26+1)=v 25-v 26 := signed_shift_cancel _ _

'''
for j,n in enumerate(res):
 bridge+=f'''/-- Candidate residual {j}: {n}. -/
theorem residual{j:02d} {{R : Type*}} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 34 → R) :
    (AQ34Natural172ResidualsDraft.residuals p {j}).evalRing v =
      (AdaptiveAQ34Context.residuals p {j}).evalRing
        (fun k => (AdaptiveAQ34Context.newFill k).evalRing (fun i => v i+1)) := by
  simp [AQ34Natural172ResidualsDraft.residuals, AdaptiveAQ34Context.residuals,
    AdaptiveAQ34Context.newFill, AdaptiveAQ34Context.newRest, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, signed_shift_cancel] <;> ring

'''
bridge+='''/-- Proposed exact polynomial evaluation at arbitrary integer ports and in
any commutative ring. This proof is not yet checked. -/
theorem evaluation_identity_candidate {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 34 → R) :
    (AQ34Natural172LiteralDraft.literal p).evalRing v =
      (positiveShift (AdaptiveAQ34Literal.literal p)).evalRing v := by
  rw [positiveShift, ModelJonesSyntax.evalRing_subst]
  simp only [Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, Int.cast_one]
  rw [← AdaptiveAQ34Literal.new_literal, ModelJonesSyntax.evalRing_subst,
    ← AQ34Natural172ResidualsDraft.sum_eq_literal]
  simp only [AQ34Natural172ResidualsDraft.sum, AdaptiveAQ34Context.sum,
    Expr.evalRing_add, Expr.evalRing_mul]
'''
for j in range(22):bridge+=f'  have h{j:02d} := residual{j:02d} p v\n'
bridge+='  simp only ['+', '.join(f'h{j:02d}' for j in range(22))+']\n\n'
bridge+='''/-- Exact all-ring source statement required by the endpoint clients. -/
def EvaluationIdentity : Prop :=
  ∀ (R : Type) [CommRing R] (p : Fin 4 → ℤ) (v : Fin 34 → R),
    (AQ34Natural172LiteralDraft.literal p).evalRing v =
      (positiveShift (AdaptiveAQ34Literal.literal p)).evalRing v

theorem evaluationIdentity_candidate : EvaluationIdentity := by
  intro R _ p v
  exact evaluation_identity_candidate p v

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem internalZero_iff (h : EvaluationIdentity) (p : Fin 4 → ℤ) (v : Fin 34 → V) :
    InternalZero (AQ34Natural172LiteralDraft.literal p) v ↔
      InternalZero (positiveShift (AdaptiveAQ34Literal.literal p)) v := by
  rw [ModelDifferenceRing.internalZero_iff, ModelDifferenceRing.internalZero_iff,
    h (DiffRing V) p (fun i => ι (v i))]

def expression : Expr (Fin 34) :=
  AQ34Natural172LiteralDraft.literal CurrentWindowCarry2011.ports

theorem sameNoZero (h : EvaluationIdentity) :
    SameNoZero expression IPRAAQ34Native.literalNatural := by
  intro V _ _
  apply forall_congr'
  intro v
  exact not_congr (internalZero_iff h CurrentWindowCarry2011.ports v)

theorem polynomialBridge (h : EvaluationIdentity) : PolynomialBridge expression :=
  HAExpressionNoZeroEquiv.bridge expression IPRAAQ34Native.literalNatural
    (sameNoZero h) IPRAAQ34Native.bridge34

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

end DiophantineConsistency.AQ34Natural172BridgeDraft
#print axioms DiophantineConsistency.AQ34Natural172BridgeDraft.signed_shift_cancel
#print axioms DiophantineConsistency.AQ34Natural172BridgeDraft.evaluation_identity_candidate
#print axioms DiophantineConsistency.AQ34Natural172BridgeDraft.evaluationIdentity_candidate
#print axioms DiophantineConsistency.AQ34Natural172BridgeDraft.native_equivalence
#print axioms DiophantineConsistency.AQ34Natural172BridgeDraft.standard_equivalence
#print axioms DiophantineConsistency.AQ34Natural172BridgeDraft.reference_equivalence
'''
(P/'AQ34Natural172Bridge.lean.src').write_text(bridge)
print(json.dumps({'scope':'generated inert AQ34 natural literal, residual and evaluation source; no Lean','rows':len(g['source']),'variables':len(g['witnesses']),'residuals':len(res),'child_sum_exact_DAG':True,'source_hashes':{n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ('AQ34Natural172Literal.lean.src','AQ34Natural172Residuals.lean.src','AQ34Natural172Bridge.lean.src')}},indent=2,sort_keys=True))
