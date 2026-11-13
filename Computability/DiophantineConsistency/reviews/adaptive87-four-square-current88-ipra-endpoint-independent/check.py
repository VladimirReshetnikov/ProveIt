#!/usr/bin/env python3
"""Independent, bounded textual source-interface review; no Lean/providers."""
import hashlib,json,resource,subprocess,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent
sha=lambda x:hashlib.sha256(x).hexdigest()
def require(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,digest in pins.items():require(sha((r/f).read_bytes())==digest,'pin '+f)
def read(f):return (r/f).read_text()
s=read('research/adaptive87-four-square-current88-ipra-endpoint-draft/AdaptiveFourSquare88IPRA.lean.src');m=read('research/adaptive87-four-square-current88-model-draft/FourSquare88Model.lean.src');p=read('Lean/DiophantineConsistency/HAAdaptiveFactor87.lean');nat=read('Lean/DiophantineConsistency/IPRAExpressionNative.lean');std=read('Lean/DiophantineConsistency/IPRAStandardTheory.lean');z=read('Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean')
for token in ['def naturalExpression : Expr (Fin 13) := positiveShift (expressionAt CurrentWindowCarry2011.ports)','theorem bridge (hp : PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87)','PolynomialBridge naturalExpression := HAExpressionSameZero.bridge _ _ sameZero hp']:
 require(token in m,'model '+token)
require('PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87' in p,'actual parent')
for token in ['theorem bridge88 : PolynomialBridge naturalExpression :=\n  AdaptiveFourSquare88ModelDraft.bridge HAAdaptiveFactor87.polynomialBridge','IPRAExpressionNative.equivalence_of_bridge naturalExpression bridge88','(IPRAStandardTheory.provable_iff _).2 native_equivalence88','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:
 require(token in s,'endpoint '+token)
require('nativeTheory ⊢ nativeNoZero e 🡘 ∼mappedNativeRefutation embedding' in nat,'native endpoint')
require('standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in std,'standard direction')
require('(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in z,'translated orientation')
require('(Semiformula.lMap embedding sourceSentence)ᴺ' in s,'translated client')
q=subprocess.run([sys.executable,'-I','-S','-B','research/adaptive87-four-square-current88-ipra-endpoint-draft/check.py'],cwd=r,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=25,check=True)
require(q.stdout==(r/'research/adaptive87-four-square-current88-ipra-endpoint-draft/receipt.json').read_bytes(),'prior receipt')
print(json.dumps({'scope':'source interface and historical receipt checks only; Lean/provider/TeX/PDF not checked','pins_sha256':sha((d/'pins.json').read_bytes()),'parent_bridge_exact':True,'current_ports_and_positive_shift':True,'native_standard_and_gg_directions':True,'author_receipt_reproduced':True},sort_keys=True,indent=2))
