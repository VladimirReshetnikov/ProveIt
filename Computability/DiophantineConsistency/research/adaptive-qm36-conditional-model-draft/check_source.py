#!/usr/bin/env python3
"""Read-only source maps and finite controls for QM36 drafts; no Lean."""
from pathlib import Path
import hashlib,json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
a=json.loads(pin(D/'research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'))
b=json.loads(pin(D/'research/adaptive-square-sums36-combined-shift-quartic/candidate.json','dfa54188a5457f6de2e6d232b2141f12e5f38406bea88e0a5f3f8a07def78523'))
c=json.loads(pin(D/'research/adaptive-square-sums36-factored-roots/candidate.json','92ec1caec949f4cad0cc3e021becfbbb04a971403a76b282d240addc58d58182'))
pin(P/'generate.py','200b449e64d48e0efdd9c8e3464f6544905035c06f6cf6d98066749f0eea6b48')
gen=json.loads(pin(P/'generated.json','c75ff24452f97bdd654ffcc082b3e7de6107657fa771021afd3a06a99d9f9a81'))
transfer=pin(P/'AdaptiveQM36ConditionalTransfer.lean.src','865a63bdcb03a5f7dc1845bc5af0217529b3d549e7a6e67b73f0f1cf447bc754')
slots=pin(P/'AdaptiveQM36ParentSlots.lean.src','69bf3f920031a0451740b04c48a68a3ee4edd5708aed84cf85066bf24a23ac78')
zeros=pin(P/'AdaptiveQM36ResidualZeros.lean.src','716de991c36f462e2a3d0e7e65f2909e2db66923abb185ccb9674a11275a426e')
oldres=pin(D/'research/adaptive-qm37-conditional-model-draft/AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
def vector(s):
 x=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(x)==1;return x[0].split(',')
rr=vector(oldres);assert len(rr)==28 and rr[11]=='productDifference' and rr[26]=='gammaProductDifference';wanted=[('combinedEquality' if i==11 else n) for i,n in enumerate(rr) if i!=26];assert len(wanted)==27
assert len(a['witnesses'])==37 and a['witnesses'][20]=='productVariable' and a['witnesses'][33]=='gammaProductVariable'
assert len(b['witnesses'])==36 and b['witnesses'][20]=='combinedShift' and b['witnesses']==c['witnesses']
assert b['witnesses']==[('combinedShift' if n=='productVariable' else n) for n in a['witnesses'] if n!='gammaProductVariable']
for suffix,g in [('155',b),('153',c)]:
 literal=pin(P/f'AdaptiveQM36Literal{suffix}.lean.src',gen['outputs'][f'AdaptiveQM36Literal{suffix}.lean.src']);res=pin(P/f'AdaptiveQM36Residuals{suffix}.lean.src',gen['outputs'][f'AdaptiveQM36Residuals{suffix}.lean.src'])
 assert len(g['source'])==int(suffix) and vector(res)==wanted
 for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 36) := .var {i}' in literal
 for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 36) := .constant (p {i})' in literal
 for n,o,x,y in g['source']:assert f'  let {n} := {x} {o} {y}\n' in literal
 assert f"  {g['output']}\n" in literal and 'theorem sum_eq_literal' in res
for s in ('((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V)=ι beta','theorem fixed_beta_representation','theorem extend_pos','(h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)','(h37 : AdaptiveQM37ConditionalTransferDraft.GraphZeroObligations)','(h36 : GraphZeroObligations)'):
 assert s in transfer
assert '0<beta' not in transfer and '.mp hz 11' in slots and '.mp hz 26' in slots and '∀ i : Fin 27' in zeros
maps=D/'research/adaptive-qm36-residual-maps-draft';mp=pin(maps/'AdaptiveQM36ResidualMaps.lean.src','7fbe29e233c55aa8a3da52ec62030e294d523d4cc820a3ea24195c6926b82432')
bridge=D/'research/adaptive-qm36-factorized-ring-bridge-draft';fb=pin(bridge/'AdaptiveQM36FactorizedRingBridge.lean.src','9a7d38b4dc75a13b2bc400214823ceb6d0607ce1c3ab4008d62626de55e912f7')
assert '((p 0 : ℤ) : DiffRing V)=ι beta' in mp and 'theorem graphZeroObligations' in mp
assert 'theorem evaluation_identity {R : Type*} [CommRing R]' in fb and fb.count('/-- Residual ')==27 and 'theorem native_equivalence' in fb
cert=json.loads(pin(D/'research/adaptive-square-sums36-factored-roots/result.json','b5688a298d31bcb1815bcfceb33ed2283ddfd397f71b6fc84984218e7182151a'));assert cert['complete_output_polynomial_identical'] and cert['all_27_residuals_identical']
# Finite modular controls: identity of 153 vs 155 at arbitrary signed ports;
# and 155→37 lift when beta is nonnegative and combined residual vanishes.
rng=random.Random(3615537);mod=1000000007
def evalg(g,vals,ports):
 e=dict(zip(g['witnesses'],vals));e.update(zip(g['fixed_numerals'],ports))
 for n,o,x,y in g['source']:
  x=e[x] if isinstance(x,str) else x;y=e[y] if isinstance(y,str) else y
  e[n]=(x+y if o=='+' else x-y if o=='-' else x*y)%mod
 return e[g['output']]
for _ in range(100):
 v=[rng.randrange(1,8) for _ in range(36)];ports=[rng.randrange(-4,5) for _ in range(4)]
 assert evalg(b,v,ports)==evalg(c,v,ports)
 beta=rng.randrange(0,6);ports[0]=beta;v[20]=v[28]*(1+v[0]*beta)+v[15]*v[12]
 lift=[]
 for i in range(37):
  if i==20:lift.append(v[28]*(1+v[0]*beta))
  elif i==33:lift.append(v[15]*v[12])
  elif i<33:lift.append(v[i])
  else:lift.append(v[i-1])
 projected=[lift[20]+lift[33] if i==20 else lift[i] if i<33 else lift[i+1] for i in range(36)]
 assert projected==v and all(x>0 for x in lift) and evalg(a,lift,ports)==evalg(b,v,ports)
print(json.dumps({'scope':'bounded source/coordinate transcription and finite controls; no Lean or model theorem','positive_graph_rows':[158,155,153],'variables':[37,36,36],'residuals':27,'finite_factorized_controls':100,'finite_represented_beta_lift_controls':100,'port_cast_premise_explicit':True,'beta_strict_positivity_assumed':False,'inherited_model_obligations_explicit':True},sort_keys=True,indent=2))
