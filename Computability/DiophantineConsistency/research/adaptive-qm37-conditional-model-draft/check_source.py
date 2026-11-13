#!/usr/bin/env python3
"""Read-only source/coordinate audit with finite controls; no Lean."""
from pathlib import Path
import ast,hashlib,json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
child=json.loads(pin(D/'research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'))
parent=json.loads(pin(D/'research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'))
pin(P/'generate.py','f74bd1def369bb41fcb76d0ffa3f6c0d9441d3f3652e87923ecb1797b3757456')
gen=json.loads(pin(P/'generated.json','6680395cb79c559e430245628c5286d79ebbd2236c4ff1e8cbd7667552a89794'))
literal=pin(P/'AdaptiveQM37Literal.lean.src','8309b2c0e951d878f60667098d374883eb802b96747b1e3849a46afb10599996')
res=pin(P/'AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
zeros38=pin(P/'AdaptiveQM38ResidualZeros.lean.src','48a7b7937f74ffb99855223f636de8d985d2856567c33b46e1777bd7774a4ae2')
zeros37=pin(P/'AdaptiveQM37ResidualZeros.lean.src','b0b656020f0f1fb34849d103ff283b45d48ca3fd7368a7d8e23bf5096780b1be')
diff=pin(P/'AdaptiveQM37DifferenceWitness.lean.src','b65647fb73619d6f52e166ae61233854a47e9f968174481f321f44bcdf915c80')
transfer=pin(P/'AdaptiveQM37ConditionalTransfer.lean.src','be810ba3342ba05423e42e70eceff065809ba0380b804b79060b17ae73415566')
oldres=pin(D/'research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38Residuals.lean.src','d0bb6ab27fbd9f70c5e4faf529a725ae065bf9787b570a8c675c38d21460fa97')
cert=json.loads(pin(D/'research/adaptive-square-sums37-difference-quartic/result.json','07ede5d8f22e400be9dd6ad478c8bc55281925d27edfd1e2b5f03bf41a7394be'))
assert len(child['witnesses'])==37 and len(parent['witnesses'])==38 and len(child['source'])==158
assert parent['witnesses'][13]=='squareVariable' and parent['witnesses'][30]=='ySquareVariable' and child['witnesses'][13]=='differencePlusOne'
assert child['witnesses']==[('differencePlusOne' if n=='squareVariable' else n) for n in parent['witnesses'] if n!='ySquareVariable']
for i,n in enumerate(child['witnesses']):assert f'let {n} : Expr (Fin 37) := .var {i}' in literal
for i,n in enumerate(child['fixed_numerals']):assert f'let {n} : Expr (Fin 37) := .constant (p {i})' in literal
for n,o,a,b in child['source']:assert f'  let {n} := {a} {o} {b}\n' in literal
assert f"  {child['output']}\n" in literal and gen['square_sum_exact_DAG']
def vec(t):
 x=re.findall(r'^  !\[([^\n]+)\]$',t,re.M);assert len(x)==1;return x[0].split(',')
a=vec(oldres);b=vec(res);assert len(a)==29 and len(b)==28 and a[4]=='squareDifference' and a[21]=='ySquareDifference' and b[4]=='differenceEquality'
assert b==[('differenceEquality' if i==4 else n) for i,n in enumerate(a) if i!=21]
assert 'h 4' in diff and 'h 21' in diff and '.mp hz 2' in diff and 'theorem difference_of_aux' in diff and 'theorem parent_difference' in diff
assert '∀ i : Fin 29' in zeros38 and '∀ i : Fin 28' in zeros37
assert '(hproject :' in transfer and '(hextend :' in transfer and 'AdaptiveQM37DifferenceWitnessDraft.parent_difference' in transfer
assert '(h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)' in transfer and '(h37 : GraphZeroObligations)' in transfer
assert cert['parent_aux_equals_child_aux_plus_Q_times_difference_residual']
# Sample exact lift/project behavior; the child difference is constructed
# nonnegative before adding one. These controls do not prove model claims.
rng=random.Random(3715838);M=1000000007
for _ in range(100):
 u=[rng.randrange(1,8) for _ in range(37)]; u[11]=rng.randrange(1,9);u[25]=rng.randrange(1,u[11]+1);d=u[11]*u[11]-u[25]*u[25];u[13]=d+1
 old=[]
 for i in range(38):
  if i==13:old.append(u[25]*u[25])
  elif i==30:old.append(u[11]*u[11])
  elif i<30:old.append(u[i])
  else:old.append(u[i-1])
 projected=[(d+1 if i==13 else old[i] if i<30 else old[i+1]) for i in range(37)]
 assert projected==u and all(x>0 for x in old)
 ports=[rng.randrange(-3,4) for _ in range(4)]
 def run(G,vals):
  e=dict(zip(G['witnesses'],vals));e.update(zip(G['fixed_numerals'],ports))
  for n,o,a,b in G['source']:
   a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
   e[n]=(a+b if o=='+' else a-b if o=='-' else a*b)%M
  return e[G['output']]
 assert run(parent,old)==run(child,u)
print(json.dumps({'scope':'source and finite arithmetic controls only; no Lean, all-model proof or endpoint','parent_variables':38,'child_variables':37,'child_rows':len(child['source']),'parent_residuals':len(a),'child_residuals':len(b),'finite_positive_lift_controls':100,'unproved_graph_and_prior_obligations_explicit':True},sort_keys=True,indent=2))
