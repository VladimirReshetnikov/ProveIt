#!/usr/bin/env python3
"""Exact residual/cut algebra plus static evaluation and endpoint audit."""
from pathlib import Path
import collections,hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
base='research/adaptive-aq17-forced105-extraction-draft/'
s=pin(base+'AQ17Forced105CutExtraction.lean.src','3aaac2765bebc24bc0c3e08b5a66b704b97183d1fdb981ccf81288bf8e40bc05')
e=pin(base+'AQ17Forced105Evaluation.lean.src','6a20d07dd4bf6b2e8f561663260c783e57185107a772baabbbc3fa3295c7f447')
t=pin(base+'AQ17Forced105Endpoint.lean.src','7395fb0cd9111653070bf55382627df8ccd66c6f8d41148aab47ff056b1ee613')
pin(base+'receipt.json','8a942628a32c75475de69b1134fbc592f81b1b63fddfbb0d07bb52e8ec32b698')
pin('reviews/adaptive-aq17-forced105-model-independent/result.json','c1dfec6f8f0c258e6acbe108fd5ea4a1d7fb27c336185a8c7217f8912b549ad3')
g=json.loads(pin('research/adaptive-aq17-natural-forced105/candidate.json','ff131760c176ebd56a593aff49523daf384c03322e2ddaae07f65f8f63bb7bac'))
assert [g['witnesses'][i] for i in (3,4,5,6,7,9,10,11,13,14,15,16)]==['n_f','n_i','n_T','n_X','n_Y','n_eta','n_zeta','n_y','n_rankVariable','n_firstQuotient','n_mainQuotient','n_vValueVariable']
for i in range(8):
 m=re.search(r'(?ms)^theorem relation%02d\b(.*?)(?=^theorem )'%i,e);assert m
 assert f'AQ17Forced105ResidualsDraft.residuals p {i})' in m.group(1) and f'AQ17Factored94ResidualsDraft.residuals p {i})' in m.group(1)
 assert f'relation{i:02d} p v' in e.split('theorem evaluation ',1)[1]
for x in ['.mp (hr 0)','.mp (hr 1)','.mp (hr 2)','.mp (hr 3)','.mp (hr 7)','4≤qnat v','ι (v 13+1)','linear_combination haux - ((ι (v 11))*(ι (v 11))-(ι (v 16))*(ι (v 16)))*hstrong','theorem forcingCutExtraction : ForcingCutExtraction']:assert x in s,x
for x in ['(h22 : AQ22Quotient110ConditionalTransferDraft.GraphZeroObligations)','(h20 : AQ20Substituted104ConditionalTransferDraft.GraphZeroObligations)','(h17 : AQ17Factored94ConditionalTransferDraft.GraphZeroObligations)','AQ17Forced105EvaluationDraft.zeroEquivalence','sixForced_of_cut AQ17Forced105CutExtractionDraft.forcingCutExtraction']:assert x in t,x
# Sparse free-ring computations, deliberately excluding the complete output.
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
targets={'A0','A1','auxResidual','g72','vDifference'};rows={x[0]:x for x in g['source']};need=set(targets);todo=list(targets)
while todo:
 for x in rows.get(todo.pop(),[None,None,None,None])[2:]:
  if isinstance(x,str) and x not in need:need.add(x);todo.append(x)
env={x:atom(x) for x in g['witnesses']+g['fixed_numerals']}
for n,op,x,y in g['source']:
 if n not in need:continue
 x=env[x] if isinstance(x,str) else ({():x} if x else {})
 y=env[y] if isinstance(y,str) else ({():y} if y else {})
 env[n]=mul(x,y) if op=='*' else add(x,y,-1 if op=='-' else 1)
one={():1};A=lambda name:atom('n_'+name);shift=lambda name:add(A(name),one)
k=add(shift('eta'),shift('zeta'));c=add(shift('eta'),mul(shift('Y'),k));av=add(mul(shift('X'),shift('Y')),shift('Y'))
delta=add(add({():3},mul({():4},av)),mul(av,av));ell=mul(mul(shift('X'),shift('Y')),mul(shift('Y'),k));I=mul(mul(c,c),shift('i'));q=mul(I,I)
Q=mul(delta,add(mul(A('f'),A('f')),one,-1));y2=mul(A('y'),A('y'));z2=mul(A('vValueVariable'),A('vValueVariable'))
assert env['A0']==add(mul(A('firstQuotient'),A('firstQuotient')),add(one,mul(ell,add(ell,k))),-1)
assert env['A1']==add(mul(A('mainQuotient'),A('mainQuotient')),add(one,mul(delta,mul(c,c))),-1)
assert env['g72']==add(q,Q,-1)
assert env['auxResidual']==add(add(y2,mul(Q,add(y2,z2,-1)),-1),one,-1)
assert add(env['auxResidual'],mul(add(y2,z2,-1),env['g72']),-1)==add(add(y2,mul(q,z2)),add(one,mul(q,y2)),-1)
timeexpr=add(mul(mul(A('f'),A('f')),add(mul(A('T'),c),shift('rankVariable'),-1)),c,-1)
assert env['vDifference']==add(A('vValueVariable'),timeexpr,-1)
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',s+e+t)
print(json.dumps({'scope':'source and exact free-ring cut validation; no Lean','evaluation_residual_relations':8,'norm_strong_aux_time_residuals_checked':5,'auxiliary_linear_combination_sign_verified':True,'time_rank_shift_verified':True,'q_bound_mathematical_argument':'c>=2, I>=2, q=I²>=4','inherited_graph_obligation_premises':3},sort_keys=True,indent=2))
