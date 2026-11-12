#!/usr/bin/env python3
"""Inspect guard-gap source and finite controls without invoking Lean."""
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,sha):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);return b
s=pin(P/'Natural80GuardGap.lean','df59908f11990a28b4b788d0014757a897f2bdc1a4011772e0e825397cad43eb').decode()
for x in ('theorem gap_of_80_zero','(hbeta : (p 0 : DiffRing V)=ι beta)',
          '(hK : (p 1 : DiffRing V)=ι K)','(hb : 0<beta) (hKpos : 0<K)',
          'Natural80JPosDraft.J_pos_of_zero','internalZero_iff_partial p v',
          'guard_factor_one','guard_eval','#print axioms DiophantineConsistency.Natural80GuardGapDraft.gap_of_80_zero'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
g=json.loads(pin(D/'research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'))
pin(D/'research/ordinary14-74-ownzero-units-draft/OwnZeroUnits74.lean','668fb089dad1ced2867530cb7f95919eb584d49f4aa953903a7e2b6d526de43c')
def calc(v):
 e=v.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
rng=random.Random(148081)
for _ in range(500):
 v={n:rng.randrange(0,5) for n in g['witnesses']}
 v.update({'beta':rng.randrange(1,5),'K0':rng.randrange(1,5),'MC':rng.randrange(-3,4),'MF':rng.randrange(-3,4)})
 v['n_J']=rng.randrange(1,5);e=calc(v)
 if e['guard']==1:
  assert v['n_F']+1+v['n_alpha']+1<e['q']
positive=0
for beta in range(2,10):
 for K0 in range(1,10):
  v={n:0 for n in g['witnesses']}
  w=(1-K0)%beta or beta;q=beta+1
  v.update({'n_J':1,'n_F':0,'n_alpha':beta-2,'n_w':w-1,
            'n_h':(q*w+K0-1)//beta,'beta':beta,'K0':K0,'MC':0,'MF':0})
  e=calc(v);assert e['guard']==1 and v['n_F']+v['n_alpha']+2<e['q']
  positive+=1
print(json.dumps({'scope':'unelaborated source and finite guard controls only',
                  'represented_positive_beta_and_K0_explicit':True,
                  'no_gamma_positivity_premise':True,'finite_controls':500,
                  'constructed_guard_unit_controls':positive,
                  'axiom_print_not_executed':True},sort_keys=True,indent=2))
