#!/usr/bin/env python3
"""Check the source interface and finite guard controls without Lean."""
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,sha):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);return b
s=pin(P/'Natural80JPos.lean','6ac50565b28ac25581504ff28c1b4d6785c61607423d0bed7c22532d6ec8e221').decode()
for x in ('theorem guard_zero_cut','theorem guard_at_most_negative_two','theorem J_pos_of_zero',
          '(hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)',
          'ModelDifferenceRing.one_le_of_pos',
          '#print axioms DiophantineConsistency.Natural80JPosDraft.J_pos_of_zero'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
g=json.loads(pin(D/'research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'))
pin(D/'research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean','015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9')
def calc(v):
 e=v.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
rng=random.Random(148000)
for _ in range(300):
 v={n:rng.randrange(0,5) for n in g['witnesses']}
 v.update({n:rng.randrange(-3,4) for n in g['fixed_numerals']})
 v['n_J']=0;v['K0']=rng.randrange(1,5)
 e=calc(v)
 assert e['guard']==-(v['n_F']+v['n_alpha']+1)*(v['n_w']+1+v['K0'])-v['n_F']
 assert e['guard']<=-2 and e['out']!=0
print(json.dumps({'scope':'source and finite guard controls only; no model, Lean or iPRA theorem',
                  'controls':300,'represented_positive_K0_explicit':True,
                  'no_gamma_positivity_premise':True,'axiom_print_not_executed':True},sort_keys=True,indent=2))
