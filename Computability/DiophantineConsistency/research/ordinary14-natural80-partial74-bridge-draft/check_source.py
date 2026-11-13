#!/usr/bin/env python3
"""Check partial-coordinate source and finite controls, without Lean."""
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,sha):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);return b
s=pin(P/'Natural80Partial74.lean','942674c7951850ae30d457410cfc7a0359fc255831c31a87fc914a5ef3035c16').decode()
for x in ('theorem output_eval82','theorem composed_coordinates','theorem output_eval74',
          'theorem partial_embedding','theorem internalZero_iff_partial',
          'j = 0 ∨ j = 3 ∨ j = 8 ∨ j = 11 ∨ j = 12',
          '#print axioms DiophantineConsistency.Natural80Partial74Draft.output_eval74',
          '#print axioms DiophantineConsistency.Natural80Partial74Draft.internalZero_iff_partial'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
a=json.loads(pin(D/'research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'))
b=json.loads(pin(D/'research/ordinary14-root74-natural-forced82/candidate.json','1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'))
c=json.loads(pin(D/'research/ordinary14-positive-guard74/candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'))
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']==c['fixed_numerals']
rep={'J':'n_J','gamma':'n_gamma'}
assert all([n,'+','n_'+n,1] in b['source'] for n in rep)
assert a['source']==[[n,op,rep.get(x,x),rep.get(y,y)] for n,op,x,y in b['source'] if n not in rep]
def calc(g,v,mod):
 e=v.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%mod
 return e
rng=random.Random(148074);slots={0,3,8,11,12}
for mod in (4,17,1009):
 for _ in range(100):
  va={n:rng.randrange(-8,9) for n in a['witnesses']+a['fixed_numerals']}
  vb=va.copy();vb['n_J']-=1;vb['n_gamma']-=1
  vc={n:va['n_'+n]+(0 if i in slots else 1) for i,n in enumerate(c['witnesses'])}
  vc.update({n:va[n] for n in c['fixed_numerals']})
  ea,eb,ec=calc(a,va,mod),calc(b,vb,mod),calc(c,vc,mod)
  assert all(ea[n]==eb[n]==ec[n] for n in ('F0','F1','Fa','Fs','guard','out'))
print(json.dumps({'scope':'unelaborated source and finite ring controls only',
                  'unshifted_74_slots':sorted(slots),'signed_modular_controls':300,
                  'axiom_print_commands_not_executed':2,'no_model_ipra_or_byte_claim':True},sort_keys=True,indent=2))
