#!/usr/bin/env python3
"""Check source assumptions and graph gamma shift without invoking Lean."""
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
s=pin(P/'Natural80GammaShift.lean','150871559ad8be8ac689135c8021b8e488af138e68f929b878632d13d99c216a').decode()
for x in ('theorem output_eval','theorem internalZero_iff_related','theorem exists_zero_iff',
          'gamma_pos_of_80_zero','simpa [w,add_comm] using hg','(hbeta : (p 0 : DiffRing V)=ι beta)',
          '(hK : (p 1 : DiffRing V)=ι K)','(hMC : (p 2 : DiffRing V)=ι MC)',
          '(hMF : (p 3 : DiffRing V)=ι MF)','(hMCbound : MC<beta) (hMFbound : MF<2*beta)',
          '#print axioms DiophantineConsistency.Natural80GammaShiftDraft.output_eval',
          '#print axioms DiophantineConsistency.Natural80GammaShiftDraft.internalZero_iff_related',
          '#print axioms DiophantineConsistency.Natural80GammaShiftDraft.exists_zero_iff'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
pin(D/'research/ordinary14-natural80-gamma-client-draft/Natural80GammaClient.lean','7fca431907062c8578970ae7840f37d3710f09f49c0e1e4a784ba7a94cb8288b')
a=json.loads(pin(D/'research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'))
b=json.loads(pin(D/'research/ordinary14-natural-forcedj81/candidate.json','24d0c9f0f7d0078f268b27f6d3a0698952fbc0b13c4d28b4e5f9152dc4a41999'))
assert ['gamma','+','n_gamma',1] in b['source']
assert a['source']==[[n,op,'n_gamma' if x=='gamma' else x,'n_gamma' if y=='gamma' else y]
                      for n,op,x,y in b['source'] if n!='gamma']
def calc(g,v,mod):
 e=v.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%mod
 return e
rng=random.Random(1480812)
for mod in (4,17,1009):
 for _ in range(100):
  v={n:rng.randrange(-5,6) for n in a['witnesses']+a['fixed_numerals']}
  w=v.copy();w['n_gamma']-=1
  x,y=calc(a,v,mod),calc(b,w,mod)
  assert all(x[n]==y[n] for n in ('F0','F1','Fa','Fs','guard','out'))
print(json.dumps({'scope':'unelaborated source and finite controls only',
                  'represented_four_ports_and_rank_bounds_explicit':True,
                  'signed_gamma_shift_controls':300,'axiom_prints_not_executed':3,
                  'no_model_ipra_or_byte_claim':True},sort_keys=True,indent=2))
