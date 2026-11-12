#!/usr/bin/env python3
"""Source, graph, and finite guard controls only; no Lean invocation."""
from pathlib import Path
import hashlib, json, random
P=Path(__file__).resolve().parent
D=P.parents[1]
def pin(path,sha):
    b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);return b
s=pin(P/'Natural81JShift.lean','f8e6436236c850e013ea9b9f9bbfe2ce48c45625a1d58ac1865e0413d96a5ca6').decode()
for x in ('theorem output_eval','theorem guard_zero_cut','theorem guard_at_most_negative_two',
          'theorem J_pos_of_zero','theorem internalZero_iff_related','theorem exists_zero_iff',
          '(hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)',
          'ModelDifferenceRing.one_le_of_pos'):
    assert x in s,x
assert 'sorry' not in s and 'admit' not in s
pin(D/'research/ordinary14-natural-forcedj81-lean-draft/P81NaturalForcedJ.lean',
    '73fbd4a953a32c7c56a1e1b06f93c4da9aed950c8022f8988ac82c6c06353897')
pin(D/'research/ordinary14-natural-forced82-lean-draft/P82NaturalForced.lean',
    '4fd5635afea3327181cdce6d176103195a9d2698f40ab8c40e2ea5c9a9b1fb84')
a=json.loads(pin(D/'research/ordinary14-natural-forcedj81/candidate.json',
                 '24d0c9f0f7d0078f268b27f6d3a0698952fbc0b13c4d28b4e5f9152dc4a41999'))
b=json.loads(pin(D/'research/ordinary14-root74-natural-forced82/candidate.json',
                 '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a'))
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
assert ['J','+','n_J',1] in b['source']
assert a['source']==[[n,op,'n_J' if x=='J' else x,'n_J' if y=='J' else y]
                      for n,op,x,y in b['source'] if n!='J']
def calc(g, v):
    e=v.copy()
    for n,op,x,y in g['source']:
        x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
        e[n]=x+y if op=='+' else x-y if op=='-' else x*y
    return e
rng=random.Random(148182)
for _ in range(200):
    v={x:rng.randrange(-3,4) for x in a['witnesses']+a['fixed_numerals']}
    w=v.copy();w['n_J']-=1
    aa,bb=calc(a,v),calc(b,w)
    assert all(aa[n]==bb[n] for n in ('F0','F1','Fa','Fs','guard','out'))
for _ in range(200):
    v={x:rng.randrange(0,5) for x in a['witnesses']}
    v.update({x:rng.randrange(-3,4) for x in a['fixed_numerals']})
    v['n_J']=0;v['K0']=rng.randrange(1,5)
    e=calc(a,v)
    assert e['guard']==-(v['n_F']+v['n_alpha']+1)*(v['n_w']+1+v['K0'])-v['n_F']
    assert e['guard']<=-2 and e['out']!=0
print(json.dumps({'scope':'source and finite graph controls only; no Lean/model theorem',
                  'signed_jshift_controls':200,'positive_k0_guard_controls':200,
                  'strict_represented_k0_hypothesis_explicit':True},sort_keys=True,indent=2))
