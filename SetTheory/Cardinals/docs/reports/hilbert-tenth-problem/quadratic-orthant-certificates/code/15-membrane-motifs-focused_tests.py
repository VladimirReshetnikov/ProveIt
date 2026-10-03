from motif_compiler import *
import json
from pathlib import Path
stats={}
r=[Rule('divide','h',0,(1,),(1,),elementary=True)]
p=Plan('skin',(0,),(Plan('h',(1,),(Plan('h',(1,),mode=0),)),))
q=make_packet(p,r);fs,_,_=expanded_oracle(p,r)
assert len(fs[0].children)==1 and len(fs[0].children[0].children)==2
stats['elementary_nonleaf_guard']=True
re=[Rule('evolve','h',0,(0,1)),Rule('evolve','h',1,(1,0))]
p1=Plan('skin',(0,0),(Plan('h',(2,0),evolution=((0,1),(1,0),(0,1))),))
p2=Plan('skin',(0,0),(Plan('h',(2,0),evolution=((0,2),)),))
assert pkey(p1)==pkey(p2)
assert make_packet(p1,re)==make_packet(p2,re)
stats['evolution_count_normalization']=True
s=q['schema'].copy();s['configs']=s['configs']+[{'label':'orphan','children':[]}]
try:compile_schema(s,r,1);raise AssertionError('accepted orphan config')
except ValueError as e:assert str(e)=='orphan configuration'
stats['orphan_config_rejected']=True
r=[Rule('evolve','h',0,(2,0,0,0)),Rule('evolve','h',2,(0,1,0,0)),Rule('evolve','h',3,(1,1,0,0)),Rule('divide','h',1,(0,0,1,0),(0,0,0,1))]
leaves=[Cfg('h',(0,1,0,0))]
for t in range(1,9):
    children=tuple(Plan('h',c.x,evolution=((0,c.x[0]),) if c.x[0] else (),mode=3) for c in leaves)
    p=Plan('skin',(0,0,0,0),children);fs,_,_=expanded_oracle(p,r)
    children=tuple(Plan('h',c.x,evolution=tuple((ri,c.x[r[ri].a]) for ri in (0,1,2) if c.x[r[ri].a])) for c in fs[0].children)
    p=Plan('skin',(0,0,0,0),children);fs,_,_=expanded_oracle(p,r);leaves=list(fs[0].children)
    expected={sum(bit*4**i for i,bit in enumerate(bits)) for bits in product((0,1),repeat=t)}
    assert len(leaves)==2**t and {c.x[0] for c in leaves}==expected
    assert all(c.x[1:]==(1,0,0) for c in leaves)
stats['deterministic_rounds']=8;stats['distinct_motifs']=len(leaves)
# Exact generic ledger checked against every saved detailed example.
examples=json.loads((Path(__file__).parent/'examples.json').read_text())
packets=[x for x in examples.values() if isinstance(x,dict) and 'witness' in x]
packets+=list(examples['same_mass_different_successor'].values())
for p in packets:
    cs=p['schema']['configs'];ts=p['schema']['transitions'];K=len(cs);J=len(ts)
    w=p['witness'];d=sum(n.startswith('x:0:') for n in w)
    A=sum(len(c['children']) for c in cs);E=sum(len(t['children']) for t in ts);B=sum(n.startswith('e:') for n in w);L=sum(len(t['targets']) for t in ts)
    V=d*K+A+E+B+3*d*J+K*J
    assert V==p['ledger']['variables']
stats['variable_ledgers_checked']=len(packets)
(Path(__file__).parent/'focused_receipt.json').write_text(json.dumps(stats,indent=2)+'\n')
print(json.dumps(stats,indent=2))
