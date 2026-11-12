#!/usr/bin/env python3
"""Independent graph and finite-difference degree review; no Lean."""
import hashlib, json, math, zlib
from pathlib import Path

D=Path(__file__).resolve().parents[2]
CANDIDATE='ordinary14-natural-forcedj82-degree97'
PARENT='ordinary14-natural-shifted-pell83'
CANDIDATE_SHA='7d4ba963bda9c7acd7eb80fd96cd289809960e6c9de6e919f461ebd14ecea76f'
PARENT_SHA='36c910fe9a6c59eeab8bfd97583dae3c27d7680f848046ed84622d9d8dd45d19'
GATES=82
DEGREE=97
LEADER=979034495
RAY_COORD='n_t'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(path, digest):
    data=(D/path).read_bytes(); assert sha(data)==digest, path
    return json.loads(data)
c=load('research/'+CANDIDATE+'/candidate.json',CANDIDATE_SHA)
p=load('research/'+PARENT+'/candidate.json',PARENT_SHA)
assert c['domain']==p['domain']=='nonnegative integers'
assert c['witnesses']==p['witnesses'] and len(c['witnesses'])==14
assert c['fixed_numerals']==p['fixed_numerals']==['beta','K0','MC','MF']
old={r[0]:r[1:] for r in p['source']}
new={r[0]:r[1:] for r in c['source']}
assert len(old)==GATES+1 and len(new)==GATES
assert set(old)-set(new)=={'J'} and set(new)<=set(old)
assert old['J']==['+','n_J',1]
for name,row in new.items():
    op,x,y=old[name]
    assert row==[op,'n_J' if x=='J' else x,'n_J' if y=='J' else y]
# Check topology, every node and input/port is live, and the exact product and
# guard structure used in the unbounded J=0 argument.
seen=set(c['witnesses']+c['fixed_numerals'])
for n,op,x,y in c['source']:
    assert n not in seen and op in ('+','-','*')
    assert all(type(t) is int or t in seen for t in (x,y));seen.add(n)
live={c['output']}
for n,op,x,y in reversed(c['source']):
    if n in live:live.update(t for t in (x,y) if isinstance(t,str))
assert set(new)|set(c['witnesses'])|set(c['fixed_numerals'])<=live
shape={'alpha':['+','n_alpha',1],'w':['+','n_w',1], 'qm':['*','n_J','beta'],
 'q':['+',1,'qm'],'X':['*','q','w'],'qF':['-','qm','n_F'],'C':['-','qF','alpha'],
 'g26':['+','X','K0'],'g27':['*','C','g26'],'guard_base':['-','g27','n_F'],
 'bt_quotient':['*','qm','n_h'],'guard':['-','guard_base','bt_quotient'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],
 'P01234':['*','P0123','guard'],'out':['-','P01234',1]}
for n,row in shape.items(): assert new[n]==row,n
assert c['output']=='out'
# Authenticate all physical ports using zlib rather than the candidate's
# coefficient-propagation computation; neither is a Lean/file binding.
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
a=load(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for name,m in a['ports'].items():
    assert all(m[k]==b['ports'][name][k] for k in ('sha256_gzip','sha256_raw','raw_bytes','bits'))
    compressed=(D/root/m['path']).read_bytes();raw=zlib.decompress(compressed,31)
    assert sha(compressed)==m['sha256_gzip'] and sha(raw)==m['sha256_raw']
    assert len(raw)==m['raw_bytes'];ports[name]=int.from_bytes(raw,'little')
    assert ports[name].bit_length()==m['bits']
assert set(ports)==set(c['fixed_numerals']) and ports['K0']>0 and ports['beta']>0
prime=1000000007
def evaluate(t):
    e={n:t for n in c['witnesses']};e.update({n:v%prime for n,v in ports.items()})
    if RAY_COORD:e[RAY_COORD]=2*t
    def value(v):return v if type(v) is int else e[v]
    for n,op,x,y in c['source']:
        x,y=value(x),value(y)
        e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
    return e['out']
row=[evaluate(i) for i in range(DEGREE+1)]
for _ in range(DEGREE):row=[(y-x)%prime for x,y in zip(row,row[1:])]
leader=row[0]*pow(math.factorial(DEGREE),-1,prime)%prime
assert leader==LEADER
print(json.dumps({'scope':'independent graph edit, guard shape and degree lower bound; no Lean or PDF binding',
 'gates':GATES,'degree':DEGREE,'prime':prime,'ray_leader':leader,
 'ray_method':'finite differences','parent_degree_bound_inherited':True,
 'graph_shape_checks':len(shape),'actual_K0_positive':True},sort_keys=True,indent=2))
