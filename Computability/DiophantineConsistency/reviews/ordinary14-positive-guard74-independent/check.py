#!/usr/bin/env python3
"""Independent positive guard and exact graph checks; never invokes Lean."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess
import sys

D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-positive-guard74'
P=D/'research/ordinary14-negative-pell75'
R=D/'reviews/ordinary14-negative-pell75-independent'
def digest(data):return hashlib.sha256(data).hexdigest()
def pinned(path,expected):
    data=path.read_bytes()
    assert digest(data)==expected,str(path)
    return data

new=json.loads(pinned(A/'candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'))
old=json.loads(pinned(P/'candidate.json','89a9a0217d28d655fbf2592d995f4d766175a45560fa4d33b251dd3711e5b1c1'))
readme=(A/'README.md').read_bytes()
tail=(b'\nIndependent external review is recorded in\n'
      b'`../../reviews/ordinary14-positive-guard74-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)])=='e2aa139b7b0fa2d62da27500625775f5f219d9b36b230984ebb636952ceb71ce'
assert new['witnesses']==old['witnesses'] and new['fixed_numerals']==old['fixed_numerals']
assert new['domain']=='strictly positive integers'
assert [row for row in old['source'] if 'h' in row[2:]]==[['bt_quotient','*','qm','h']]
rows=[]
for row in old['source']:
    name=row[0]
    if name=='Fg':continue
    if name=='guard_base':rows.append(['guard_base','+','g27','qF'])
    elif name=='P01234':rows.append(['P01234','*','P0123','guard'])
    else:rows.append(row)
assert rows==new['source'] and len(rows)==74
known=set(new['witnesses']+new['fixed_numerals'])
assert len(known)==18
for name,op,a,b in rows:
    assert name not in known and op in {'+','-','*'}
    assert all(isinstance(x,int) or x in known for x in (a,b))
    known.add(name)
live={new['output']}
for name,_,a,b in reversed(rows):
    if name in live:live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in rows)
assert set(new['witnesses']+new['fixed_numerals'])<=live

def const(n):return {():n} if n else {}
def var(name):return {(name,):1}
def add(a,b,sign=1):
    out=dict(a)
    for key,val in b.items():out[key]=out.get(key,0)+sign*val
    return {key:val for key,val in out.items() if val}
def mul(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            key=tuple(sorted(ka+kb));out[key]=out.get(key,0)+va*vb
    return {key:val for key,val in out.items() if val}
b,c,x,K,f,h=map(var,('b','C','X','K','F','h'))
q=add(const(1),b)
old_guard=add(add(mul(c,add(x,K)),f,-1),mul(b,add(h,const(1),-1)),-1)
new_guard=add(add(mul(c,add(x,K)),add(q,f,-1)),mul(b,h),-1)
assert add(const(1),old_guard)==new_guard

def fingerprints(graph,side):
    values={name:digest(('var:'+name).encode()) for name in graph['witnesses']+graph['fixed_numerals']}
    def token(x):return 'int:'+str(x) if isinstance(x,int) else values[x]
    for name,op,a,b0 in graph['source']:
        if side=='old' and name=='Fg':values[name]='proved:guard-shift'
        elif side=='new' and name=='guard':values[name]='proved:guard-shift'
        else:values[name]=digest(json.dumps([op,token(a),token(b0)],separators=(',',':')).encode())
    return values
ot,nt=fingerprints(old,'old'),fingerprints(new,'new')
for name in ('F0','F1','Fa','Fs','P0123','P01234','out'):
    assert ot[name]==nt[name],name

negative=positive=0
for q0 in range(2,15):
    for F in range(1,q0+5):
        for alpha in range(1,q0+5):
            for w in range(1,5):
                for K0 in range(5):
                    C=q0-F-alpha
                    B=C*(q0*w+K0)-F
                    assert B!=0
                    if C<=0:assert B<0;negative+=1
                    else:assert F<=q0-2 and B>=2;positive+=1
assert negative>0 and positive>0
assert (3-1-1)*(3*1-2)-1==0  # Negative K0 breaks the Bprime nonzero argument.

base=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind72=json.loads(pinned(base/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
bind115=json.loads(pinned(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports={}
for name,info in bind72['ports'].items():
    assert all(bind115['ports'][name][key]==info[key] for key in ('sha256_raw','sha256_gzip'))
    compressed=(base/info['path']).read_bytes()
    assert digest(compressed)==info['sha256_gzip']
    raw=gzip.decompress(compressed)
    assert len(raw)==info['raw_bytes'] and digest(raw)==info['sha256_raw']
    ports[name]=int.from_bytes(raw,'little')
assert ports['beta']>0 and ports['K0']>=0

prime=1000000009
env={name:[13*i+1,i+2] for i,name in enumerate(new['witnesses'])}
env.update({name:[value%prime] for name,value in ports.items()})
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def plus(a,b,sign):
    return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def times(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%prime
    return trim(out)
def value(x):return [x%prime] if isinstance(x,int) else env[x]
for name,op,a,b0 in rows:
    env[name]=times(value(a),value(b0)) if op=='*' else plus(value(a),value(b0),1 if op=='+' else -1)
ray=env[new['output']]
assert len(ray)-1==107 and ray[-1]!=0

for packet in (A,R):
    run=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
    assert not run.stderr and run.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external all-positive witness maps; no Lean/PDF theorem',
                  'operations':len(rows),'counts':dict(Counter(row[1] for row in rows)),
                  'all_live':True,'exact_guard_cut_and_downstream_dag':True,
                  'negative_C_controls':negative,'positive_C_controls':positive,
                  'negative_K0_scalar_boundary':True,'parent_review_replayed':True,
                  'prime':prime,'weighted_ray_degree':len(ray)-1,'weighted_ray_leader':ray[-1],
                  'author_readme_prelink_sha256':digest(readme[:-len(tail)])},sort_keys=True,indent=2))
