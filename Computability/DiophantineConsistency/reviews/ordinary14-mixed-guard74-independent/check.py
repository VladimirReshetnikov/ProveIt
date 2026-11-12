#!/usr/bin/env python3
"""Independent mixed-domain shift and graph checks; never invokes Lean."""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-mixed-guard74'
P = D / 'research/ordinary14-negative-pell75'

def digest(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert digest(data) == expected, str(path)
    return data

new = json.loads(pinned(A / 'candidate.json', 'bbb7c75f9a14df45c11e21ebcf28687f8abd6c97a773df151365a0ac71298152'))
old = json.loads(pinned(P / 'candidate.json', '89a9a0217d28d655fbf2592d995f4d766175a45560fa4d33b251dd3711e5b1c1'))
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent external review is recorded in\n'
        b'`../../reviews/ordinary14-mixed-guard74-independent/`.\n')
assert readme.endswith(tail)
assert digest(readme[:-len(tail)]) == '3cd65467b35eb4383fcf82cf55c37869f43e8dd321a02a5b3f98557ff8da6f47'
assert new['witnesses'] == old['witnesses'] and new['fixed_numerals'] == old['fixed_numerals']
assert new['domain'] == 'F nonnegative; all other inputs strictly positive'
assert [row for row in old['source'] if 'F' in row[2:]] == [['qF','-','q','F'], ['guard_base','-','g27','F']]
rows = []
for row in old['source']:
    name = row[0]
    if name == 'Fg': continue
    if name == 'qF': rows.append(['qF','-','qm','F'])
    elif name == 'P01234': rows.append(['P01234','*','P0123','guard'])
    else: rows.append(row)
assert rows == new['source'] and len(rows) == 74
known = set(new['witnesses'] + new['fixed_numerals'])
assert len(known) == 18
for name, op, a, b in rows:
    assert name not in known and op in {'+', '-', '*'}
    assert all(isinstance(x, int) or x in known for x in (a,b))
    known.add(name)
live = {new['output']}
for name, _, a, b in reversed(rows):
    if name in live: live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in rows)
assert set(new['witnesses'] + new['fixed_numerals']) <= live

# Exact cut identities in Z[b,F,C,X,K,h], before any domain restriction.
def const(n): return {(): n} if n else {}
def var(name): return {(name,): 1}
def add(a,b,sign=1):
    out=dict(a)
    for key,val in b.items(): out[key]=out.get(key,0)+sign*val
    return {key:val for key,val in out.items() if val}
def mul(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            key=tuple(sorted(ka+kb))
            out[key]=out.get(key,0)+va*vb
    return {key:val for key,val in out.items() if val}
b,f,c,x,K,h=map(var,('b','F','C','X','K','h'))
q=add(const(1),b)
f_old=add(f,const(1))
assert add(q,f_old,-1) == add(b,f,-1)
old_guard=add(add(mul(c,add(x,K)),f_old,-1),mul(b,h),-1)
new_guard=add(add(mul(c,add(x,K)),f,-1),mul(b,h),-1)
assert add(const(1),old_guard) == new_guard

def fingerprints(graph, side):
    tokens={name:digest(('var:'+name).encode()) for name in graph['witnesses']+graph['fixed_numerals']}
    def term(x): return 'int:'+str(x) if isinstance(x,int) else tokens[x]
    for name,op,a,b0 in graph['source']:
        if name=='qF': tokens[name]='proved:qF-shift'
        elif side=='old' and name=='Fg': tokens[name]='proved:guard-shift'
        elif side=='new' and name=='guard': tokens[name]='proved:guard-shift'
        else: tokens[name]=digest(json.dumps([op,term(a),term(b0)],separators=(',',':')).encode())
    return tokens

ot,nt=fingerprints(old,'old'),fingerprints(new,'new')
for name in ('C','G','R','A1','Fa','g72','F0','F1','Fs','P0123','P01234','out'):
    assert ot[name]==nt[name], name
for value in range(100): assert value>=0 and value+1>0 and (value+1)-1==value

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

prime=1000000009
env={name:[11*i+1,i+2] for i,name in enumerate(new['witnesses'])}
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

run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],cwd=D,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
assert not run.stderr and run.stdout==(A/'result.json').read_bytes()
print(json.dumps({'scope':'external mixed-domain coordinate identity; no Lean/PDF theorem',
                  'operations':len(rows),'counts':dict(Counter(row[1] for row in rows)),
                  'all_live':True,'exact_shift_cuts_and_downstream_dag':True,
                  'nonnegative_coordinate':'F','prime':prime,
                  'weighted_ray_degree':len(ray)-1,'weighted_ray_leader':ray[-1],
                  'author_readme_prelink_sha256':digest(readme[:-len(tail)])},sort_keys=True,indent=2))
