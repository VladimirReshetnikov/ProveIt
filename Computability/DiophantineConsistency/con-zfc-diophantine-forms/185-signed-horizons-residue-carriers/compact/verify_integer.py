#!/usr/bin/env python3
"""Verify literal integer-domain substitution and its exact weighted leader."""
import hashlib
import json
from pathlib import Path
from verify import check, require

ROOT=Path(__file__).resolve().parent
parent_path=ROOT/'equations/positive14_ops68_degree146.json'
parent=json.loads(parent_path.read_text())
p=json.loads((ROOT/'integer_equations/integer36_degree288.json').read_text())
free={'f','n','tau'}
weights={x:1 if x in free else 2 for x in parent['witnesses']}
leader=check(parent_path,weights=weights,expected_degree=288)
require(p['source'][-len(parent['source']):]==parent['source'],'Lifted graph tail differs from parent')
require(p['lift']['source_sha256']==hashlib.sha256(parent_path.read_bytes()).hexdigest(),'Parent identity mismatch')
require(p['coefficient_binding']['ports']==parent['coefficient_binding']['ports'],'Fixed tuple changed')
prefix=p['source'][:-len(parent['source'])]
require(len(prefix)==77 and len(p['source'])==145,'Incorrect arithmetic cost')
require(len(p['witnesses'])==36 and len(set(p['witnesses']))==36,'Incorrect integer variable count')

# Expand each local quadratic substitution as an exact polynomial in its three
# independent coordinates. This checks algebra, not a textual copy of a builder.
def plus(a,b,sgn=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sgn*c
        if not out[m]: del out[m]
    return out

def times(a,b):
    out={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            m=tuple(x+y for x,y in zip(ma,mb))
            out[m]=out.get(m,0)+ca*cb
    return {m:c for m,c in out.items() if c}

for x in parent['witnesses']:
    if x in free:
        require(x in p['witnesses'],'Missing unrestricted coordinate')
        continue
    names=[x+'_a',x+'_b',x+'_c']
    require(all(y in p['witnesses'] for y in names),'Missing substituted coordinate')
    vals={names[0]:{(1,0,0):1},names[1]:{(0,1,0):1},names[2]:{(0,0,1):1}}
    def val(a): return {(0,0,0):a} if isinstance(a,int) else vals[a]
    selected=[r for r in prefix if r[0]==x or r[0].startswith(x+'_')]
    for name,op,a,b in selected:
        aa,bb=val(a),val(b)
        vals[name]=times(aa,bb) if op=='*' else plus(aa,bb,1 if op=='+' else -1)
    require(vals[x]=={(0,0,0):1,(2,0,0):1,(0,2,0):1,(0,0,2):1,(0,0,1):1},'Incorrect positive parametrization')

known=set(p['witnesses'])|set(p['fixed_numerals'])
rows={}
for name,op,a,b in p['source']:
    require(name not in known,'Duplicate gate')
    require(all(isinstance(v,int) or v in known for v in (a,b)),'Unclosed gate')
    known.add(name);rows[name]=(a,b)
live=set();stack=[p['output']]
while stack:
    x=stack.pop()
    if isinstance(x,int) or x in live: continue
    live.add(x);stack.extend(rows.get(x,()))
require(live==known,'Dead quantified coordinate or gate')
require(p['exact_degree']==leader['degree']==288,'Exact degree mismatch')
print(json.dumps({'name':p['name'],'variables':36,'operations':145,'exact_degree':288,
                  'positive_substitutions':11,'free_integer_coordinates':sorted(free),
                  'weighted_parent_leader':leader,'status':'PASS'},indent=2))
