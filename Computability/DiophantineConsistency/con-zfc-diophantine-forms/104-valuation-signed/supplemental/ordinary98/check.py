#!/usr/bin/env python3
"""Exact free-register proof, parent-prefix equality, counts and scalar controls."""
from pathlib import Path
import json, random, gzip, hashlib
from build import build

def require(p,msg):
    if not p:raise ValueError(msg)

class Poly:
    def __init__(self,terms=0):
        self.t=terms if isinstance(terms,dict) else ({(0,0,0,0):terms} if terms else {})
    def __add__(self,b):
        b=b if isinstance(b,Poly) else Poly(b);o=self.t.copy()
        for m,c in b.t.items():o[m]=o.get(m,0)+c
        return Poly({m:c for m,c in o.items() if c})
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,b):return self+(-b if isinstance(b,Poly) else -Poly(b))
    def __rsub__(self,b):return Poly(b)+(-self)
    def __mul__(self,b):
        b=b if isinstance(b,Poly) else Poly(b);o={}
        for x,c in self.t.items():
            for y,d in b.t.items():
                m=tuple(a+b for a,b in zip(x,y));o[m]=o.get(m,0)+c*d
        return Poly({m:c for m,c in o.items() if c})
    __rmul__=__mul__
    def __pow__(self,k):
        r=Poly(1)
        for _ in range(k):r=r*self
        return r
d,Q,V,n=[Poly({tuple(int(i==j) for i in range(4)):1}) for j in range(4)]
e=1-Q;v=V+n
h=e*v*v+Q*V*V-1;b=e*Q;Ea=Q*V*V-1
old=(d*h+b)**2-d*Q*(2*e*v)**2
new=(d*h-b)**2+4*d*b*Ea
require(not (new-old).t,'universal polynomial identity')
packets=[build(False),build(True)]
parent=json.loads((Path(__file__).resolve().parent/'inherited/PARENT_LITERAL.json').read_text())
require(parent['source']==packets[0]['source'],'literal pinned parent graph')
require(parent['witnesses']==packets[0]['witnesses'],'literal pinned parent variables')
require(packets[0]['operations']==100 and packets[1]['operations']==98,'operation counts')
for p in packets:
    known=set(p['witnesses']+p['fixed_numerals']);seen=set()
    for name,op,a,b in p['source']:
        require(name not in known,'duplicate output')
        for q in (a,b): require(isinstance(q,int) or q in known,'undefined input')
        known.add(name);seen.add(name)
    live={p['output']}
    for name,op,a,b in reversed(p['source']):
        if name in live:live.update((a,b))
    require(seen<=live,'dead gate')
    require(set(p['witnesses']+p['fixed_numerals'])<=live,'dead input')
cut=lambda p: p['source'][:next(i for i,x in enumerate(p['source']) if x[0]=='vn2')+1]
require(cut(packets[0])==cut(packets[1]),'shared prefix')
def ev(p,env):
    e=dict(env)
    def get(a): return a if isinstance(a,int) else e[a]
    for name,op,a,b in p['source']:
        a,b=get(a),get(b)
        e[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return e[p['output']]
r=random.Random(12007098)
for _ in range(50):
    env={v:r.randint(-4,4) for v in packets[0]['witnesses']+packets[0]['fixed_numerals']}
    require(ev(packets[0],env)==ev(packets[1],env),'scalar identity control')
root=Path(__file__).resolve().parent
binding=json.loads((root/'native/ACTIVE_BINDING.json').read_text())
payloads={}
for port,row in binding['ports'].items():
    data=(root/'native'/row['file']).read_bytes();raw=gzip.decompress(data)
    require(hashlib.sha256(data).hexdigest()==row['sha256_gzip'],'compressed coefficient '+port)
    require(hashlib.sha256(raw).hexdigest()==row['sha256_raw'],'raw coefficient '+port)
    payloads[port]=int.from_bytes(raw,'little')
require(payloads['beta']==(1<<590069)-1,'compact44 beta identity')
require(0<payloads['MC']<payloads['beta']<payloads['MF']<2*payloads['beta'],'compact44 mask bounds')
receipt={'universal_free_register_identity':True,'identical_prefix_through':'vn2',
         'parent_operations':100,'new_operations':98,'new_breakdown':packets[1]['operation_breakdown'],
         'degree':70,'degree_proof':'identical polynomial; inherited attained-degree certificate',
         'scope':'Exact polynomial preservation and counts; no new calibration or semantic theorem',
         'scalar_controls':50,'compact44_payload_hashes':True}
(Path(__file__).resolve().parent/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
