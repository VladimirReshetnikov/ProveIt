#!/usr/bin/env python3
"""Compute the entire diagonal polynomial over a prime field (no Lean)."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json,gzip
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-unshift-t-finite';raw=(P/'data/equation_qcube_V2.json').read_bytes();assert sha256(raw).hexdigest()=='fcc5e40f5d22320541ec2af5857725ceafaa69d0df36708ec60d6b9a40a71f01';g=json.loads(raw);mod=1000000007
polys={n:[0,1] for n in g['witnesses']};upper={n:1 for n in g['witnesses']}
for n,info in g['coefficient_binding']['ports'].items():
 b=(P/'coefficients'/info['file']).read_bytes();d=gzip.decompress(b);assert sha256(b).hexdigest()==info['gzip_sha256'] and sha256(d).hexdigest()==info['raw_sha256'];polys[n]=[int.from_bytes(d,'little')%mod];upper[n]=0
def get(x):return [x%mod] if type(x)==int else polys[x]
def deg(x):return 0 if type(x)==int else upper[x]
for name,op,a,b in g['source']:
 x,y=get(a),get(b)
 if op=='*':
  z=[0]*(len(x)+len(y)-1)
  for i,u in enumerate(x):
   if u:
    for j,v in enumerate(y):z[i+j]=(z[i+j]+u*v)%mod
  upper[name]=deg(a)+deg(b)
 elif op in ('+','-'):
  z=[0]*max(len(x),len(y));sgn=1 if op=='+' else -1
  for i,u in enumerate(x):z[i]=u
  for i,v in enumerate(y):z[i]=(z[i]+sgn*v)%mod
  upper[name]=max(deg(a),deg(b))
 else:raise ValueError(op)
 while len(z)>1 and z[-1]==0:z.pop()
 polys[name]=z
f=polys[g['output']];assert upper[g['output']]==750 and len(f)-1==750 and f[-1]!=0
nodes={row[0]:row for row in g['source']};seen=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n)
 if n in nodes:todo.extend(x for x in nodes[n][2:] if isinstance(x,str))
assert seen==set(nodes)|set(g['witnesses'])|set(g['fixed_numerals']) and len(nodes)==80 and Counter(x[1] for x in g['source'])=={'*':48,'+':18,'-':14}
print('PASS full diagonal polynomial modulo',mod,'degree 750 coefficient',f[-1],'; symbolic degree upper bound 750; all 80 operations and 14 inputs live')
