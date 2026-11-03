#!/usr/bin/env python3
"""First-residual-only counterexample to positive Bt for the 88 draft."""
from pathlib import Path
from hashlib import sha256
import json
path=Path(__file__).resolve().parent/'graph-dag.json'
if sha256(path.read_bytes()).hexdigest()!='84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25':raise RuntimeError('graph drift')
graph=json.loads(path.read_text());v={i:i for i in range(5)}
v.update({name:1 for name in graph['witnesses']+graph['fixed_numerals']});v['r']=251
for name,op,x,y in graph['source']:
 a,b=v[x],v[y];v[name]=a+b if op=='+' else a-b if op=='-' else a*b
expected={'qm':1,'q':2,'X':2,'Y':8,'k':2,'ell':256,'g30':258,'Bt':-2,'Z':257,'A0':0,'A1':91968576,'N':26599832578100044800}
if any(v[k]!=x for k,x in expected.items()):raise RuntimeError('unexpected graph evaluation')
print(json.dumps(expected,sort_keys=True))

v={i:i for i in range(5)}
v.update({name:1 for name in graph['witnesses']+graph['fixed_numerals']})
v.update(beta=3,MC=0,MF=0,F=2,r=32769)
for name,op,x,y in graph['source']:
 a,b=v[x],v[y];v[name]=a+b if op=='+' else a-b if op=='-' else a*b
expected2={'qm':3,'q':4,'X':4,'Y':64,'k':2,'ell':32768,'g30':32770,'Bt':0,'Z':98307,'A0':0}
if any(v[k]!=x for k,x in expected2.items()):raise RuntimeError('unexpected bounded-port evaluation')
if not (0<v['beta'] and v['MC']<v['beta'] and v['MF']<2*v['beta']):raise RuntimeError('port bounds')
print(json.dumps(expected2,sort_keys=True))

# An isolated first-factor zero whose G cannot be preserved by any positive
# transport representative at q=4 (Bt>0 forces F+alpha<q).
v={i:i for i in range(5)}
v.update({name:1 for name in graph['witnesses']+graph['fixed_numerals']})
v.update(beta=3,MC=0,MF=0,F=1,alpha=19,r=32461)
for name,op,x,y in graph['source']:
 a,b=v[x],v[y];v[name]=a+b if op=='+' else a-b if op=='-' else a*b
expected3={'q':4,'qm':3,'G':28,'Bt':-132,'ell':32768,'k':2,'Z':98307,'A0':0}
if any(v[k]!=x for k,x in expected3.items()):raise RuntimeError('unexpected normalization example')
for F in range(1,4):
 for alpha in range(1,4):
  if F+alpha<4:
   if alpha+3*(4-F)>11:raise RuntimeError('unexpected normalized G')
print(json.dumps(expected3,sort_keys=True))
