#!/usr/bin/env python3
"""Read-only 80-row source/graph binding and four-variant finalizer check."""
from pathlib import Path
from hashlib import sha256
import json,re,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parent/'ten-positive-unshift-t-finite/data';L=H/'Direct80Graph.lean'
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(v,m):
 if not v:raise SystemExit(m)
need(sha(L)=='f7214574d3c3266b358abf493b3c0c4ab00721a496afb0866f072165b8b93380','Lean source drift')
f=D/'equation_qcube_V2.json';need(sha(f)=='fcc5e40f5d22320541ec2af5857725ceafaa69d0df36708ec60d6b9a40a71f01','80 graph drift')
g=json.loads(f.read_bytes());source=L.read_text();body=source.split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\ntheorem a_shape',1)[0];lines=body.strip().splitlines()
vars=g['witnesses'];ports=g['fixed_numerals'];expected=[f'let {n} : Expr (Fin 10) := .var {i}' for i,n in enumerate(vars)]+[f'let {n} : Expr (Fin 10) := .constant (p {i})' for i,n in enumerate(ports)]
need([x.strip() for x in lines[:14]]==expected,'witness/port mismatch')
def rename(x):return 'fourAm1' if x=='4Am1' else x
parsed=[]
for line in lines[14:-1]:
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);need(m is not None,'unparsed '+line)
 n,x,op,y=m.groups();parsed.append([n,op,int(x) if x.isdigit() else x,int(y) if y.isdigit() else y])
expect=[[rename(n),op,rename(x),rename(y)] for n,op,x,y in g['source']]
need(parsed==expect and lines[-1].strip()=='⟨Delta,U,Dtau,DpI2,Dg,Q,V,Znum,Mtot,N⟩','rows/field mapping differ')
need(vars==['J','F','alpha','i','T','w','s','n','eta','zeta'] and ports==['beta','K0','MC','MF'] and g['output']=='N','signature differs')
known=set(vars+ports)|{0,1,2,3,4};rows={}
for n,op,x,y in g['source']:
 need(n not in known and x in known and y in known and op in ('+','-','*'),'topology '+n);known.add(n);rows[n]=(op,x,y)
live=set();todo=['N']
while todo:
 node=todo.pop()
 if node in rows and node not in live:live.add(node);todo.extend(rows[node][1:])
need(len(rows)==len(live)==80,'not 80 live rows')
common={'UE':('*','U','Dtau'),'SE':('*','Delta','UE'),'DpI2':('*','SE','U'),'Df':('+','DpI2',1),'aF0':('*','DpI2','Df'),'fouraF0':('*',4,'aF0'),'Fsqr':('+','fouraF0',1),'Q':('*','Delta','fouraF0'),'Dg':('*','Dtau','Df'),'M2':('*','Mtot','Mtot'),'Z2':('*','Znum','Znum'),'RG':('*','M2','Dg'),'V2':('*','V','V'),'RGV2':('*','RG','V2'),'inside':('-','Z2','RGV2'),'Qinside':('*','Q','inside'),'correction':('-','RG','Z2'),'N':('+','Qinside','correction')}
results={}
for name,n in [('equation_qcube_V2.json',80),('equation_qcube_bV.json',81),('equation_unsheared_V2.json',83),('equation_unsheared_bV.json',84)]:
 o=json.loads((D/name).read_bytes()); rr={row[0]:tuple(row[1:]) for row in o['source']};need(len(o['source'])==n and all(rr.get(k)==v for k,v in common.items()),'common factors mismatch '+name)
 results[name]={'sha256':sha(D/name),'rows':n,'degree':o['exact_degree']}
need('theorem output_eval' in source and 'theorem a_eval' in source and 'theorem g_eval' in source and 'theorem q_eval' in source,'missing named theorem')
print(json.dumps({'status':'PASS','source_rows':80,'live_rows':len(live),'input_slots':10,'port_slots':4,'four_common_factor_shapes':results,'scope':'external JSON/source comparison only'},indent=2))
