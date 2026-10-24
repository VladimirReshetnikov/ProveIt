#!/usr/bin/env python3
"""Independent exact polynomial lifting audit. Does not import the compiler."""
import json,pathlib,collections,hashlib
D=pathlib.Path(__file__).resolve().parent;S=D.parent
def req(c,m):
 if not c:raise ValueError(m)
def read(n):return json.loads((S/n).read_text())
def add(p,q,sign=1):
 r=p.copy()
 for k,v in q.items():r[k]=r.get(k,0)+sign*v
 return {k:v for k,v in r.items() if v}
def mul(p,q):
 r=collections.defaultdict(int)
 for a,x in p.items():
  for b,y in q.items():r[tuple(sorted(a+b))]+=x*y
 return {k:v for k,v in r.items() if v}
def unpack(ts):
 p={}
 for c,vs in ts:
  req(isinstance(c,int) and c!=0,'noninteger/zero coefficient');key=tuple(vs);req(tuple(sorted(key))==key and key not in p,'noncanonical monomial');p[key]=c
 return p
c=read('circuit.json');nodes=c['nodes'];names=c['variable_names'];nv=len(names);mapping={};cursor=nv
for i,n in enumerate(nodes):
 op=n[0]
 if op=='c':req(len(n)==2 and isinstance(n[1],int) and n[1]>=0,'badconstant')
 elif op=='v':req(0<=n[1]<nv,'badvariable');mapping[i]=n[1]
 else:
  req(op in ['a','m'] and len(n)==3 and all(isinstance(x,int) and 0<=x<i for x in n[1:]),'badgate')
  mapping[i]=cursor;cursor+=1
req(set(n[1] for n in nodes if n[0]=='v')==set(range(nv)),'unused variable declaration')
def value(i):return {():nodes[i][1]} if nodes[i][0]=='c' and nodes[i][1] else {} if nodes[i][0]=='c' else {(mapping[i],):1}
expected=[]
for i,n in enumerate(nodes):
 if n[0] in ['a','m']:
  a,b=map(value,n[1:]);rhs=add(a,b) if n[0]=='a' else mul(a,b);expected.append(add(value(i),rhs,-1))
for a,b,label in c['equalities']:req(0<=a<len(nodes) and 0<=b<len(nodes),'badendpoint');expected.append(add(value(a),value(b),-1))
rows=read('residuals.json');req(len(rows)==len(expected),'rowcount');polynomial={}
for i,(row,want) in enumerate(zip(rows,expected)):
 p=unpack(row['terms']);req(p==want,'row mismatch '+str(i));req(max(map(len,p),default=0)<=2,'nonquadratic row');
 for mon,coef in mul(p,p).items():
  polynomial[mon]=polynomial.get(mon,0)+coef
  if not polynomial[mon]:del polynomial[mon]
e=read('equation.json');req(e['domain']=='nonnegative integers','wrongdomain');req(e['variable_count']==cursor,'variable count');req(unpack(e['terms'])==polynomial,'SOS expansion mismatch');degree=max(map(len,polynomial));req(degree==4,'notexactquartic');req(set(v for m in polynomial for v in m)==set(range(cursor)),'dead polynomial variables')
summary=read('summary.json');req(summary['ordinary_polynomial_monomials']==len(polynomial),'monomial count');req(summary['ordinary_polynomial_variables']==cursor,'summaryvariables');req(summary['SOS_residuals']==len(rows),'summaryrows')
# Each branch explicitly is the claimed sum of squared local equations.
h=read('horn_shared_source.json');hd=[]
for branch in h['branches']:
 def conv(ts):return {tuple(sorted(t['monomial'])):t['coefficient'] for t in ts if t['coefficient']}
 target={}
 for residual in branch['quadratic_residuals']:
  p=conv(residual);target=add(target,mul(p,p))
 req(target==conv(branch['sum_of_squares']),'HornSOS '+branch['name']);hd.append(max(map(len,target)))
req(sum(hd)==50 and h['witness_count']==17 and h['common_wire_count']==13,'Horncounts')
receipt={'status':'PASS','variables':cursor,'input_existentials':nv,'arithmetic_wires':cursor-nv,'quadratic_residuals':len(rows),'expanded_monomials':len(polynomial),'exact_degree':degree,'coefficient_max':max(map(abs,polynomial.values())),'horn_branches':len(hd),'scope':'Exact all-row graph lifting and complete sparse SOS equality; Horn local SOS identities. Not a proof of semantic arithmetic interfaces or ZFC calibration.','sha256':{n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n in ['circuit.json','equation.json','residuals.json','horn_shared_source.json','row_source.json']}}
(D/'STRUCTURE_CHECK.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
