#!/usr/bin/env python3
"""Independent affine elimination and integer-domain quartic audit."""
import json,pathlib,collections,sys
D=pathlib.Path(__file__).resolve().parent;S=D.parent/'direct';O=D
if '--geometric' in sys.argv:S=S/'geometric';O=D/'geometric'
if '--fixed-base' in sys.argv:S=S/'fixed_base';O=D/'fixed_base'
def read(n):return json.loads((S/n).read_text())
def req(x,s):
 if not x:raise ValueError(s)
def parse(ts):
 d={}
 for v,m in ts:
  k=tuple(m);req(k==tuple(sorted(k)) and k not in d and v!=0,'noncanonical');d[k]=v
 return d
def add(a,b,sgn=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+sgn*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for k,v in a.items():
  for l,w in b.items():d[tuple(sorted(k+l))]+=v*w
 return {k:v for k,v in d.items() if v}
def accum(a,b):
 for k,v in b.items():
  a[k]=a.get(k,0)+v
  if not a[k]:del a[k]
j=read('circuit.json');am=read('affine_map.json');forms=list(map(parse,am['node_affine_forms']));wires={int(k):v for k,v in am['nonlinear_wire_map'].items()};nv=len(j['variable_names']);cursor=nv;rows=[]
req(len(forms)==len(j['nodes']),'maplength')
for i,n in enumerate(j['nodes']):
 if n[0]=='c':expected={():n[1]} if n[1] else {}
 elif n[0]=='v':expected={(n[1],):1}
 elif n[0]=='a':expected=add(forms[n[1]],forms[n[2]])
 else:
  expected=mul(forms[n[1]],forms[n[2]])
  if any(len(m)>1 for m in expected):
   req(wires.get(i)==cursor,'wireassignment');rows.append(add({(cursor,):1},expected,-1));expected={(cursor,):1};cursor+=1
 req(forms[i]==expected,'nodeaffinemap '+str(i));req(all(v>0 and len(k)<=1 for k,v in expected.items()),'notnonnegativeaffine')
for left,right,label in j['equalities']:rows.append(add(forms[left],forms[right],-1))
actual=read('residuals_affine.json');req(len(actual)==len(rows),'rowslength');p={}
for i,(r,want) in enumerate(zip(actual,rows)):
 f=parse(r['terms']);req(f==want,'affinerow '+str(i));req(max(map(len,f),default=0)<=2,'degree');accum(p,mul(f,f))
a=read('equation_affine.json');req(a['variable_count']==cursor and a['domain']=='nonnegative integers','affine header');req(parse(a['terms'])==p,'affine polynomial');req(max(map(len,p))==4,'exactdegree');naturalterms=len(p)
# Additional integer rows impose only original semantic-input nonnegativity.
extra=read('nonnegativity_residuals.json');req(len(extra)==nv,'nonnegativecount')
for i,r in enumerate(extra):
 a,b,c=cursor+3*i,cursor+3*i+1,cursor+3*i+2;want={(i,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1};f=parse(r['terms']);req(f==want,'nonnegativity formula');accum(p,mul(f,f))
e=read('equation_integer.json');req(e['domain']=='unrestricted integers' and e['variable_count']==cursor+3*nv,'integerheader');req(parse(e['terms'])==p,'integerpolynomial');req(max(map(len,p))==4,'integerdegree');req(set(v for m in p for v in m)==set(range(cursor+3*nv)),'deadintegercoordinate')
out={'status':'PASS','natural_variables':cursor,'natural_monomials':naturalterms,'integer_variables':cursor+3*nv,'integer_monomials':len(p),'semantic_inputs':nv,'nonlinear_wires':cursor-nv,'degree':4,'scope':'Exact every-node affine map, every quadratic residual, expandedSOS, semantic-input three-square nonnegativity rows, and expanded integer quartic. Unbounded range theorem is Legendre three-square theorem; wire nonnegativity follows from checked positive affine coefficients and topological multiplication.'}
(O/'AFFINE_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
