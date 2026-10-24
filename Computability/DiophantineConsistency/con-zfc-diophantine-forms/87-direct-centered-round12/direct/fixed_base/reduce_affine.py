#!/usr/bin/env python3
"""Eliminate affine circuit wires while preserving a literal quartic SOS."""
import json,pathlib,collections
R=pathlib.Path(__file__).resolve().parent
C=json.loads((R/'circuit.json').read_text())
A=[];rows=[];wiremap={};nv=len(C['variable_names'])
def add(a,b,sgn=1):
 out=collections.defaultdict(int,a)
 for m,v in b.items():out[m]+=sgn*v
 return {m:v for m,v in out.items() if v}
def mul(a,b):
 out=collections.defaultdict(int)
 for ma,va in a.items():
  for mb,vb in b.items():out[tuple(sorted(ma+mb))]+=va*vb
 return {m:v for m,v in out.items() if v}
def enc(p):return [[v,list(k)] for k,v in sorted(p.items())]
for i,n in enumerate(C['nodes']):
 if n[0]=='c':a={():n[1]} if n[1] else {}
 elif n[0]=='v':a={(n[1],):1}
 elif n[0]=='a':a=add(A[n[1]],A[n[2]])
 else:
  p=mul(A[n[1]],A[n[2]])
  if any(len(m)>1 for m in p):
   a={(nv,):1};wiremap[i]=nv;nv+=1
   rows.append({'label':'nonlinear gate '+str(i),'terms':enc(add(a,p,-1))})
  else:a=p
 A.append(a)
for left,right,label in C['equalities']:rows.append({'label':label,'terms':enc(add(A[left],A[right],-1))})
poly=collections.defaultdict(int)
for r in rows:
 p={tuple(m):v for v,m in r['terms']}
 for m,v in mul(p,p).items():poly[m]+=v
poly={m:v for m,v in poly.items() if v}
summary={'domain':'nonnegative integers','ordinary_polynomial_variables':nv,'ordinary_polynomial_degree':max(map(len,poly)),'ordinary_polynomial_monomials':len(poly),'input_existentials':len(C['variable_names']),'nonlinear_wires':nv-len(C['variable_names']),'SOS_residuals':len(rows),'max_residual_terms':max(len(r['terms']) for r in rows),'max_abs_coefficient':max(map(abs,poly.values())),'eliminated_affine_wires':json.loads((R/'summary.json').read_text())['ordinary_polynomial_variables']-nv}
for name,obj in [('equation_affine.json',{'format':'ordinary-polynomial-sparse-v1','domain':'nonnegative integers','variable_count':nv,'terms':enc(poly)}),('residuals_affine.json',rows),('affine_map.json',{'node_affine_forms':[enc(a) for a in A],'nonlinear_wire_map':wiremap}),('summary_affine.json',summary)]:
 (R/name).write_text(json.dumps(obj,separators=(',',':'))+'\n')
# Integer-domain quartic: enforce nonnegativity only on the semantic inputs.
intpoly=dict(poly);introws=[];base=nv
for j in range(len(C['variable_names'])):
 aa,bb,cc=base+3*j,base+3*j+1,base+3*j+2
 r={(j,):1,(aa,aa):-1,(bb,bb):-1,(cc,cc):-1,(cc,):-1}
 introws.append({'label':'semantic input nonnegativity '+str(j),'terms':enc(r)})
 for m,v in mul(r,r).items():intpoly[m]=intpoly.get(m,0)+v
intpoly={m:v for m,v in intpoly.items() if v}
integer_summary={'domain':'unrestricted integers','ordinary_polynomial_variables':nv+3*len(C['variable_names']),'ordinary_polynomial_degree':max(map(len,intpoly)),'ordinary_polynomial_monomials':len(intpoly),'semantic_inputs_constrained':len(C['variable_names']),'auxiliary_nonnegativity_variables':3*len(C['variable_names']),'max_abs_coefficient':max(map(abs,intpoly.values()))}
for name,obj in [('equation_integer.json',{'format':'ordinary-polynomial-sparse-v1','domain':'unrestricted integers','variable_count':integer_summary['ordinary_polynomial_variables'],'terms':enc(intpoly)}),('nonnegativity_residuals.json',introws),('summary_integer.json',integer_summary)]:
 (R/name).write_text(json.dumps(obj,separators=(',',':'))+'\n')
print(json.dumps({'natural':summary,'integer':integer_summary},indent=2))
