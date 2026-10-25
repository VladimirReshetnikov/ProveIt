"""Compress private quadratic wires by their shared consumer coefficients.

Arguments: --parent equation.json --output directory.
All transformation formulas refer to the pinned parent's zero-based indices.
The parent may be the 245-variable equation or its 241-variable horizon delta,
whose coordinates and rows through 89 retain those same indices.
"""
from pathlib import Path
from collections import defaultdict
import argparse,hashlib,json,copy

def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for mon,c in p.items():d[mon]+=c
 return {m:c for m,c in d.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def sub(p,q):return add(p,neg(q))
def mul(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,b in q.items():d[tuple(sorted(m+n))]+=c*b
 return {m:c for m,c in d.items() if c}
def scalar(c,p):return {m:c*v for m,v in p.items() if c*v}
def var(i):return {(i,):1}
def num(i):return {():i} if i else {}
def subst(p,replace):
 q={}
 for mon,c in p.items():
  summand=num(c)
  for i in mon:summand=mul(summand,replace.get(i,var(i)))
  q=add(q,summand)
 return q
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def write(path,obj):path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')
def sha(raw):return hashlib.sha256(raw).hexdigest()

def build(parent_path,out):
 raw=parent_path.read_bytes();parent=json.loads(raw);n=len(parent['variables'])
 rows=[{tuple(m):c for c,m in rr['terms']} for rr in parent['residuals']]
 p=var;F,S,Sp,a,b,s,K,J=[p(i) for i in (3,14,15,10,11,21,70,n)]
 g=sub(sub(S,Sp),p(82));d=add(scalar(6,a),scalar(8,b),scalar(2,s));aa=sub(a,num(1))
 expect={54:sub(K,mul(F,Sp)),65:sub(p(81),mul(p(80),p(80))),67:sub(p(83),mul(g,g)),68:sub(sub(p(84),num(1)),mul(F,b)),70:sub(sub(p(85),num(1)),mul(F,aa)),73:sub(sub(p(89),num(1)),mul(F,d))}
 for j,r in expect.items():
  if rows[j]!=r:raise ValueError(('changed parent row',j))
 removed_vars={83,84,85,89};removed_rows={67,68,70,73}
 edits={65:sub(sub(p(81),mul(p(80),p(80))),mul(g,g)),69:add(neg(Sp),neg(mul(K,b)),mul(p(86),p(87)),p(88)),72:add(neg(S),neg(mul(J,aa)),p(87)),74:add(S,mul(J,b),neg(Sp),neg(mul(K,d)),p(90))}
 newJ=sub(J,mul(F,S));oldindexrows=[];origin=[]
 for j,r in enumerate(rows):
  if j in removed_rows:continue
  rr=edits.get(j,{m:c for m,c in r.items() if 83 not in m})
  if any(i in removed_vars for mon in rr for i in mon):raise ValueError(('unhandled removed occurrence',j))
  oldindexrows.append(rr);origin.append(j)
 oldindexrows.append(newJ);origin.append(None)
 ren={i:j for j,i in enumerate(i for i in range(n+1) if i not in removed_vars)}
 variables=copy.deepcopy(parent['variables'])+[{'name':'horn.F_times_S','kind':'shared_product'}]
 variables=[variables[i] for i in range(n+1) if i not in removed_vars]
 variables[ren[81]]={'name':'horn.joint_square_sum','kind':'rank_aggregate'}
 result_rows=[]
 for r,j in zip(oldindexrows,origin):
  rr={tuple(ren[i] for i in mon):c for mon,c in r.items()}
  result_rows.append({'label':'shared F times S' if j is None else ('joint Horn square aggregate' if j==65 else parent['residuals'][j]['label']),'terms':terms(rr)})
 eq={'schema':'conzfc-consumer-basis-v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variables':variables,'residuals':result_rows,'parent_equation_sha256':sha(raw),'variant':f'consumer_basis{len(variables)}','source_commit':'a0ef2df5bb1f73c35cd334bbc7f53553350ef06a'}
 # Two symbolic residual maps prove existential equivalence over Z.
 reverse={81:mul(p(80),p(80)),83:sub(p(81),mul(p(80),p(80))),84:add(num(1),mul(F,b)),85:add(num(1),mul(F,aa)),89:add(num(1),mul(F,d))}
 restored=[subst(r,reverse) for r in rows]
 for j in (65,68,70,73):
  if restored[j]:raise ValueError(('deleted restored residual nonzero',j))
 reverse_target={67:edits[65],69:add(edits[69],mul(b,rows[54])),72:add(edits[72],mul(aa,newJ)),74:add(edits[74],neg(mul(b,newJ)),mul(d,rows[54]))}
 for j,r in enumerate(restored):
  expected={} if j in (65,68,70,73) else reverse_target.get(j,next((z for z,k in zip(oldindexrows,origin) if k==j),None))
  if expected is None or r!=expected:raise ValueError(('reverse symbolic identity failed',j))
 forward={81:add(p(81),p(83)),n:mul(F,S)}
 for nr,j in zip(oldindexrows,origin):
  fr=subst(nr,forward)
  if j is None:expected={}
  elif j==65:expected=add(rows[65],rows[67])
  elif j==69:expected=add(rows[69],mul(Sp,rows[68]),neg(mul(b,rows[54])))
  elif j==72:expected=add(rows[72],mul(S,rows[70]))
  elif j==74:expected=add(rows[74],neg(mul(S,rows[68])),mul(Sp,rows[73]),neg(mul(d,rows[54])))
  else:expected=rows[j]
  if fr!=expected:raise ValueError(('forward symbolic identity failed',j))
 expanded={}
 for rr in result_rows:
  rp={tuple(m):c for c,m in rr['terms']};expanded=add(expanded,mul(rp,rp))
 metrics={'variables':len(variables),'rows':len(result_rows),'degree':max(map(len,expanded)),'monomials':len(expanded),'height':max(map(abs,expanded.values())),'row_height':max(abs(c) for r in result_rows for c,_ in r['terms'])}
 cert={'schema':'consumer_basis_certificate_v1','parent_equation_sha256':sha(raw),'parent_variables':n,'new_variables':len(variables),'deleted_parent_coordinates':sorted(removed_vars),'deleted_parent_rows':sorted(removed_rows),'edited_parent_rows':sorted(edits),'added_parent_index':n,'new_row_parent_indices':origin,'old_to_new':[[i,j] for i,j in ren.items()],'reverse_polynomials':[[i,terms(v)] for i,v in reverse.items()],'forward_polynomials':[[i,terms(v)] for i,v in forward.items()],'verified_symbolic_forward_residual_identities':len(oldindexrows),'verified_symbolic_reverse_residual_identities':len(rows)}
 out.mkdir(parents=True,exist_ok=True)
 for name,obj in [('equation.json',eq),('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','domain':'unrestricted integers','variables':len(variables),'terms':terms(expanded)}),('METRICS.json',metrics),('basis_certificate.json',cert)]:write(out/name,obj)
 print(json.dumps(metrics))
 return eq,cert
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--parent',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);ns=ap.parse_args();build(ns.parent,ns.output)
