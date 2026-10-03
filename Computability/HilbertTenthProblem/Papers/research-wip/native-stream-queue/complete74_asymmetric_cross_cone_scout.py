#!/usr/bin/env python3
"""Bounded exact reassociation scout on three saved asymmetric complete74 cuts.
No historical builder imports; no new positive-domain theorem.
"""
import argparse, copy, hashlib, itertools, json
from collections import Counter
from pathlib import Path
PINS={'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908','complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28','complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f'}
SCALE={'Lbig','n2','wn2','sn2','UM'}
PACK={'qF','packed','gap','Lm1','rproduct','qMF','mask_factor','mask','r_lhs'}
CUTS={'Lbig','wn2','sn2','UM','r_lhs'}
def need(ok,msg):
 if not ok: raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def plus(a,b,sgn=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+sgn*v
 return {k:v for k,v in c.items()if v}
def mul(a,b):
 c={}
 for u,x in a.items():
  for v,y in b.items():
   k=tuple(sorted(u+v));c[k]=c.get(k,0)+x*y
 return {k:v for k,v in c.items()if v}
def symbolic(rows):
 e={n:{(n,):1}for n in('q','w','s','F','Z','MC','MF','Jrep')}
 def val(v):return {():v}if type(v)is int and v else {}if type(v)is int else e[v]
 for n,o,a,b in rows:
  a,b=val(a),val(b);e[n]=mul(a,b)if o=='*'else plus(a,b,1 if o=='+'else-1)
 return e
def scale_rows(method,need_cube):
 rows=[['Lbig','*','q','q'],['wn2','*','w','q']]
 if method=='cube' or need_cube:rows.append(['n2','*','Lbig','q'])
 if method=='cube':rows.append(['sn2','*','s','n2'])
 else:rows.extend([['scale_sq','*','s','q'],['sn2','*','scale_sq','Lbig']])
 rows.append(['UM','*','wn2','sn2']);return rows
def packing_rows(method):
 r=[['Lm1','-','Lbig',1]]
 if method=='literal':r.extend([['qF','*','q','F'],['packed','+','Z','qF'],['gap','-','Lbig','packed'],['rproduct','*','gap','Lm1']])
 elif method=='horner':r.extend([['q_minus_F','-','q','F'],['q_gap','*','q','q_minus_F'],['gap','-','q_gap','Z'],['rproduct','*','gap','Lm1']])
 else:r.extend([['q_minus_F','-','q','F'],['cube_minus_q','-','n2','q'],['first_pack_product','*','q_minus_F','cube_minus_q'],['Z_Lm1','*','Z','Lm1'],['rproduct','-','first_pack_product','Z_Lm1']])
 r.extend([['qMF','*','q','MF'],['mask_factor','+','MC','qMF'],['mask','*','mask_factor','Jrep'],['r_lhs','+','rproduct','mask']]);return r
def sos(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 acc='square_0'
 for i in range(1,len(pairs)):out.append([f'sum_{i}','+',acc,f'square_{i}']);acc=f'sum_{i}'
 return out,acc
def ledger(rows,free,roots,fixed):
 available=set(free);defs={};degree={n:0 if n in fixed else 1 for n in free};M=0;seen={};dups=[]
 for n,o,a,b in rows:
  need(n not in available and o in('+','-','*'),'fresh gate')
  need(all(type(v)is int or v in available for v in(a,b)),'closed source')
  key=(o,tuple(sorted((a,b),key=repr))if o in('+','*')else(a,b))
  if key in seen:dups.append([seen[key],n])
  seen[key]=n;available.add(n);defs[n]=(a,b);M+=o=='*'
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b];degree[n]=da+db if o=='*'else max(da,db)
 live=set();inputs=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n in defs:
   if n not in live:live.add(n);todo.extend(defs[n])
  else:inputs.add(n)
 need(live==set(defs)and inputs==set(free),'all paid gates and inputs live')
 return dict(M=M,A=len(rows)-M,operations=len(rows),literal_commutative_CSE_duplicates=dups),degree

def scale_lower_bound():
 # Product-only monomial straight-line programs: supplied q,w,s are free;
 # square q² and ports wq,sq³,wsq⁴ must all be produced. Four operations
 # would have to produce precisely these four distinct target monomials.
 initial={(1,0,0),(0,1,0),(0,0,1)}
 targets={(2,0,0),(1,1,0),(3,0,1),(4,1,1)}
 feasible=[]
 for order in itertools.permutations(targets):
  have=set(initial);ok=True
  for target in order:
   if not any(tuple(x+y for x,y in zip(a,b))==target for a in have for b in have):ok=False;break
   have.add(target)
  if ok:feasible.append(order)
 need(not feasible,'four multiplications impossible in specified monomial model')
 return dict(minimum_multiplications=5,targets=['q²','wq','sq³','wsq⁴'],four_gate_orders_excluded=24,scope='multiplications only; supplied q,w,s; no divisions/additions or supplied-product aliases; q² retained for packing')

def verify(root):
 root=Path(root)
 for n,h in PINS.items():need(digest((root/n).read_bytes())==h,'pin '+n)
 parents=json.loads((root/'complete74_factored_first_norm.json').read_text())['forms'];need([f['mode']for f in parents]==['raw30','positive22','signed20'],'exact inventory')
 local=[];records=[];counts=Counter();base_cuts=symbolic(scale_rows('cube',False)+packing_rows('literal'))
 for scale,pack in itertools.product(('cube','sq'),('literal','horner','cube_factor')):
  sr=scale_rows(scale,pack=='cube_factor');pr=packing_rows(pack);ev=symbolic(sr+pr)
  need(all(ev[n]==base_cuts[n]for n in CUTS),'five exact local output polynomials')
  local.append(dict(scale=scale,packing=pack,multiplications=sum(r[1]=='*'for r in sr+pr),additions=sum(r[1]!='*'for r in sr+pr),outputs={n:[[list(m),c]for m,c in sorted(ev[n].items())]for n in sorted(CUTS)}))
  counts['local_cut_identities']+=len(CUTS)
  for form in parents:
   p=form['packet'];old=copy.deepcopy(p['source']);hits=[i for i,r in enumerate(old)if r==['wn2','*','w','n2']];need(len(hits)==1,'unique asymmetric operand cut');old[hits[0]][3]='q'
   for n,o,a,b in old:
    if n not in SCALE|PACK:need(not(set((a,b))&((SCALE|PACK)-CUTS)),'all external local consumers are preserved cuts')
   for pair in p['comparisons']:need(not(set(pair)&((SCALE|PACK)-CUTS)),'all comparison consumers are preserved cuts')
   out=[]
   for row in old:
    if row[0]=='Lbig':out.extend(copy.deepcopy(sr+pr))
    if row[0]not in SCALE|PACK:out.append(row)
   outside=lambda rs:[r for r in rs if r[0]not in SCALE|PACK and r[0]not in{'scale_sq','q_minus_F','q_gap','cube_minus_q','first_pack_product','Z_Lm1'}]
   need(outside(out)==outside(old),'every outside row unchanged in order')
   pairs=copy.deepcopy(p['comparisons']);poly,output=sos(out,pairs);free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]
   cl,deg=ledger(out,free,[v for ab in pairs for v in ab],p['fixed_numerals']);pl,pdeg=ledger(poly,free,[output],p['fixed_numerals'])
   need(not cl['literal_commutative_CSE_duplicates'],'no hidden literal CSE savings')
   expect=74+(1 if pack=='cube_factor' else 0)+(1 if pack=='cube_factor'and scale=='sq' else 0)
   need(cl['operations']==expect and pl['operations']==expect+3*len(pairs)-1,'full paid ledgers')
   # Whole-source lifting: all outside source rows and comparisons are
   # byte-identical; the five ring identities cover every crossing edge.
   counts['whole_graph_identities']+=1;counts['retained_comparisons']+=len(pairs);counts['full_live_gates']+=pl['operations']
   records.append(dict(mode=form['mode'],scale=scale,packing=pack,ordinary_input=p['ordinary_input'],fixed_numerals=copy.deepcopy(p['fixed_numerals']),witnesses=copy.deepcopy(p['witnesses']),source=out,comparisons=pairs,polynomial_source=poly,output=output,certificate_ledger=cl,polynomial_ledger=pl,naive_degree_upper=pdeg[output],scope='same complete polynomial as one-operand asymmetric source; no independently proved asymmetric positive inverse'))
 need(len(records)==18 and min(r['certificate_ledger']['operations']for r in records)==74,'bounded family')
 return dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),counts=dict(counts),scale_lower_bound=scale_lower_bound(),local_proofs=local,forms=records,scope='Three actual saved parents, two product scale schedules and three packing schedules only. All supplied ports unchanged. Minimum74 in this family; no global arithmetic lower bound, no new universal point, no transport coordinate substitution used.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],minimum=74)))
if __name__=='__main__':main()
