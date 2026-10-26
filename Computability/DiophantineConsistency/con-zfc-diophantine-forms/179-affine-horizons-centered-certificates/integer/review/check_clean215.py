#!/usr/bin/env python3
"""Independent finite audit of the new weak-frame215 prototype; no producer imports."""
from pathlib import Path
from collections import defaultdict
import hashlib,json
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
SOURCE=ROOT/'round21/integer/final/beta217/equation.json'
NEW=ROOT/'round22/integer/clean215'
def read(p):return json.loads(p.read_bytes())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,s):
 if not ok:raise ValueError(s)
def add(*pp):
 r=defaultdict(int)
 for p in pp:
  for m,c in p.items():r[m]+=c
 return {m:c for m,c in r.items() if c}
def scale(p,k):return {m:c*k for m,c in p.items() if c*k}
def mul(p,q):
 r=defaultdict(int)
 for m,c in p.items():
  for n,d in q.items():r[tuple(sorted(m+n))]+=c*d
 return {m:c for m,c in r.items() if c}
def pol(r):return {tuple(m):c for c,m in r['terms']}
def equal_rows(a,b):return len(a)==len(b) and all(x==y for x,y in zip(a,b))
def measure(eq):
 rows=[pol(r)for r in eq['residuals']];p=add(*(mul(r,r)for r in rows));n=len(eq['variables'])
 return {'variables':n,'rows':len(rows),'degree':max(map(len,p)),'monomials':len(p),'height':max(map(abs,p.values())),'all_variables_live':{i for m in p for i in m}==set(range(n))}
j=read(SOURCE);names={v['name']:i for i,v in enumerate(j['variables'])};labels={r['label']:i for i,r in enumerate(j['residuals'])};old=[pol(r)for r in j['residuals']];rows=list(old)
V=lambda name:{(names[name],):1};C=lambda n:{():n} if n else{}
t=V('t0');F=V('crt.growth_majorant_F');A=add(V('shared.A'),C(1));Y=V('index0.Y');Yb=V('index2.Y');W=V('shared.W');U=V('mul.450');VV=V('mul.451');z=V('shared.Zminus1')
need(rows[99]==add(V('base0.T'),mul(t,t),C(1),scale(mul(A,t),-2)),'Old growth modulus')
d=add(t,C(2));rows[99]=add(V('base0.T'),mul(d,d),C(1),scale(mul(A,d),-2));rows[100]=add(rows[100],scale(Y,-2))
old_error=add(Yb,scale(t,-1),scale(F,-1));new_error=add(Yb,scale(Y,-1),scale(F,-1))
ii=labels['cap.pooled_index_residue'];rows[ii]=add(rows[ii],mul(new_error,new_error),scale(mul(old_error,old_error),-1))
# Recover actual anchor index from its defining cap residue, without using the producer's ledger.
cap=old[labels['cap.index_residue']];J=scale(add(cap,scale(V('cap.R'),-1),scale(mul(V('index15.Y'),V('cap.h')),4)),-1)
need(all(len(m)<=1 for m in J),'Anchor atom must be affine')
atoms=[('t',t),('F+t',add(t,F)),('x',V('x')),('y+1',V('y')),('F',F),('B',V('choose0.output')),('a',add(V('crt.encoded.a'),C(-1)))]
atoms +=[(s,V('crt.encoded.'+s))for s in ['b','c','d','S','Sp','u','vq']]
atoms +=[('C',V('crt.encoded_index_minus_one')),('N',V('pow1.output')),('J',J),('q',add(scale(V('radix.odd_square_root_half'),4),C(1))),('q+1',add(scale(V('radix.odd_square_root_half'),4),C(2))),('BH',V('self_radix.BH'))]
atoms +=[(f'pow{i}.output',V(f'pow{i}.output'))for i in [3,4,5,7,8,9,10,11,12,13,14,15,16,17]]
atoms +=[('growth_base',d)]
def reparam(p):return {m:c*8**m.count(names['t0']) for m,c in p.items()}
rows=[reparam(p)for p in rows];atoms=[(s,reparam(p))for s,p in atoms]
under=sorted({m[0]for _,p in atoms for m in p if m});bounds={s:abs(p.get((),0))+sum(c*c//4 for m,c in p.items()if m)for s,p in atoms};constant=max(bounds.values())+1
need(constant==22 and len(under)==43,'Exact weak frame constants changed')
need(all(not j['variables'][i]['name'].startswith(('shared.','index','cap.','base')) for i in under),'Private Pell dependency in frame')
rows[labels['shared.frame_definition']]=add(W,C(-constant),*({(i,i):-1}for i in under))
need(old[94]==add(U,W,scale(mul(W,z),-2)),'Old frame ordinate')
need(old[95]==add(VV,scale(mul(W,U),-1),scale(U,-1)),'Old frame product')
rows[94]=add(U,scale(W,4),scale(mul(W,z),-8));rows[95]=add(VV,scale(mul(W,U),-4),scale(U,-1))
need(old[96]==add(mul(A,A),mul(U,U),scale(mul(VV,VV),-1),C(-1)),'Unchanged full frame norm')
deleted=names['cofinal.horizon_root'];removedrow=labels['cofinal.horizon']
need(old[removedrow]==add(t,C(-16),{(deleted,deleted):-1}),'Original horizon')
need(all(all(deleted not in m for m in row)for i,row in enumerate(rows)if i!=removedrow),'Deleted root not private')
# Independently verify the exact three Horn consumer identities.
S=V('crt.encoded.S');Sp=V('crt.encoded.Sp');K=V('mul.314');aa=V('crt.encoded.a');bb=V('crt.encoded.b');ss=V('mul.40')
pindex=names['mul.337'];rindex=names['mul.340'];jindex=len(j['variables']);Jprod={(jindex,):1}
need(old[47]==add(K,scale(mul(F,Sp),-1)),'Retained K definition')
need(old[60]==add(V('mul.337'),C(-1),scale(mul(F,bb),-1)),'Old p definition')
need(old[62]==add(V('mul.340'),C(-1),scale(mul(F,add(aa,C(-1))),-1)),'Old r definition')
new61=add(scale(Sp,-1),scale(mul(K,bb),-1),mul(V('mul.342'),V('mul.344')),V('sqd.13'))
new64=add(scale(S,-1),scale(mul(Jprod,add(aa,C(-1))),-1),V('mul.344'))
new65=add(S,mul(Jprod,bb),scale(Sp,-1),scale(mul(K,add(scale(aa,2),scale(bb,4),scale(ss,2))),-1),V('sqd.14'))
submap={pindex:add(C(1),mul(F,bb)),rindex:add(C(1),mul(F,add(aa,C(-1)))),names['mul.314']:mul(F,Sp),jindex:mul(F,S)}
def subst(p):
 out={}
 for m,c in p.items():
  term=C(c)
  for i in m:term=mul(term,submap.get(i,{(i,):1}))
  out=add(out,term)
 return out
need(subst(new61)==subst(old[61]),'Exact Horn consumer61')
need(subst(new64)==subst(old[64]),'Exact Horn consumer64')
need(subst(new65)==subst(add(old[65],mul(Sp,old[63]))),'Exact Horn consumer65 plus Sp times row63')
rows[61]=new61;rows[64]=new64;rows[65]=new65;rows.append(add(Jprod,scale(mul(F,S),-1)))
removed={deleted,pindex,rindex};omitted={removedrow,60,62}
need(all(all(x not in m for x in removed for m in row)for i,row in enumerate(rows)if i not in omitted),'Deleted variables remain')
keep=[i for i in range(len(j['variables'])+1)if i not in removed];ren={i:k for k,i in enumerate(keep)}
predicted=[{tuple(ren[x]for x in m):c for m,c in row.items()}for i,row in enumerate(rows)if i not in omitted]
weak=read(NEW/'weak215/equation.json');need(equal_rows(predicted,[pol(r)for r in weak['residuals']]),'Exact complete semantic mutation differs')
results={'source_sha256':sha(SOURCE),'weak_sha256':sha(NEW/'weak215/equation.json'),'weak_frame_constant':constant,'underlying_coordinate_count':len(under),'bound_constants':bounds,'no_private_Pell_dependency':True,'all_semantic_mutations_reconstructed':True,'Horn_consumer_identities':['new61 = old61 after old p/r and retained K=FSp,new Jprod=FS substitutions','new64 = old64 after those substitutions','new65 = old65 + Sp*old63 after those substitutions'],'Horn_deleted_coordinates_private_after_restoration':True,'weak_metrics':measure(weak),'variants':{}}
for tag in ['integer215','integer215_sparse']:
 eq=read(NEW/tag/'equation.json');c=read(NEW/tag/'row_certificate.json');need(c['input_sha256']==results['weak_sha256'] and c['output_sha256']==sha(NEW/tag/'equation.json'),'Row certificate file binding')
 rr=list(predicted)
 for i,k,a in c['operations']:
  need(i!=k,'Noninvertible row operation');rr[i]=add(rr[i],scale(rr[k],a))
 need(equal_rows(rr,[pol(r)for r in eq['residuals']]),'Forward row replay')
 for i,k,a in reversed(c['operations']):rr[i]=add(rr[i],scale(rr[k],-a))
 need(equal_rows(rr,predicted),'Inverse row replay')
 met=measure(eq);expected=read(NEW/tag/'metrics.json');need(all(met[k]==expected[k]for k in ['variables','rows','degree','monomials','height']),'Independent exact collection mismatch')
 results['variants'][tag]={'sha256':sha(NEW/tag/'equation.json'),'reversible_row_operations':len(c['operations']),'metrics':met}
results['status']='PASS finite source mutation and exact collection; semantic proof separately reviewed'
(OUT/'CLEAN215_INDEPENDENT.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
