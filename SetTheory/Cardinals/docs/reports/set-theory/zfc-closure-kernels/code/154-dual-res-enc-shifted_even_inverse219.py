#!/usr/bin/env python3
"""Shifted even formula codes with negative equality and 11-leaf inverse MP.

I(a,b)=max(0,4P(a,b)-2), Q(a,b)=4P(a,b), R=4P+1, J=4P+3.
The source measurements do not certify changed runtime entries or startup.
"""
import json,itertools,collections
from functools import cache
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'shifted_even_inverse219';OUT.mkdir(exist_ok=True)
imp=z.MACRO[119];pop=imp[0];pair=imp[1][0];scale=imp[1][1]
word=tuple(tuple(r[1:])for r in ROWS);iw=q.x.flat(imp)
occ=[]
for i in range(len(word)-len(iw)+1):
 if word[i:i+len(iw)]!=iw:continue
 j=i+len(iw);k=0
 while j+k<len(word)and word[j+k]==q.CI(1):k+=1
 occ.append((i,j,k))
assert collections.Counter(k for i,j,k in occ)=={0:41,1:12,2:22,3:6}
builders={(i,j):k for i,j,k in occ};tags={j+h:(k,h,j)for i,j,k in occ for h in range(k)}
def skeleton(n,lo=0):
 hi=lo+len(q.x.flat(n))
 if (lo,hi)in builders:return('B',builders[lo,hi])
 if 2527<=lo and hi<=2574:return('D',n)
 if 4598<lo and hi<=4610:return('X',)
 if s.leaf(n):
  if lo==4598:return('O',)
  return('T',*tags[lo])if lo in tags else('F',n)
 return('N',skeleton(n[0],lo),skeleton(n[1],lo+len(q.x.flat(n[0]))))
SK=skeleton(OLD)
def P(a,b):return(a+b)*(a+b+1)//2+b
shifted_scales=[]
for n in q.assocs((q.CD(7),q.CI(1),q.CI(1),scale)):
 if s.boundary(n)!=(0,0,False):continue
 good=True
 for h in range(16):
  rr=[3,0,2,0,4,5,0,h,8]
  try:oo,_=q.sim(n,rr,20000)
  except RuntimeError:good=False;break
  exp=rr.copy();exp[1]=max(0,4*h-2);exp[7]=0
  if oo!=exp:good=False;break
 if good:shifted_scales.append(n)
ibs=[]
for sc in shifted_scales:ibs.extend(q.assocs((pop,pair,sc)))
# A second implementation computes the old code then saturating-subtracts two.
for zero in(6,7):
 nop=q.CD(zero),q.CC(1)
 for dec in [((q.CD(1),q.CD(1)),nop),(q.CD(1),(q.CD(1),nop))]:
  ibs.append((imp,dec))
ibs=list(dict.fromkeys(ibs))
builder_checks=0
for ib in ibs:
 for a,bv,rest in itertools.product(range(4),range(4),range(2)):
  rr=[3,bv,P(a,rest),0,4,5,0,0,8];oo,_=q.sim(ib,rr)
  exp=rr.copy();exp[1]=max(0,4*P(a,bv)-2);exp[2]=rest
  assert oo==exp,(a,bv,rest,oo,exp);builder_checks+=1
def replace_imp(n,ib):
 if n==imp:return ib
 if s.leaf(n):return n
 return replace_imp(n[0],ib),replace_imp(n[1],ib)
odd=q.CD(5),((q.CD(5),q.CC(2)),('CH',None))
def source(ib,compact):
 neg=replace_imp(z.MACRO[218],ib)
 def go(sk):
  k=sk[0]
  if k=='F':return sk[1]
  if k=='B':return ib if sk[1]==0 else imp
  if k=='D':return None if compact else replace_imp(sk[1],ib)
  if k=='X':return None
  if k=='O':return odd
  if k=='T':
   tag,slot,end=sk[1:]
   if tag==2:return None
   if tag==3 and slot==2 and not(compact and end==2524):return(q.CI(1),neg)
   return q.CI(1)
  a,c=go(sk[1]),go(sk[2])
  return c if a is None else a if c is None else(a,c)
 return go(SK)
loop=((q.CD(5),(q.CD(5),q.CD(5))),q.CD(5)),q.ubody
cmp=s.subtree(OLD,'111110');core=cmp,q.move71
mps=q.assocs((loop,q.move65,q.move16,core,q.clear7))
assert len(mps)==14
mpchecks=0
for h in range(160):
 a,bv=q.unp(h//4+(h%4==2))
 for tw in sorted(set((0,1,2,3,4,5,a,a+1))):
  rr=[3,tw,5,0,6,h,0,0,7];oo,_=q.sim(mps[0],rr)
  exp=rr.copy();exp[1]=bv if tw==a else 0;exp[5]=exp[6]=exp[7]=0
  assert oo==exp,(h,tw,oo,exp);mpchecks+=1
records=[];trees=[]
for bi,ib in enumerate(ibs):
 for compact in(False,True):
  tr=source(ib,compact)
  for mi,mp in enumerate(mps):
   tt=s.replace(tr,'1111',mp);rr=s.sites(tt)
   assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
   records.append({'implication_builder':bi,'compact_rho1':compact,
                   'mp_association':mi,'metrics':s.metrics(tt)})
   trees.append(tt)
minimum=min(r['metrics']['dag_nodes']for r in records)
compiled=0
for k,(rec,tr)in enumerate(zip(records,trees)):
 if rec['metrics']['dag_nodes']!=minimum or compiled>=12:continue
 compiled+=1;dd=OUT/f'best{k}';dd.mkdir(exist_ok=True)
 (dd/'sites.json').write_bytes(s.compact(s.sites(tr)))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta
  (dd/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:
  rec['error']=repr(exc);(dd/'candidate.tm').unlink(missing_ok=True)
 (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
summary={'status':'EXPLORATORY_SOURCE_AND_DECODER_ONLY',
 'codec':{'I':'max(0,4P-2)','Q':'4P','R':'4P+1','J':'4P+3','F':1},
 'calibration':'Direct named-formula calibration, not a bijective numeric recoding; old rho6 retained',
 'implication_builder_count':len(ibs),'shifted_scaler_count':len(shifted_scales),
 'finite_builder_checks':builder_checks,'finite_mp_checks':mpchecks,
 'layouts':len(records),'minimum_DAG':minimum,
 'minimum_DAG_zero6':min((r['metrics']['dag_nodes']for r in records if r['metrics']['maximum_zero_run']<=6),default=None),
 'minimum_compiler_count':min((r['compiler']['working_states']for r in records if'compiler'in r),default=None),
 'compiled_minimum_representatives':compiled,'records':records}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items()if k!='records'}),flush=True)
