#!/usr/bin/env python3
"""Odd constructor disambiguation by parities inside the pairing arguments.

All tested codecs preserve truth0 and F1. Exact global formula/variable code
conjugacy is the mathematical calibration; this script measures source and
exploratory decoder costs and checks each builder on bounded examples.
"""
import itertools,json,collections,time
from functools import cache
from pathlib import Path
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'inner_parity_codec219';OUT.mkdir(exist_ok=True)
CI=q.CI;CD=q.CD;CC=q.CC
imp=z.MACRO[119];pop=imp[0];pair=imp[1][0]
scale=(CD(7),((CI(1),CI(1)),CC(2)))
def move(a,b,k=1):
 body=CI(b)if k==1 else(CI(b),CI(b))
 return(CD(a),(body,CC(2)))
def double(r):return(move(r,7,2),move(7,r))
D={1:double(1),6:double(6)}
@cache
def assocs(xs):
 if len(xs)==1:return(xs[0],)
 return tuple((a,bb)for k in range(1,len(xs))for a in assocs(xs[:k])for bb in assocs(xs[k:]))
# Codec tuple is I,R,Q,E; each field tuple means (ma,da,mb,db).
identity=(1,0,1,0);codecset=[]
for axis in[0,1]:
 def fields(ma,da,mb,db):return(ma,da,mb,db)if axis==0 else(mb,db,ma,da)
 # Short R uses an even first coordinate. The odd first coordinate is
 # split by parity of the second coordinate between Q and E.
 for swap in[False,True]:
  r=fields(2,0,1,0);qe=[fields(2,1,2,0),fields(2,1,2,1)]
  if swap:qe.reverse()
  codecset.append((identity,r,*qe))
 # Short Q/E uses an odd first coordinate. The double-even cell is R.
 for short in[2,3]:
  cc=[identity,fields(2,0,2,0),None,None]
  cc[short]=fields(2,1,1,0);cc[5-short]=fields(2,0,2,1);codecset.append(tuple(cc))
assert len(set(codecset))==8
word=tuple(tuple(r[1:])for r in ROWS);iw=q.x.flat(imp)
occ=[]
for i in range(len(word)-len(iw)+1):
 if word[i:i+len(iw)]!=iw:continue
 j=i+len(iw);k=0
 while j+k<len(word)and word[j+k]==CI(1):k+=1
 occ.append((i,j,k))
assert collections.Counter(k for i,j,k in occ)=={0:41,1:12,2:22,3:6}
builders={(i,j):k for i,j,k in occ};tags={j+h:(k,h)for i,j,k in occ for h in range(k)}
def skeleton(n,lo=0):
 hi=lo+len(q.x.flat(n))
 if(lo,hi)in builders:return('B',builders[lo,hi])
 if s.leaf(n):return('T',*tags[lo])if lo in tags else('F',n)
 return('N',skeleton(n[0],lo),skeleton(n[1],lo+len(q.x.flat(n[0]))))
SK=skeleton(OLD)
def literal(f,order,association):
 ma,da,mb,db=f;parts=[pop]
 for r,m,d in((6,ma,da),(1,mb,db))[::1 if order==0 else-1]:
  if m==2:parts.append(D[r])
  if d:parts.append(CI(r))
 parts.extend([pair,scale]);alltrees=assocs(tuple(parts))
 # Assoc0 right comb,1 left comb,2 is the smallest DAG against old source.
 if association==0:return alltrees[0]
 if association==1:return alltrees[-1]
 @cache
 def nodes(n):return frozenset([n])if s.leaf(n)else nodes(n[0])|nodes(n[1])|{n}
 oldnodes=nodes(OLD)
 return min(alltrees,key=lambda t:(len(nodes(t)-oldnodes),s.metrics(t)['maximum_zero_run']))
def build(sk,bs,keepq,keepe):
 kind=sk[0]
 if kind=='F':return sk[1]
 if kind=='B':return bs[sk[1]]
 if kind=='T':
  k,h=sk[1:];return CI(1)if h==({1:0,2:keepq,3:keepe}[k])else None
 a,bb=build(sk[1],bs,keepq,keepe),build(sk[2],bs,keepq,keepe)
 return bb if a is None else a if bb is None else(a,bb)
def P(a,b):return(a+b)*(a+b+1)//2+b
results=[];start=time.time();best=999
for ci,codec in enumerate(codecset):
 for order,assoc in itertools.product(range(2),range(3)):
  bs=[literal(f,order,assoc)for f in codec]
  for f,n in zip(codec,bs):
   ma,da,mb,db=f
   for a,bv,rest in itertools.product(range(4),range(4),range(2)):
    rr=[3,bv,P(a,rest),0,4,5,0,0,8];oo,_=q.sim(n,rr)
    exp=rr.copy();exp[1]=2*P(ma*a+da,mb*bv+db);exp[2]=rest
    assert oo==exp,(ci,order,assoc,f,a,bv,oo,exp)
  for kq,ke in itertools.product(range(2),range(3)):
   tr=build(SK,bs,kq,ke);m=s.metrics(tr)
   rec={'codec_I_R_Q_E':codec,'codec_index':ci,'transform_order':order,'association':assoc,'kept_Q_tag':kq,'kept_E_tag':ke,'metrics':m}
   if m['dag_nodes']<best:best=m['dag_nodes'];print('BEST',rec,flush=True)
   if m['dag_nodes']<=218 and m['maximum_zero_run']<=6:
    name=f'c{ci}_o{order}_a{assoc}_q{kq}_e{ke}';dd=OUT/name;dd.mkdir(exist_ok=True);rr=s.sites(tr);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
    (dd/'sites.json').write_bytes(s.compact(rr))
    try:
     U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
    except Exception as exc:rec['error']=repr(exc)
    (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
   results.append(rec)
 print('CODEC_DONE',ci,'best',best,'seconds',time.time()-start,flush=True)
(OUT/'summary.json').write_text(json.dumps({'tested':len(results),'minimum_DAG':best,'results':results,'seconds':time.time()-start,'builder_cases_per_source':128,'status':'EXACT_CODEC_FAMILY; EXPLORATORY_SOURCE_COST'},indent=2)+'\n')
