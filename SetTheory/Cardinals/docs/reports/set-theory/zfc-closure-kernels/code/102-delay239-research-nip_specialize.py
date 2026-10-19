"""Re-express current source's NIP gate directly; candidate table awaits routing repair.
The general six-leaf NIP specialization is prior ProveIt Source57/71 work.
New here is its exact source240 instantiation and source-control certificate.
"""
from pathlib import Path
from collections import Counter
import json,hashlib,argparse
B=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--sites',type=Path,default=B.parent/'machines/sites_logical.json')
ap.add_argument('--table',type=Path,default=B.parent/'reference/zfc240_old.tm')
ap.add_argument('--intervals',type=Path,default=B/'reachable_intervals8.json')
ap.add_argument('--output-dir',type=Path,required=True)
args=ap.parse_args();O=args.output_dir;O.mkdir(parents=True,exist_ok=True)
old=json.loads(args.sites.read_text());Q='1110100101';iv=json.loads(args.intervals.read_text());T={}
for line in args.table.read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),d,int(z))
start=next(i for i,row in enumerate(old)if row[0]==Q+'0');assert start==6309 and iv['invariants'][start][6]==[0,0]
check=[row for row in old if row[0]==Q+'0'or row[0].startswith(Q+'10')];cleanup=[row for row in old if row[0].startswith(Q+'11')]
assert len(check)==12 and len(cleanup)==14
newcheck=[[Q+'0'+s,k,a]for s,k,a in [('0','CD',5),('100','CD',5),('10100','CD',5),('10101','CC',1),('1011','CB',1),('11','CH',None)]]
newclean=[[Q+'1'+p[len(Q)+2:],k,a]for p,k,a in cleanup]
new=[row for row in old if not row[0].startswith(Q)]+newcheck+newclean;new.sort();assert len(new)==6449
# Independent control-graph construction uses complete finite binary path integers.
def src(ss):
 leaf={p:(k,a)for p,k,a in ss};pre={p[:i]for p in leaf for i in range(len(p))};assert len(pre)+1==len(leaf)and not pre&leaf.keys()
 assert all(p+b in leaf or p+b in pre for p in pre for b in'01')
 def at(p):
  for i in range(1,len(p)+1):
   if p[:i]in leaf:
    assert set(p[i:])<={'0'};return p[:i]
  while p not in leaf:assert p in pre;p+='0'
  return p
 def inc(p):
  if not p:return''
  x=(int(p,2)+1)%(1<<len(p));return format(x,'0'+str(len(p))+'b')
 def cut(p,bit,n):
  found=[i for i,b in enumerate(p)if b==bit]
  return p[:found[-n]]if len(found)>=n else''
 def go(p,pos=False):
  k,a=leaf[p]
  if k=='CH':return None
  if k=='CI'or(k=='CD'and pos):return at(inc(p))
  if k in('CD','CB'):return at(inc(cut(p,'0',a if k=='CB'else 1)))
  return at(cut(p,'1',a))
 return leaf,at,go
ol,oa,od=src(old);nl,na,nd=src(new)
oldlocal={p for p,k,a in check};newlocal={p for p,k,a in newcheck};mapping={p:p for p in ol if not p.startswith(Q)}
mapping.update({p:Q+'1'+p[len(Q)+2:]for p,k,a in cleanup});mapping[Q+'0']=Q+'00'
checks=0;incoming=[]
for p,r in mapping.items():
 if p==Q+'0':continue
 assert ol[p]==nl[r]
 for pos in((False,True)if ol[p][0]=='CD'else(False,)):
  x,y=od(p,pos),nd(r,pos)
  if x in oldlocal:assert x==Q+'0';incoming.append([p,pos])
  if y in newlocal:assert y==Q+'00'
  assert x in mapping and mapping[x]==y,(p,r,pos,x,y)
  checks+=1
# Normal-form source paths, all other register values represented symbolically.
def step(leaf,dst,p,h,x):
 k,a=leaf[p]
 if k=='CH':return('HALT',h,x)
 assert a in(5,6)if k in('CI','CD')else True
 pos=False
 if k=='CI':
  if a==5:h+=1
  else:x+=1
 elif k=='CD':
  v=h if a==5 else x;pos=v>0
  if pos:
   if a==5:h-=1
   else:x-=1
 return(dst(p,pos),h,x)
def trace(leaf,dst,p,h,x,stop):
 out=[]
 for n in range(1000):
  if p==stop or p=='HALT':return(p,h,x,n,out)
  out.append([p,h,x]);p,h,x=step(leaf,dst,p,h,x)
 raise AssertionError('fuel')
oldexit=cleanup[0][0];newexit=newclean[0][0]
normal=[]
for h in(0,1,2,3,5,9):
 a=trace(ol,od,Q+'0',h,0,oldexit);b=trace(nl,nd,Q+'00',h,0,newexit)
 assert(a[0]=='HALT')==(b[0]=='HALT')==(h==1)
 if h!=1:assert a[1:3]==b[1:3]==(0,0)
 normal.append(dict(initial_H=h,old_steps=a[3],new_steps=b[3],old_trace=a[4],new_trace=b[4]))
# Prove repeated clear-H phase locally: positive decrement +continue lowers H by1
# and restores the same source pointer; zero decrement exits to one break.
oldclear='11101001011001100';newclear=Q+'010100'
assert ol[oldclear]==nl[newclear]==('CD',5)
for leaf,dst,p in((ol,od,oldclear),(nl,nd,newclear)):
 cont=dst(p,True);assert leaf[cont]==('CC',1)and dst(cont)==p
 out=dst(p,False);assert leaf[out]==('CB',1)
# Every unbounded H>=2 follows identical clear-loop recurrence after its fixed
# prefix. The prefix inspection atH2 andH3 fixes affine H-2 through all guards;
# onlyH-dependent guards are positive whileH>=2 or the proved clear loop.
# Exact affine prefix proof for the exhaustive natural cases H=0,H=1,H=2+n.
def affine_prefix(leaf,dst,entry,exit,clear,hn):
 p=entry;hh=hn;xx=(0,0);trace=[]
 for count in range(30):
  if p==exit or p=='HALT' or (p==clear and hn[1]==1):
   return dict(endpoint=p,H=hh,X=xx,steps=count,trace=trace)
  k,a=leaf[p];trace.append(dict(path=p,opcode=k,argument=a,H=hh,X=xx))
  if k=='CH':p='HALT';continue
  positive=False
  if k in('CI','CD'):
   v=hh if a==5 else xx
   if k=='CI':v=(v[0]+1,v[1])
   elif v==(0,0):positive=False
   else:
    assert v[0]>=1,('undecided symbolic guard',p,v)
    positive=True;v=(v[0]-1,v[1])
   if a==5:hh=v
   else:assert a==6;xx=v
  p=dst(p,positive)
 raise AssertionError('affine prefix did not close')
affine=[]
for hn in((0,0),(1,0),(2,1)):
 aa=affine_prefix(ol,od,Q+'0',oldexit,oldclear,hn)
 bb=affine_prefix(nl,nd,Q+'00',newexit,newclear,hn)
 assert aa['H']==bb['H'] and aa['X']==bb['X']==(0,0)
 if hn==(1,0):assert aa['endpoint']==bb['endpoint']=='HALT'
 elif hn==(0,0):assert aa['endpoint']==oldexit and bb['endpoint']==newexit
 else:assert aa['endpoint']==oldclear and bb['endpoint']==newclear and aa['H']==(0,1)
 affine.append(dict(input_H=hn,old=aa,new=bb))
report=dict(status='SOURCE_SPECIALIZATION_WITH_INDUCTIVE_PRECONDITION',source_before_sha256=hashlib.sha256(args.sites.read_bytes()).hexdigest(),entry=Q+'0',precondition='R6=0; R5 arbitrary natural; other registers arbitrary',invariant_certificate='reachable_intervals8.json',entry_interval=iv['invariants'][start],old_leaves=len(old),new_leaves=len(new),outside_commuting_edges=checks,external_entry_edges=incoming,normal_form='Halt iff entryR5=1; otherwise return at corresponding cleanup withR5=R6=0, all other registers unchanged.',clear_loop_induction='At positiveH, CD5;CC1 returns to the same source pointer withH-1. AtH0, CD5 selectsCB1, which exits. Nat induction gives termination and the full register normal form for allH.',exact_affine_prefix_cases=affine,finite_examples=normal,table_status='UNVERIFIED_NIP_LAYOUT_REQUIRES_72_ROUTE_REPAIR')
(O/'source_certificate.json').write_text(json.dumps(report,indent=2)+'\n');(O/'sites_logical.json').write_text(json.dumps(new,indent=2)+'\n')
t=dict(T);t[46,0]=(0,'R',62);t[46,1]=(1,'R',78);t[62,0]=(0,'R',53);t[62,1]=(1,'R',77);t[77,0]=(0,'R',103)
(O/'candidate_unverified_old.tm').write_text('#! start 95\n# Source-specialized candidate; 72 route repair still required.\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(t.items())))
print(json.dumps({k:v for k,v in report.items()if k not in('finite_examples','exact_affine_prefix_cases','entry_interval')},indent=2))
