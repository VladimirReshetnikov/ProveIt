#!/usr/bin/env python3
from pathlib import Path
from collections import defaultdict
import argparse,json,sys,time,hashlib
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description='Audit zero-cost exterior reader rotations of scanner_best196.')
ap.add_argument('--axioms',type=Path,required=True,help='Directory containing symbolic_runtime.py and search/scanner_best196.*')
ap.add_argument('--out',type=Path,default=HERE/'receipt.json')
args=ap.parse_args();BASE=args.axioms
sys.path.insert(0,str(BASE));import symbolic_runtime as rt
src=json.loads((BASE/'search/scanner_best196.sites.json').read_text())
T={}
for ln in(BASE/'search/scanner_best196.native.tm').read_text().splitlines():
 q,b,w,d,n=ln.split();T[int(q),int(b)]=int(w),d=='R',int(n)
oldrows=[(x['path'],x['op'],x['arg'])for x in src]
oldgraph=[tuple(x['instruction'])for x in src]

def tree(rows):
 leaves={p:(op,a)for p,op,a in rows}
 def build(p):
  return ('leaf',)+leaves[p]if p in leaves else(build(p+'0'),build(p+'1'))
 return build('')
def sites(t,p=''):
 return [(p,t[1],t[2])]if t[0]=='leaf'else sites(t[0],p+'0')+sites(t[1],p+'1')
def replace(t,p,u):
 if not p:return u
 side=int(p[0]);ch=list(t);ch[side]=replace(ch[side],p[1:],u);return tuple(ch)
def cfg(rows):
 ints={}
 for i,(p,op,a)in enumerate(rows):
  for j in range(len(p)+1):
   k=p[:j]
   if k not in ints:ints[k]=[i,i]
   else:ints[k][1]=i
 def anc(p,bit,k):
  pos=[i for i,b in enumerate(p)if b==str(bit)]
  if len(pos)<k:raise ValueError('jump exceeds context')
  return p[:pos[-k]]
 out=[]
 for i,(p,op,a)in enumerate(rows):
  if op=='inc':r=('inc',a,i+1)
  elif op=='dec':r=('dec',a,ints[anc(p,0,1)][1]+1,i+1)
  elif op=='continueTo':r=('jump',ints[anc(p,1,a)][0])
  elif op=='breakTo':r=('jump',ints[anc(p,0,a)][1]+1)
  elif op=='halt':r=('halt',)
  else:raise ValueError(op)
  if any(x>=len(rows)for x in(r[2:]if op in('inc','dec')else r[1:]if op!='halt'else[])):raise ValueError('exit whole program')
  out.append(r)
 return out

def prefixmap(table,t):
 groups=defaultdict(list);lookup={};sub={}
 def visit(node,p,q):
  if node[0]=='leaf':return
  groups[q].append(p);lookup[p]=q;sub[p]=node
  for bit in(0,1):
   if node[bit][0]=='leaf':continue
   data=[1]+list(map(int,p))+[bit];old=data.copy();pos=len(data)-1;end=pos+1;now=q
   for tick in range(100):
    if pos==end:break
    if not 0<=pos<end:raise ValueError('unknown prefix')
    if(now,data[pos])not in table:raise ValueError('terminal')
    w,d,now=table[now,data[pos]];data[pos]=w;pos+=1 if d else-1
   if pos!=end or data!=old:raise ValueError('bad prefix')
   visit(node[bit],p+str(bit),now)
 visit(t,'',84);return groups,lookup,sub

def metrics(rows):
 return {'six_zero_addresses':[i for i,(p,op,a)in enumerate(rows)if '000000'in p],
  'six_zero_increment_addresses':[i for i,(p,op,a)in enumerate(rows)if op=='inc'and'000000'in p+'0'],
  'first_path':rows[0][0],'seed_path':rows[25][0],'max_path':max(len(p)for p,op,a in rows)}

def contracts(rows,graph):
 result=[]
 for i,((p,op,a),ins)in enumerate(zip(rows,graph)):
  st=rt.frame(tuple(map(int,p)))
  def fr(n,extra=0,effect=rt.PLAIN):return rt.canonical(rt.frame(tuple(map(int,rows[n][0])),extra,effect))
  if op=='inc':result.append((i,None,st,fr(ins[2],0,('x','inc',rt.PHYSICAL[a]))))
  elif op=='dec':
   result.append((i,(rt.PHYSICAL[a],True),st,fr(ins[2])))
   result.append((i,(rt.PHYSICAL[a],False),st,fr(ins[3],1,('x','dec',rt.PHYSICAL[a]))))
  elif op in('breakTo','continueTo'):result.append((i,None,st,fr(ins[1])))
  else:result.append((i,None,st,None))
 return result

r=tree(oldrows);assert sites(r)==oldrows and cfg(oldrows)==oldgraph
groups,look,sub=prefixmap(T,r);records=[];baseline=metrics(oldrows)
print('BASE',baseline,flush=True)
for p,node in sub.items():
 if p.startswith('10101001'):continue
 q=look[p]
 if groups[q]!=[p]or q in rt.BOXSTATES or not all(T[q,b][:2]==(b,True)for b in(0,1)):continue
 for side in(0,1):
  childp=p+str(side)
  if childp not in look:continue
  child=look[childp]
  if groups[child]!=[childp]or child in rt.BOXSTATES or not all(T[child,b][:2]==(b,True)for b in(0,1)):continue
  if T[q,side][2]!=child:continue
  new=dict(T)
  if side==0:
   (a,b),c=node;replacement=(a,(b,c))
   aa=T[child,0][2];bb=T[child,1][2];cc=T[q,1][2]
   new[q,0]=(0,True,aa);new[q,1]=(1,True,child);new[child,0]=(0,True,bb);new[child,1]=(1,True,cc)
  else:
   a,(b,c)=node;replacement=((a,b),c)
   aa=T[q,0][2];bb=T[child,0][2];cc=T[child,1][2]
   new[q,0]=(0,True,child);new[q,1]=(1,True,cc);new[child,0]=(0,True,aa);new[child,1]=(1,True,bb)
  nr=replace(r,p,replacement);rows=sites(nr)
  try:ng=cfg(rows)
  except ValueError as e:records.append({'p':p,'q':q,'child':child,'side':side,'cfg':'invalid','error':str(e)});continue
  if ng!=oldgraph:records.append({'p':p,'q':q,'child':child,'side':side,'cfg':'different','first_mismatch':next(i for i,(a,b)in enumerate(zip(ng,oldgraph))if a!=b)});continue
  rec={'p':p,'q':q,'child':child,'side':side,'cfg':'identical','metrics':metrics(rows)}
  try:prefixmap(new,nr);rec['prefix_decoder']='pass'
  except ValueError as e:rec['prefix_decoder']='fail';rec['prefix_error']=str(e);records.append(rec);continue
  checks=rt.validate(new,contracts(rows,ng));rec['full_runtime']=checks
  if checks['ok']:
   short=dict(new);short[23,0]=(0,False,75);short.pop((34,0));short.pop((34,1));rec['short_runtime']=rt.validate(short,contracts(rows,ng))
  records.append(rec);print('CANDIDATE',rec,flush=True)
args.out.write_text(json.dumps({'machine_sha256':hashlib.sha256((BASE/'search/scanner_best196.native.tm').read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256((BASE/'search/scanner_best196.sites.json').read_bytes()).hexdigest(),'baseline':baseline,'tested_rotations':len(records),'rotations':records,'scope':'All pure-reader single-occurrence exterior rotations, excluding protected engine controls; exact ordinal CFG and prefix checks followed by full symbolic contracts for survivors. No startup or general lower-bound claim.'},indent=2)+'\n')
print('DONE',len(records),flush=True)
