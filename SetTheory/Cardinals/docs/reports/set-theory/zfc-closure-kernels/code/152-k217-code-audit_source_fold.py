#!/usr/bin/env python3
"""Independent exact finite source/rotation/fold audit; no runtime imports.

Uses only the Python standard library. The all-tape fold proof is finite on
its two represented cells plus an incoming-edge invariant. No finite sample
of natural register values is used or needed for these obligations.
"""
from pathlib import Path
from collections import defaultdict
import json,hashlib,argparse

def need(test,msg):
 if not test:raise ValueError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def table(path):
 out={};start=[]
 for line in path.read_text().splitlines():
  if line.startswith('#! start '):start.append(int(line.split()[-1]))
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in out and b in(0,1)and w in(0,1)and d in('L','R'),'table syntax');out[q,b]=(w,1 if d=='R'else-1,z)
 need(start==[0],'start0');Q={q for q,b in out};need(set(out)=={(q,b)for q in Q for b in(0,1)},'table completeness');need({z for w,d,z in out.values()}-Q=={254},'halt254');return out

def readtree(rows):
 root={}
 for p,o,a in rows:
  n=root
  for x in p:
   need(x in'01'and 'leaf'not in n,'source path');n=n.setdefault(x,{})
  need(not n,'duplicate source leaf');n['leaf']=(o,a)
 def build(n):
  if 'leaf'in n:need(len(n)==1,'leaf branch');return n['leaf']
  need(set(n)=={'0','1'},'full source');return build(n['0']),build(n['1'])
 return build(root)
def leaf(n):return isinstance(n[0],str)
def rows(n,p=''):
 if leaf(n):return[[p,*n]]
 return rows(n[0],p+'0')+rows(n[1],p+'1')
def nodes(n,p=''):
 yield p,n
 if not leaf(n):
  yield from nodes(n[0],p+'0');yield from nodes(n[1],p+'1')
def replace(n,old,new):
 if n==old:return new
 if leaf(n):return n
 return replace(n[0],old,new),replace(n[1],old,new)
def boundary(n):
 if leaf(n):
  o,a=n;return (1,0,False)if o=='CD'else(a,0,False)if o=='CB'else(0,a,False)if o=='CC'else(0,0,o=='CH')
 a,b=boundary(n[0]),boundary(n[1]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2]
def cfg(n):
 rs=rows(n);iv={};j=0
 def intervals(n,p=''):
  nonlocal j
  lo=j
  if leaf(n):j+=1
  else:intervals(n[0],p+'0');intervals(n[1],p+'1')
  iv[p]=(lo,j)
 intervals(n);out=[]
 for i,(p,op,arg)in enumerate(rs):
  nxt=(i+1)%len(rs)
  def unwind(bit,k):
   for h in range(len(p)-1,-1,-1):
    if p[h]==bit:
     k-=1
     if not k:return iv[p[:h]][1]%len(rs)if bit=='0'else iv[p[:h]][0]
   return 0
  dest=[nxt]if op=='CI'else[unwind('0',1),nxt]if op=='CD'else[unwind('0',arg)]if op=='CB'else[unwind('1',arg)]if op=='CC'else[]
  out.append((op,arg,tuple(dest)))
 return out

def allocation(T,tree):
 result=defaultdict(set);prefixes=defaultdict(list);maximum=0
 for p,n in nodes(tree):
  if leaf(n):continue
  tape={-1:1,**{i:int(x)for i,x in enumerate(p)}};before=dict(tape);q,h=84,0
  for step in range(500):
   if h==len(p):break
   need(h in tape,'prefix reads unknown exterior');w,d,q=T[q,tape[h]];tape[h]=w;h+=d
  else:raise ValueError('prefix fuel')
  need(tape==before,'prefix tape preservation');result[q].add(n);prefixes[q].append(p);maximum=max(maximum,step)
 return dict(result),dict(prefixes),maximum

def audit(base,candidate,out):
 old=table(base/'binary/machine/k218.native.tm');T=dict(old);original=readtree(json.loads((base/'source/sites218.json').read_text()));tree=original;oldcfg=cfg(original);oldword=[r[1:]for r in rows(original)];receipts=[]
 for q,r,edge in[(210,188,0),(213,210,0),(201,213,1)]:
  groups,paths,_=allocation(T,tree)
  need(len(groups[q])==len(groups[r])==1,'unique logical roles');n=next(iter(groups[q]));need(not leaf(n[edge])and groups[r]=={n[edge]},'child role binding')
  need([k for k,v in T.items()if v[2]==r]==[(q,edge)],'unique physical child entry')
  need(all(T[z,b][:2]==(b,1)for z in(q,r)for b in(0,1)),'pure decoder rows')
  before=dict(T)
  if edge==0:
   (A,B),C=n;nn=A,(B,C)
   T[q,0]=(0,1,before[r,0][2]);T[q,1]=(1,1,r);T[r,0]=(0,1,before[r,1][2]);T[r,1]=(1,1,before[q,1][2])
  else:
   A,(B,C)=n;nn=(A,B),C
   T[q,0]=(0,1,r);T[q,1]=(1,1,before[r,1][2]);T[r,0]=(0,1,before[q,0][2]);T[r,1]=(1,1,before[r,0][2])
  need(all(boundary(x)==(0,0,False)for x in(A,B,C)),'closed factors')
  tree=replace(tree,n,nn);actual,_,_ =allocation(T,tree)
  expected={z:{replace(x,n,nn)for x in ns}for z,ns in groups.items()};expected[r]={nn[1-edge]}
  need(actual==expected,'complete expected decoder binding after rotation')
  need(cfg(tree)==oldcfg,'exact whole ordinal CFG equality');need([r[1:]for r in rows(tree)]==oldword,'exact primitive word equality')
  receipts.append(dict(q=q,r=r,edge=edge,source_paths=paths[q],factor_leaves=[len(rows(x))for x in(A,B,C)],all_factors_closed=True,whole_CFG_equal=True,whole_word_equal=True,complete_expected_decoder_binding=True))
 need(T==table(candidate/'unfolded218.native.tm'),'independent unfolded table identity');need(rows(tree)==json.loads((candidate/'sites217.json').read_text()),'independent source identity')
 need(T[69,0]==(0,1,105)and T[400,0]==(0,1,104),'distinct zero roles');need(T[69,1]==T[400,1]==(1,1,31),'common one role');need(T[213,0]==(0,1,92)and T[213,1]==(1,1,90),'exposed selector');need(T[92,0]==(0,1,104)and T[90,0]==(0,1,105),'return continuations')
 entry69=[(list(k),list(v))for k,v in T.items()if v[2]==69];entry400=[(list(k),list(v))for k,v in T.items()if v[2]==400]
 need(entry69==[([53,1],[1,1,69])]and entry400==[([224,0],[0,1,400])],'unique origin marker entries')
 U={(q,b):(w,d,69 if z==400 else z)for(q,b),(w,d,z)in T.items()if q!=400};U[69,0]=(0,-1,213)
 need(U==table(candidate/'k217.native.tm'),'independent final table identity');Q={q for q,b in U};need(len(Q)== 217 and len(U)== 434 and 400 not in Q,'217 state census')
 folded_groups,_,_=allocation(U,tree)
 unfolded_groups,_,_=allocation(T,tree)
 folded_expected=defaultdict(set)
 for q,ns in unfolded_groups.items():folded_expected[69 if q==400 else q].update(ns)
 need(folded_groups==dict(folded_expected),'complete final folded decoder binding')
 traces=[]
 for marker,expected in[(0,104),(1,105)]:
  tape={-1:marker,0:0};initial=dict(tape);q,h=69,0;trace=[]
  for j in range(3):
   need(h in tape,'two-cell fold window');b=tape[h];w,d,z=U[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
  need(tape==initial and(q,h)==(expected,1),'exact whole two-cell fold endpoint');traces.append(dict(marker=marker,read=0,steps=3,target=expected,trace=trace))
 for marker in(0,1):
  w,d,z=U[69,1];need((w,d,z)==(1,1,31),'read-one fold branch');traces.append(dict(marker=marker,read=1,steps=1,target=31))
 reach={0};todo=[0]
 for q in todo:
  for bit in(0,1):
   z=U[q,bit][2]
   if z!= 254 and z not in reach:reach.add(z);todo.append(z)
 need(reach==Q,'all states graph reachable')
 result=dict(status='INDEPENDENT_SOURCE_ROTATION_AND_ALL_TAPE_FOLD_PASS',rotations=receipts,entry69=entry69,entry400=entry400,fold_traces=traces,working_states=217,transition_rows=434,all_working_states_graph_reachable=True,complete_final_folded_decoder_binding=True,source_metrics=dict(leaves=len(rows(tree)),distinct_subtrees=len({n for p,n in nodes(tree)}),max_depth=max(len(p)for p,op,a in rows(tree)),maximum_zero_run=max(len(z)for p,op,a in rows(tree)for z in p.split('1'))),sha256={str(p.name):sha(p.read_bytes())for p in[candidate/'k217.native.tm',candidate/'sites217.json',candidate/'unfolded218.native.tm']},proof_scope='Exact source/control-graph and decoder bindings. Final fold has a direct all-initial-tape positive 1/3-step simulation from state0, using the uniquely written predecessor bit; its converse follows by concatenating bounded blocks. Primitive-runtime correctness of rotated parent and blank-start calibration are separate obligations.')
 out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));return result
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--base',type=Path,required=True);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();audit(a.base,a.candidate,a.out)
