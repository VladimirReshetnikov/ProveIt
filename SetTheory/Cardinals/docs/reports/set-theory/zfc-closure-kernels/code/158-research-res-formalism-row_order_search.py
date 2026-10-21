#!/usr/bin/env python3
"""Exhaustive 8! axiom-row reorderings in a fixed closed-macro template."""
from pathlib import Path
import os
import sys,json,itertools,time
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve();sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b
root=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,root);q=lambda k:b.sole(g,k)
macros={'a':q(98),'b':q(12),'c':q(166),'I':q(90),'F':q(184)[0],'push':q(19),'readU':q(104),'to1':q(81),'+1':('CI',1)};rev={v:k for k,v in macros.items()}
ranges=[('rho8',135,486),('G',486,895),('rho6',895,1178),('rho5',1178,1474),('rho4',1474,1773),('rho3',1773,2069),('rho2',2069,2419),('rho1',2419,2650)]
positions=[]
def record(t,lo=0,p=''):
 hi=lo+len(s.sites(t))
 if hi<=135 or lo>=2650:return
 if t in rev and lo>=135 and hi<=2650:positions.append((p,rev[t],lo,hi));return
 if s.leaf(t):raise ValueError((p,t,lo,hi))
 record(t[0],lo,p+'0');record(t[1],lo+len(s.sites(t[0])),p+'1')
record(root);words=[]
for name,lo,hi in ranges:
 w=[name2 for p,name2,a,bb in positions if lo<=a and bb<=hi];words.append(w)
 assert sum(len(s.sites(macros[x]))for x in w)==hi-lo
print('TOKENS',len(positions),'WORDS',[len(x)for x in words],flush=True)
# Integer baseline grammar.
bnodes=[];bid={};btrees=[]
def base(t):
 key=t if s.leaf(t)else(base(t[0]),base(t[1]))
 if key in bid:return bid[key]
 i=len(bnodes);bid[key]=i;bnodes.append(key);btrees.append(t);return i
broot=base(root);B=len(bnodes);macroIds={k:base(t)for k,t in macros.items()};assert len(bnodes)==B
pm={p:i for i,(p,*_)in enumerate(positions)};templates=[]
def template(t,p=''):
 if p in pm:return('var',pm[p])
 if s.leaf(t):return('const',base(t))
 a,bb=template(t[0],p+'0'),template(t[1],p+'1')
 if a[0]==bb[0]=='const':return('const',bid[(a[1],bb[1])])
 ans=('pair',a,bb);templates.append(ans);return ans
tr=template(root)
def evaluate(word):
 ns=list(bnodes);idx=dict(bid)
 def ins(k):
  if k not in idx:idx[k]=len(ns);ns.append(k)
  return idx[k]
 def realize(t):
  if t[0]=='const':return t[1]
  if t[0]=='var':return macroIds[word[t[1]]]
  return ins((realize(t[1]),realize(t[2])))
 n=realize(tr);seen=set();todo=[n]
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k);z=ns[k]
  if isinstance(z[0],int):todo.extend(z)
 def decode(k):
  z=ns[k];return z if not isinstance(z[0],int)else(decode(z[0]),decode(z[1]))
 return len(seen),lambda:decode(n)
identity=sum(words,[]);assert evaluate(identity)[0]==205
out=HERE/'row-order-search';out.mkdir(exist_ok=True);best=999;best6=999;hist={};start=time.monotonic();records=[]
for trial,perm in enumerate(itertools.permutations(range(8)),1):
 word=sum((words[k]for k in perm),[]);score,decode=evaluate(word);hist[score]=hist.get(score,0)+1
 if score<=min(best,best6):
  t=decode();met=s.metrics(t);assert met['dag_nodes']==score
  if score<best or(met['maximum_zero_run']<=6 and score<=best6):
   d=out/f'candidate{trial:05d}';d.mkdir(exist_ok=True);rr=s.sites(t);assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]
   info=dict(trial=trial,row_order=[ranges[k][0]for k in perm],permutation=perm,metrics=met,seconds=time.monotonic()-start);(d/'sites.json').write_bytes(s.compact(rr));(d/'result.json').write_text(json.dumps(info,indent=2));records.append(info);print('BEST',info,flush=True)
   best=min(best,score)
   if met['maximum_zero_run']<=6:best6=min(best6,score)
 if trial%5000==0:print('PROGRESS',trial,best,best6,round(time.monotonic()-start,3),flush=True)
result=dict(trials=trial,best=best,best6=best6,histogram=hist,records=records,seconds=time.monotonic()-start,scope='All8! row orders in one fixed closed-macro parenthesization template. Same complete axiom set, different stack order; no runtime/startup.')
(out/'result.json').write_text(json.dumps(result,indent=2));print('DONE',trial,best,best6,round(time.monotonic()-start,3),flush=True)
