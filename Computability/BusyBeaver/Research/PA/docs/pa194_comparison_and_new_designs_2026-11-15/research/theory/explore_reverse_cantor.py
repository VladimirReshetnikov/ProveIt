#!/usr/bin/env python3
"""Replay an unsuccessful reversed-Cantor source design experiment.

This builds an UNVERIFIED 206-control raw candidate and an optimistic local
fold price of 198. It is not a certified 198-state consistency machine.
Only finite source arithmetic regressions are run. No full symbolic physical
simulation or absolute iPRA calibration is asserted for this experiment.

The source resolver and raw-action fold screen are adapted from the attributed
loop-continuation packet. See PROVENANCE.json and retained licenses.
Python standard library only; assertions must remain enabled.
"""
from pathlib import Path
import argparse,collections,functools,hashlib,json
HERE=Path(__file__).resolve().parent
START,HALT=74,254

def tup(t):return tuple(map(tup,t))if isinstance(t,list)else t

def read_table(p):
 r={}
 for line in p.read_text().splitlines():
  if not line.strip()or line.lstrip().startswith('#'):continue
  q,b,w,d,n=line.split();r[int(q),int(b)]=int(w),d=='R',int(n)
 return r

def text_table(r):
 return ''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(r.items()))

def parse_grammar(p):
 g=json.loads(p.read_text())
 def go(t):
  if isinstance(t,list):return tup(t)
  return tuple(go(x)for x in g['rules'][t])if t in g['rules']else t
 return go(g['root'])

def source(nodes,ax,root='node172',append_halt=False):
 sites=[]
 def walk(t,p):
  if isinstance(t,str):return walk(ax if t=='x67'else nodes[t],p)
  if t[0]=='leaf':sites.append((p,t[1],t[2]));return
  walk(t[0],p+'0');walk(t[1],p+'1')
 walk((root,('leaf','halt',None))if append_halt else root,'')
 def locate(p):
  for i,(q,_,_)in enumerate(sites):
   if q.startswith(p)or(p.startswith(q)and set(p[len(q):])<={'0'}):return i
  raise ValueError(('unresolved',p))
 def after(p):
  for i in range(len(p)-1,-1,-1):
   if p[i]=='0':return locate(p[:i]+'1')
  raise ValueError(('source escaped',p))
 def cut(p,b,k):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    k-=1
    if not k:return p[:i]
  raise ValueError(('jump escaped',p,b,k))
 ins=[]
 for p,o,a in sites:
  if o=='inc':v=(o,a,after(p))
  elif o=='dec':v=(o,a,after(cut(p,'0',1)),after(p))
  elif o=='breakTo':v=('jump',after(cut(p,'0',a)))
  elif o=='continueTo':v=('jump',locate(cut(p,'1',a)))
  else:assert o=='halt';v=('halt',)
  ins.append(v)
 return sites,ins

def reachable(rows):
 seen={START};todo=[START]
 for q in todo:
  for b in(0,1):
   n=rows[q,b][2]
   if n!=HALT and n not in seen:seen.add(n);todo.append(n)
 return {k:v for k,v in rows.items()if k[0]in seen}

def local_prices(rows):
 # This is only a nomination screen. It is not a simultaneous-fold proof.
 incoming=collections.defaultdict(set)
 for(q,b),(w,d,n)in rows.items():
  if d and w==b:incoming[n].add(b)
 providers=[collections.defaultdict(list),collections.defaultdict(list)]
 states={q for q,b in rows}
 for h in sorted(states):
  w0,d0,u0=rows[h,0];w1,d1,u1=rows[h,1]
  if w0 or w1!=1 or not d0 or not d1:continue
  for bit in(0,1):
   if(u0,bit)in rows and(u1,bit)in rows:
    providers[bit][rows[u0,bit],rows[u1,bit]].append((h,u0,u1))
 options={};edges=collections.defaultdict(list)
 for a in sorted(q for q in states if incoming[q]=={0}):
  for b in sorted(q for q in states if incoming[q]=={1}):
   opts=[]
   for bit in(0,1):
    if rows[a,bit]==rows[b,bit]:opts.append([rows[a,bit]])
    else:opts.append([(bit,False,h)for h,u0,u1 in providers[bit].get((rows[a,bit],rows[b,bit]),[])if not{a,b}&{h,u0,u1}])
   if all(opts):options[a,b]=opts;edges[a].append(b)
 matching={}
 def aug(a,seen):
  for b in edges[a]:
   if b in seen:continue
   seen.add(b)
   if b not in matching or aug(matching[b],seen):matching[b]=a;return True
  return False
 for a in edges:aug(a,set())
 return [[a,b,[opts[0]for opts in options[a,b]]]for b,a in matching.items()]

def compile_changes(raw,nodes,ax,newnodes,patches):
 @functools.lru_cache(None)
 def expand(t):
  if isinstance(t,str):return expand(ax if t=='x67'else nodes[t])
  if t[0]=='leaf':return t
  return tuple(map(expand,t))
 entries=collections.defaultdict(set);seen=set()
 def walk(t,q):
  t=expand(t)
  if(t,q)in seen:return
  seen.add((t,q));entries[t].add(q)
  if t[0]=='leaf':return
  for bit,c in enumerate(t):
   w,d,n=raw[q,bit]
   if w==bit and d and n!=HALT:walk(c,n)
 walk('node172',84)
 nq={n:next(iter(entries[expand(n)]))for n in nodes if len(entries[expand(n)])==1}
 leaf={'inc':{0:14,1:61,2:56,3:161,4:71,5:63,6:13,7:82,8:39},
       'dec':{0:14,1:41,2:56,3:17,4:144,5:45,6:21,7:62,8:39}}
 rows=dict(raw);sigs={(rows[q,0],rows[q,1]):q for q,_ in rows if q not in[nq[n]for n in patches]};nextq=4000
 def action(t,bit):
  nonlocal nextq
  if isinstance(t,str):
   if t in nq:return bit,True,nq[t]
   t=newnodes[t]
  if t[0]=='leaf':
   if t[1]in leaf:return bit,True,leaf[t[1]][t[2]]
   if t[1]=='continueTo':return(0,False,1)if t[2]==1 else(0,False,16)if t[2]==2 else(1,False,73)
   if t[1]=='breakTo'and t[2]==1:return 0,False,302
   if t[1]=='halt':return bit,True,HALT
   raise ValueError(t)
  acts=action(t[0],0),action(t[1],1)
  if acts in sigs:return bit,True,sigs[acts]
  q=nextq;nextq+=1;rows[q,0],rows[q,1]=acts;sigs[acts]=q
  return bit,True,q
 for n,t in patches.items():
  q=nq[n];rows[q,0],rows[q,1]=action(t[0],0),action(t[1],1)
 return reachable(rows)

def run_macro(nodes,ax,name,regs):
 _,ins=source(nodes,ax,name,True);r=list(regs);pc=0
 for _ in range(100000):
  x=ins[pc]
  if x[0]=='halt':return r
  if x[0]=='jump':pc=x[1]
  elif x[0]=='inc':r[x[1]]+=1;pc=x[2]
  elif r[x[1]]==0:pc=x[2]
  else:r[x[1]]-=1;pc=x[3]
 raise AssertionError(('regression fuel exhausted',name,regs))

def main():
 assert __debug__,'Do not use -O'
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 provenance=json.loads((HERE/'PROVENANCE.json').read_text())
 for name,digest in provenance['files'].items():assert hashlib.sha256((HERE/'inputs'/name).read_bytes()).hexdigest()==digest
 raw=read_table(HERE/'inputs/raw.native.tm');nodes={n:tup(t)for n,t in json.loads((HERE/'inputs/nodes.json').read_text()).items()};ax=parse_grammar(HERE/'inputs/grammar.json')
 inc=lambda r:('leaf','inc',r);dec=lambda r:('leaf','dec',r);cont=lambda r:('leaf','continueTo',r)
 core=((dec(6),(inc(7),(inc(1),cont(3)))),(dec(1),((inc(7),'node37'),cont(3))))
 push=((dec(2),'node9'),'node47')
 nn=dict(nodes);nn['node46']=core;nn['node49']=push
 rr=compile_changes(raw,nodes,ax,nn,{'node46':core,'node49':push});folds=local_prices(rr)
 oldsites,_=source(nodes,ax);sites,ins=source(nn,ax)
 assert len(raw)==402 and len(oldsites)==3673 and len(rr)==412 and len(sites)==3457 and len(folds)==8
 pair=lambda a,b:(a+b)*(a+b+1)//2+b
 for a in range(12):
  for bb in range(12):
   assert run_macro(nn,ax,'node46',[0,bb,0,0,0,0,a,0,0])==[0,0,0,0,0,0,0,pair(bb,a),0]
   assert run_macro(nn,ax,'node49',[0,a,bb,0,0,0,0,0,0])==[0,0,pair(a,bb),0,0,0,0,0,0]
   assert run_macro(nn,ax,'node65',[0,bb,pair(a,4),0,0,0,0,0,0])==[0,4*pair(bb,a),4,0,0,0,0,0,0]
 result={'status':'RESEARCH_ONLY_NOT_A_CERTIFIED_MACHINE','parent_source_sites':len(oldsites),'candidate_source_sites':len(sites),'raw_controls':len(rr)//2,'proposed_folds_not_certified':len(folds),'optimistic_control_price':len(rr)//2-len(folds),'source_regression_cases':432,'grid':'a,b in {0,...,11}, three contracts per pair','arbitrary_input_source_proof_completed':False,'physical_contracts_verified':False,'simultaneous_folds_verified':False,'absolute_calibration_claimed':False,'raw_table_sha256':hashlib.sha256(text_table(rr).encode()).hexdigest(),'states_added':sorted({q for q,_ in rr}-{q for q,_ in raw}),'states_removed':sorted({q for q,_ in raw}-{q for q,_ in rr})}
 args.output.mkdir(parents=True,exist_ok=True)
 (args.output/'candidate_raw_UNVERIFIED.tm').write_text(text_table(rr))
 for name,obj in [('nodes.json',nn),('grammar.tree.json',ax),('proposed_folds_UNVERIFIED.json',folds),('sites.json',sites),('instructions.json',ins),('receipt.json',result)]:
  (args.output/name).write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
