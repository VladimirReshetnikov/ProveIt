#!/usr/bin/env python3
"""Replay and independently audit the ST/U214 source composition.

Tree closure and splicing follow the ProveIt/Wade source framework, as retained
in the U214 packet.  The construction only splices a closed block.  Literal TM
compilation, arbitrary-register runtime, and blank startup are separate checks.
"""
from pathlib import Path
from functools import lru_cache
import argparse,hashlib,json

PINS={
 'u214':'9428a13d4c228e9760e8f546e43527ee5e196ae667ad2386ddabf961b477d083',
 'st215':'212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9',
 'result':'7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00'}

def need(p,why):
 if not p:raise ValueError(why)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def leaf(n):return isinstance(n[0],str)
def parse(rows):
 inst={p:(o,a)for p,o,a in rows};need(len(inst)==len(rows),'Duplicate source address')
 def get(p):return inst[p]if p in inst else(get(p+'0'),get(p+'1'))
 t=get('');need(sites(t)==rows,'Not canonical full source tree');return t
def sites(n,p=''):
 return[[p,*n]]if leaf(n)else sites(n[0],p+'0')+sites(n[1],p+'1')
@lru_cache(None)
def size(n):return 1 if leaf(n)else size(n[0])+size(n[1])
@lru_cache(None)
def boundary(n):
 if leaf(n):
  o,a=n;return(1 if o=='CD'else a if o=='CB'else 0,a if o=='CC'else 0,o=='CH')
 x,y=boundary(n[0]),boundary(n[1]);return max(x[0]-1,y[0],0),max(x[1],y[1]-1,0),x[2]or y[2]
def closed_forest(n,lo,hi):
 out=[]
 def visit(n,i):
  end=i+size(n)
  if end<=lo or hi<=i:return
  if lo<=i and end<=hi:
   need(boundary(n)==(0,0,False),'Selected factor is not closed');out.append(n);return
  need(not leaf(n),'Partial leaf');visit(n[0],i);visit(n[1],i+size(n[0]))
 visit(n,0);need(sum(map(size,out))==hi-lo,'Forest size');return out
def splice(n,lo,hi,new):
 inserted=0
 def visit(n,i):
  nonlocal inserted
  end=i+size(n)
  if end<=lo or hi<=i:return n
  if lo<=i and end<=hi:
   need(boundary(n)==(0,0,False),'Removal of open factor')
   if i==lo:inserted+=1;return new
   return None
  need(not leaf(n),'Partial primitive');x=visit(n[0],i);y=visit(n[1],i+size(n[0]))
  if x is None:
   need(y is None or boundary(y)[:2]==(0,0),'Open right remainder');return y
  if y is None:need(boundary(x)[:2]==(0,0),'Open left remainder');return x
  return x,y
 t=visit(n,0);need(inserted==1,'Not one insertion');return t
def metrics(n):
 ns=set()
 def visit(n):
  if n in ns:return
  ns.add(n)
  if not leaf(n):visit(n[0]);visit(n[1])
 visit(n);ss=sites(n)
 return {'dag_nodes':len(ns),'leaf_occurrences':len(ss),'maximum_depth':max(len(p)for p,o,a in ss),'maximum_zero_run':max(len(x)for p,o,a in ss for x in p.split('1'))}
def graph(rows):
 """Independent ordinal resolver using only leaf intervals and ancestor cuts."""
 bounds={}
 for i,(p,o,a)in enumerate(rows):
  for j in range(len(p)+1):
   pre=p[:j]
   if pre not in bounds:bounds[pre]=[i,i+1]
   else:bounds[pre][1]=i+1
 out=[]
 for i,(p,o,a)in enumerate(rows):
  if o=='CI':dest=(i+1,)
  elif o=='CH':dest=()
  else:
   bit='1'if o=='CC'else'0';level=a if o!='CD'else 1;positions=[j for j,b in enumerate(p)if b==bit]
   need(len(positions)>=level,'Escaping source branch')
   anc=p[:positions[-level]];v=bounds[anc][0 if o=='CC'else 1]%len(rows)
   dest=(v,i+1)if o=='CD'else(v,)
  out.append((o,a,dest))
 return out
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--u214',type=Path,required=True);p.add_argument('--st215',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 raws={'u214':a.u214.read_bytes(),'st215':a.st215.read_bytes()}
 for k,raw in raws.items():need(sha(raw)==PINS[k],'Wrong '+k+' source hash')
 ur,sr=(json.loads(raws[k])for k in('u214','st215'));u,st=map(parse,(ur,sr))
 newparts=closed_forest(u,2885,3659);need(len(newparts)==1,'U214 emitter is not one closed subtree');new=newparts[0]
 oldparts=closed_forest(st,2884,4481);need([size(n)for n in oldparts]==[132,654,652,103,56],'Old emitter forest differs')
 result=splice(st,2884,4481,new);rr=sites(result);raw=(json.dumps(rr,separators=(',',':'))+'\n').encode('ascii')
 need(sha(raw)==PINS['result'],'Unexpected composed source');need(boundary(result)==(0,0,True),'Source not closed')
 ug,sg,rg=map(graph,(ur,sr,rr));delta=-823;f=lambda i:i if i<4481 else i+delta
 # Exact copied-emitter arithmetic and all its resolved control edges.
 for j in range(774):
  o,v,d=ug[2885+j];need(all(2885<=q<=3659 for q in d),'U214 emitter not closed in ordinal CFG')
  need(rg[2884+j]==(o,v,tuple(q-1 for q in d)),'Emitter graph differs')
 # Complete exterior check, not a checksum-only claim.
 exterior=list(range(2884))+list(range(4481,len(sr)))
 for i in exterior:
  o,v,d=sg[i];need(all(not 2884<q<4481 for q in d),'External edge enters removed emitter interior')
  need(rg[f(i)]==(o,v,tuple(f(q)for q in d)),('Exterior graph differs',i))
 # Critical direct-transfer return remains scheduler zero after the splice.
 need(rr[3873]==['00111','CC',3]and rg[3873]==('CC',3,(0,)),'Command return is not scheduler zero')
 need(rr[3874]==['010','CD',1],'S entry context differs');need(rr[3894]==['11101','CH',None],'Single S halt differs')
 m=metrics(result);need(m=={'dag_nodes':197,'leaf_occurrences':3909,'maximum_depth':42,'maximum_zero_run':6},'Metrics differ')
 out=a.output;out.mkdir(parents=True,exist_ok=True);(out/'sites.json').write_bytes(raw)
 report={'status':'EXACT_ST_U214_SOURCE_COMPOSITION_PASS','input_sha256':{k:sha(v)for k,v in raws.items()},'source_sha256':sha(raw),'metrics':m,'old_ST_emitter_interval':[2884,4481],'copied_U214_emitter_interval':[2885,3659],'new_emitter_interval':[2884,3658],'emitter_primitives':774,'retained_exterior_primitives':len(exterior),'old_closed_forest_leaf_counts':[size(n)for n in oldparts],'command_return':{'ordinal':3873,'address':'00111','target':0},'direct_S_entry':{'ordinal':3874,'address':'010'},'single_halt':{'ordinal':3894,'address':'11101'},'runtime_cases':sum(2 if o=='CD'else 1 for p,o,a in rr),'scope':'Exact source reconstruction and complete copied/exterior CFG comparison. Physical table, unbounded primitive runtime, blank startup, strong compiler, and U/PA consistency calibration are separate obligations.'}
 (out/'source_receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
