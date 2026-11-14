#!/usr/bin/env python3
"""Bind all seven role-emitter macros to the pinned Rocq source DAG.
Adapted from supplied U222 audit_source.py's exact finite normalization.
It accepts only identical resolved control edges and commuting adjacent CI.
The all-natural contracts are inherited proved lemmas, not finite simulations.
"""
from pathlib import Path
import argparse,hashlib,json,re
from audit_role_source import cfg,require
RANGES={119:(78,105),121:(52,78),166:(26,52),168:(107,133),180:(78,107),181:(695,723),218:(995,1042)}
LEMMAS={119:'cons119',121:'par121',166:'par166',168:'par168',180:'wal180',181:'wel181',218:'wn218'}
def check(baseline,dag):
 raw=dag.read_bytes();sha=hashlib.sha256(raw).hexdigest()
 require(sha=='ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1','unexpected proof DAG')
 rows=json.loads(baseline.read_text());old=cfg(rows)
 edge=r'(?:ENode|EInc|EDecnz|EBreak|EContinue)\s+\d+|EHalt'
 pattern=re.compile(r'^\s*\|\s*(\d+)\s*=>\s*\(('+edge+r'),\s*('+edge+r')\)\s*$',re.M)
 nodes={int(i):(a,b)for i,a,b in pattern.findall(raw.decode())};require(len(nodes)==487,'incomplete DAG')
 def unfold(e,p,anc):
  z=e.split();kind=z[0]
  if kind=='ENode':
   n=int(z[1]);require(n not in anc and n in nodes,'cyclic or absent node')
   a,b=nodes[n];return unfold(a,p+'0',anc|{n})+unfold(b,p+'1',anc|{n})
  op={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}[kind]
  return [[p,op,None if kind=='EHalt'else int(z[1])]]
 results={}
 for n,lemma in LEMMAS.items():
  lo,hi=RANGES[n];proof=cfg(unfold('ENode '+str(n),'',set()))
  actual=[(o,a,tuple(t-lo for t in dst))for o,a,dst in old[lo:hi]]
  require(len(actual)==len(proof),'wrong macro length')
  require([r[2]for r in actual]==[r[2]for r in proof],('changed CFG',n))
  edits=[];i=0
  while i<len(actual):
   if actual[i]==proof[i]:i+=1;continue
   op,arg,dst=actual[i];po,pa,pd=proof[i]
   if op==po and op in('CB','CC'):
    edits.append({'site':i,'kind':'same resolved jump','actual':arg,'proof':pa});i+=1;continue
   if op==po=='CI'and i+1<len(actual):
    a2,p2=actual[i+1],proof[i+1]
    require(a2[0]==p2[0]=='CI'and arg==p2[1]and pa==a2[1],('noncommuting primitive change',n,i))
    require(dst==(i+1,)and a2[2]==(i+2,),'not straight-line increments')
    require(all(i+1 not in ds for j,(_,_,ds)in enumerate(actual)if j!=i),'jump enters swap interior')
    edits.append({'sites':[i,i+1],'kind':'commuting increments','actual':[arg,a2[1]],'proof':[pa,p2[1]]});i+=2;continue
   raise ValueError(('unproved primitive change',n,i,actual[i],proof[i]))
  results[str(n)]={'lemma':'ProgLibPerm.'+lemma,'range':[lo,hi],'primitive_count':hi-lo,'normalization_steps':edits,'exact_resolved_cfg':True}
 return {'status':'PROVED_MACRO_BINDING_PASS','dag_sha256':sha,'baseline_sha256':hashlib.sha256(baseline.read_bytes()).hexdigest(),'macros':results,'scope':'Finite binding only. Uniform arithmetic contracts are the all-natural named lemmas and their ordinary induction proofs.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('baseline',type=Path);p.add_argument('dag',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
 r=check(a.baseline,a.dag);v=json.dumps(r,indent=2)+'\n'
 if a.output:a.output.write_text(v)
 print(v)
