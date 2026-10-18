#!/usr/bin/env python3
"""Replay every guarded instruction using expanded independent symbolic registers.

The candidate directory supplies machine_old.tm and a logical, complete prefix
source in sites_logical.json. The inherited block/list induction checker is
re-run against the actual table. No source program equivalence is assumed to
follow from this runtime certificate; it needs a separate source proof.

Coverage is reported, not assumed to include every retained transition row.
QT244 leaves (27,1) unused in every symbolic runtime case and in the exact
blank initialization. Keeping an unused row in a total binary table is valid;
complete coverage of source instructions/guards is the correctness obligation.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import argparse,sys,json,time

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
 p=argparse.ArgumentParser();p.add_argument('candidate',type=Path)
 p.add_argument('--reference',type=Path,default=Path(__file__).resolve().parents[1]/'reference/baseline245')
 p.add_argument('--limit',type=int);a=p.parse_args();assert __debug__
 sys.path.insert(0,str(a.reference/'code'))
 import full_symbolic_parametric as F
 T,start=F.rebuild.read_table(a.candidate/'machine_old.tm');assert start==95
 states={q for q,b in T};assert len(T)==2*len(states)
 assert {(q,b)for q in states for b in (0,1)}==set(T)
 assert {q for w,d,q in T.values()}-states=={254}
 sites=json.loads((a.candidate/'sites_logical.json').read_text());trie={}
 for pc,op,r in sites:
  assert isinstance(pc,str)and set(pc)<=set('01')and 1<=len(pc)<=F.PADDING
  assert op in('CI','CD','CB','CC','CH')
  assert (r is None)if op=='CH'else(type(r)is int and r>=0)
  if op in('CI','CD'):assert r<9
  node=trie
  for b in pc:
   assert 'leaf'not in node
   node=node.setdefault(b,{})
  assert not node
  node['leaf']=True
 def full(node):
  assert set(node)=={'leaf'}or set(node)=={'0','1'}
  if 'leaf'not in node:full(node['0']);full(node['1'])
 full(trie)
 F.m.TABLE=T;F.m.prove_blocks();F.m.prove_word_identity()
 counts=Counter();rules=Counter();used=set();records=[];began=time.monotonic()
 expected=sum(2 if op=='CD'else 1 for p,op,r in sites)
 try:
  for i,(pc,op,r)in enumerate(sites):
   for zero in ((True,False)if op=='CD'else(None,)):
    res=F.case(pc,op,r,zero,[[0,9]]*9)
    for trace in res['trace']:
     if 'state'in trace:used.add((trace['state'],trace['read']))
     rules[trace['rule']]+=1
    counts['cases']+=1;counts['symbolic_rules']+=res['rules']
    records.append({'index':i,'pc':pc,'op':op,'r':r,'zero':zero,**{k:v for k,v in res.items()if k!='trace'}})
    if a.limit and counts['cases']>=a.limit:break
   if i%500==0:print('expanded sites',i,'cases',counts['cases'],flush=True)
   if a.limit and counts['cases']>=a.limit:break
 except Exception as err:
  failure={'status':'FAIL','index':i,'pc':pc,'op':op,'r':r,'zero':zero,'error':repr(err),'counts':dict(counts),'seconds':time.monotonic()-began}
  (a.candidate/'expanded-failure.json').write_text(json.dumps(failure,indent=2)+'\n');print(json.dumps(failure),flush=True);raise
 complete=counts['cases']==expected
 if a.limit is None:assert complete
 out={'status':'PASS_UNIVERSAL_EXPANDED_RUNTIME'if complete else'PASS_LIMITED','complete':complete,'working_states':len(states),'source_leaves':len(sites),'expected_cases':expected,'counts':dict(counts),'frame_padding':F.PADDING,'arbitrary_primary_registers':True,'arbitrary_nonempty_finite_spare_suffix':True,'positive_progress_checked':True,'table_sha256':sha256((a.candidate/'machine_old.tm').read_bytes()).hexdigest(),'sites_logical_sha256':sha256((a.candidate/'sites_logical.json').read_bytes()).hexdigest(),'rules':dict(rules),'literal_rows':sorted(used),'unused_runtime_rows':sorted(set(T)-used),'seconds':time.monotonic()-began,'cases':records,'limitation':'Ordinary symbolic-induction proof replay; no new Lean/Rocq endpoint.'}
 (a.candidate/('expanded-runtime.json'if complete else'expanded-limited.json')).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k not in('cases','literal_rows')}),flush=True)
if __name__=='__main__':main()
