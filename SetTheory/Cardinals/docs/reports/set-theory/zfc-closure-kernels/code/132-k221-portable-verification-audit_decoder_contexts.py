#!/usr/bin/env python3
"""Diagnose context requirements of retained decoder subtrees using literal rows.
No optimizer imports. Known source-PC bits plus its left sentinel are simulated;
reads outside this finite known region are rejected rather than assumed zero.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,hashlib
from check_grammar_equivalence import validate,need,sha

def table(p):
 rows={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R'),'table row');rows[q,b]=(w,1 if d=='R'else-1,z)
 return rows

def advance(T,q,p,b):
 # Coordinate0 is the current source branch, prefix lies at negative positions.
 tape={i-len(p):int(v)for i,v in enumerate(p)};tape[-len(p)-1]=1;tape[0]=b;before=tape.copy();h=0;trace=[];reads={}
 for step in range(100):
  if h==1:
   return dict(ok=tape==before,state=q,head=h,trace=trace,read_requirements={str(k):v for k,v in sorted(reads.items())if k<0},restored=tape==before)
  if h not in tape:return dict(ok=False,error='unknown_context_read',head=h,state=q,trace=trace)
  v=tape[h];reads.setdefault(h,v)
  if (q,v)not in T:return dict(ok=False,error='missing_row',head=h,state=q,trace=trace)
  w,d,z=T[q,v];trace.append([q,h,v,w,d,z]);tape[h]=w;h+=d;q=z
 return dict(ok=False,error='fuel',head=h,state=q,trace=trace)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 br=json.loads(a.baseline.read_bytes());cr=json.loads(a.candidate.read_bytes());_,_,bt=validate(br);_,_,ct=validate(cr);T=table(a.table)
 leaf=lambda t:isinstance(t[0],str)
 groups=defaultdict(set);meanings=defaultdict(set);oldpaths=defaultdict(list);original_blocks=[]
 def baseline(t,p,q):
  if leaf(t):return
  groups[q].add(t);meanings[t].add(q);oldpaths[q,t].append(p)
  for b,ch in enumerate(t):
   if leaf(ch):continue
   r=advance(T,q,p,b);need(r['ok'],'baseline decoder violated known prefix')
   original_blocks.append((q,t,p,b,ch,r));baseline(ch,p+str(b),r['state'])
 baseline(bt,'',84)
 # A retained subtree might have multiple physical representations. Record all,
 # rather than silently selecting one inverse-map winner.
 failures=[];pass_count=0;pass_requirements=defaultdict(Counter);candidate_paths=defaultdict(list)
 def visit(t,p):
  nonlocal pass_count
  if leaf(t):return
  candidate_paths[t].append(p)
  if t in meanings:
   for q in sorted(meanings[t]):
    for b,ch in enumerate(t):
     if leaf(ch):continue
     r=advance(T,q,p,b);good=r['ok']and ch in groups.get(r.get('state'),set())
     if good:pass_count+=1
     else:
      reqs=[]
      for oq,ot,op,ob,och,orr in original_blocks:
       if oq==q and ot==t and ob==b:
        x=dict(prefix=op,state_after=orr['state'],requirements=orr.get('read_requirements',{}),trace=orr['trace'])
        if x['requirements']not in [v['requirements']for v in reqs]:reqs.append(x)
      failures.append(dict(state=q,bit=b,candidate_prefix=p,actual=r,expected_child_states=sorted(meanings[ch]),original_success_contexts=reqs))
  for b,ch in enumerate(t):visit(ch,p+str(b))
 visit(ct,'')
 # Per-role contracts derive solely from the literal baseline table traces.
 contracts=[]
 for q,t,p,b,ch,r in original_blocks:
  sig=r['read_requirements']
  if sig:
   key=(q,t,b,tuple(sorted(sig.items())))
   if any(x['_key']==key for x in contracts):continue
   contracts.append(dict(_key=key,state=q,bit=b,subtree_sha256=sha(json.dumps(t,separators=(',',':')).encode()),subtree=t,baseline_prefix=p,required_left_bits=sig,minimum_suffix_length=max(-int(i)for i in sig),expected_next_state=r['state']))
 for x in contracts:x.pop('_key')
 # Include shortest distinguishing suffix needed by each old alias role.
 roles=[]
 for q,ts in sorted(groups.items()):
  if len(ts)<2:continue
  for t in ts:
   ps=oldpaths[q,t]
   signatures=sorted({tuple(sorted(r['read_requirements'].items()))for oq,ot,p,b,ch,r in original_blocks if oq==q and ot==t})
   roles.append(dict(state=q,old_prefix_count=len(ps),new_prefix_count=len(candidate_paths.get(t,[])),old_prefix_samples=ps[:5],new_prefix_samples=candidate_paths.get(t,[])[:5],left_read_signatures=[dict(s)for s in signatures]))
 out=dict(status='LITERAL_DECODER_CONTEXT_DIAGNOSIS',baseline_sha256=sha(a.baseline.read_bytes()),candidate_sha256=sha(a.candidate.read_bytes()),table_sha256=sha(a.table.read_bytes()),passed_retained_compound_branches=pass_count,failed_retained_compound_branches=len(failures),failures=failures,alias_roles=roles,compound_context_contracts=contracts,maximum_context_suffix=max((x['minimum_suffix_length']for x in contracts),default=0),scope='Necessary retained-row decoder-context check, not a whole-machine correctness claim. All paths and consulted left-context bits are derived from literal transitions.')
 a.output.write_text(json.dumps(out,indent=2)+'\n');print('passes',pass_count,'failures',len(failures));print(json.dumps(failures[:8],indent=2))
if __name__=='__main__':main()
