#!/usr/bin/env python3
"""Exact graph comparison; hashes identify files but are not compared as proof.

Compare each new start-rooted table with every possible root in each archived
194-control table, allowing both reflection and global symbol exchange and
ignoring write/move decoration on the unique halt edge. The complement screen
is structural only; it does not preserve the fixed all-zero tape convention.
"""
from pathlib import Path
import json,hashlib,argparse
D=Path(__file__).resolve().parent

def read(p):
 rows={}
 for l in p.read_text().splitlines():
  if not l.strip()or l.lstrip().startswith('#'):continue
  q,b,w,m,n=l.split();rows[int(q),int(b)]=(int(w),1 if m=='R'else-1,int(n))
 states={q for q,b in rows};assert len(states)==194 and len(rows)==388
 assert len({n for w,m,n in rows.values()}-states)==1
 return rows,states

def canonical(r,states,root,reflect=False,complement=False):
 order=[root];ix={root:0};ans=[]
 for q in order:
  for b in(0,1):
   w,m,n=r[q,b^complement]
   if n not in states:ans.append((0,1,-1));continue
   if n not in ix:ix[n]=len(order);order.append(n)
   ans.append((w^complement,-m if reflect else m,ix[n]))
 return tuple(ans)

def main():
 p=argparse.ArgumentParser();p.add_argument('--frontier',type=Path,default=D.parent/'comparison/frontier194');a=p.parse_args()
 candidates=[]
 for name in('PA194AX11H_SF','PA194LC_AX11H_SF'):
  f=D/'machines'/name/'machine.tm';r,s=read(f);sig=canonical(r,s,0);assert len(sig)==388
  candidates.append((name,r,s,sig))
 comparisons=0;matches=[];tablecount=0;spanningtables=0;maxroots=[]
 for f in sorted(a.frontier.glob('*.tm')):
  old,states=read(f);anyspan=False;maxreachable=0
  for root in states:
   sig=canonical(old,states,root);maxreachable=max(maxreachable,len(sig)//2)
   if len(sig)!=388:continue
   anyspan=True
   for reflect in(False,True):
    for complement in(False,True):
     v=canonical(old,states,root,reflect,complement)
     for name,_,__,target in candidates:
      comparisons+=1
      if v==target:matches.append({'candidate':name,'reference':f.name,'root':root,'reflect':reflect,'complement':complement})
  tablecount+=1;spanningtables+=anyspan;maxroots.append((f.name,maxreachable))
 # Cross candidate check under the same stronger symmetries.
 name0,r0,s0,sig0=candidates[0];name1,r1,s1,sig1=candidates[1]
 pair_matches=[]
 for root in s1:
  for mirror in(False,True):
   for bit in(False,True):
    if canonical(r1,s1,root,mirror,bit)==sig0:pair_matches.append((root,mirror,bit))
 result={'status':'PASS'if not matches and not pair_matches else'FAIL','prior_tables':tablecount,'prior_spanning_tables':spanningtables,'nonspanning':[(f,n)for f,n in maxroots if n<194],'exact_tuple_comparisons':comparisons,'matches':matches,'between_candidate_matches':pair_matches,'scope':'Every archived table and all spanning roots, arbitrary labels, reflection, global bit exchange, erased terminal decoration; exact tuples compared.'}
 (D/'novelty.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert result['status']=='PASS'
if __name__=='__main__':main()
