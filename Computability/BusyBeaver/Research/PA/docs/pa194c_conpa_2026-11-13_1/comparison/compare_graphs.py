#!/usr/bin/env python3
"""Exact action-labelled rooted/full graph comparison for finite binary tables.

No empirical simulation is involved. Full canonicalization ranges over all
possible roots whose action-directed reachability spans every working state.
For the compared 194-state tables every working state is such a root. Therefore
lexicographic minimization gives an isomorphism invariant of the entire graph,
without choosing a distinguished start. L/R reflection and global bit exchange
are separately optional structural symmetries (bit exchange changes blank 0).
"""
import json,hashlib,argparse
from pathlib import Path

def read_table(path):
 rows={}
 for line in Path(path).read_text().splitlines():
  line=line.strip()
  if not line or line.startswith('#'):continue
  q,a,w,d,t=line.split();q,a,w,t=map(int,(q,a,w,t))
  assert (q,a) not in rows and a in [0,1] and w in [0,1] and d in ['L','R']
  rows[q,a]=(w,0 if d=='L' else 1,t)
 Q={q for q,a in rows};H={v[2] for v in rows.values()}-Q
 assert len(rows)==2*len(Q) and len(H)==1
 return rows,Q,next(iter(H))

def canonical(rows,Q,H,start,mirror=0,complement=0):
 ids={start:0};order=[start];out=[]
 for q in order:
  for a in [0,1]:
   w,d,t=rows[q,a^complement]
   if t in Q and t not in ids:ids[t]=len(ids);order.append(t)
   out.extend([w^complement,d^mirror,len(Q) if t==H else ids[t]])
 return tuple(out),len(order)

def fingerprints(path):
 rows,Q,H=read_table(path);forms={};roots={}
 for mi in [0,1]:
  for co in [0,1]:
   candidates=[]
   for r in sorted(Q):
    c,n=canonical(rows,Q,H,r,mi,co)
    if n==len(Q):candidates.append((c,r))
   assert candidates,'No root spans graph; this canonicalizer does not support this table'
   c,r=min(candidates)
   key=f'mirror{mi}_complement{co}'
   forms[key]=c;roots[key]={'root':r,'spanning_roots':len(candidates)}
 def hs(c):return hashlib.sha256(json.dumps(c,separators=(',',':')).encode()).hexdigest()
 identity=forms['mirror0_complement0']
 return {'path':str(path),'states':len(Q),'rows':len(rows),'byte_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),'rootfree_sha256':hs(identity),'rootfree_reflection_sha256':hs(min(forms['mirror0_complement0'],forms['mirror1_complement0'])),'rootfree_reflection_bitexchange_sha256':hs(min(forms.values())),'spanning_roots':roots['mirror0_complement0']['spanning_roots']},forms

def main():
 ap=argparse.ArgumentParser();ap.add_argument('paths',nargs='+');ap.add_argument('--out');a=ap.parse_args()
 rec=[];forms=[]
 for p in a.paths:
  r,f=fingerprints(p);rec.append(r);forms.append(f)
 pairs=[]
 for i in range(len(rec)):
  for j in range(i+1,len(rec)):
   if rec[i]['states']!=rec[j]['states']:continue
   same= forms[i]['mirror0_complement0']==forms[j]['mirror0_complement0']
   refl= any(forms[i]['mirror0_complement0']==forms[j][f'mirror{m}_complement0'] for m in [0,1])
   allsym= any(forms[i]['mirror0_complement0']==v for v in forms[j].values())
   pairs.append({'left':i,'right':j,'same_full_graph':same,'same_allowing_reflection':refl,'same_allowing_reflection_and_bit_exchange':allsym})
 result={'method':'Exact lexicographic BFS canonical forms over every spanning root; vectors compared directly before hashing','tables':rec,'pairs':pairs}
 if a.out:Path(a.out).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
