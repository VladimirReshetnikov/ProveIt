#!/usr/bin/env python3
"""Exact graph novelty against the pinned current194-control corpus.

Allows arbitrary state names, any spanning root, reflection, bit exchange,
and ignored actions on transitions into halt. Global bit exchange is a
structural screen, not a semantic equivalence of zero-blank machines.
"""
from pathlib import Path
import argparse,csv,json,hashlib,re
HERE=Path(__file__).resolve().parent
def parse(raw):
 rows={}
 for line in raw.decode('ascii').splitlines():
  if not line.strip()or line.lstrip().startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in rows
  rows[q,b]=(w,d,n)
 states={q for q,b in rows};assert len(rows)==2*len(states)and all((q,b)in rows for q in states for b in(0,1))
 assert len({n for w,d,n in rows.values()}-states)==1
 return rows,states
def rooted(rows,states,start,mirror=False,flip=False):
 index={start:0};order=[start];out=[]
 for q in order:
  for b in(0,1):
   w,d,n=rows[q,b^flip];w^=flip
   if mirror:d='L'if d=='R'else'R'
   if n in states:
    if n not in index:index[n]=len(index);order.append(n)
    out.append((w,d,index[n]))
   else:out.append((0,'R',-1))
 return tuple(out),len(order)
def check(candidate,comparison=HERE):
 raw=candidate.read_bytes();rows,states=parse(raw);assert len(states)==194
 forms={rooted(rows,states,q,m,f)[0]for q in states if rooted(rows,states,q)[1]==194 for m in(False,True)for f in(False,True)}
 assert forms,'Candidate must have a spanning root'
 checks=[];matches=[]
 for rec in csv.DictReader((comparison/'frontier194_all521.csv').open()):
  p=comparison/rec['representative'];rr=p.read_bytes();assert hashlib.sha256(rr).hexdigest()==rec['sha256'],p
  table,ss=parse(rr);assert len(ss)==194
  for q in sorted(ss):
   tup,n=rooted(table,ss,q)
   if n==194:break
  else:
   checks.append({'table_class':rec['table_class'],'name':rec['name'],'spanning':False,'match':False});continue
  hit=tup in forms
  ans={'table_class':rec['table_class'],'name':rec['name'],'spanning':True,'match':hit};checks.append(ans)
  if hit:matches.append(ans)
 return {'candidate':str(candidate),'candidate_sha256':hashlib.sha256(raw).hexdigest(),'candidate_transformed_root_forms':len(forms),'comparison_tables':len(checks),'spanning_comparison_tables':sum(x['spanning']for x in checks),'matches':matches,'method':'Exact tuple equality; arbitrary state labels/spanning roots, reflection, bit exchange, ignored terminal-edge actions. Bit exchange is structural only.','checks':checks}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('candidate',type=Path,nargs='+');p.add_argument('--comparison',type=Path,default=HERE);p.add_argument('--output',type=Path);a=p.parse_args()
 result=[check(x,a.comparison)for x in a.candidate]
 if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps([{k:v for k,v in x.items()if k!='checks'}for x in result],indent=2))
 assert all(not x['matches']for x in result),'Existing graph match'
