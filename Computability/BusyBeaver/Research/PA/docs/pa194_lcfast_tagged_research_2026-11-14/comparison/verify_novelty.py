#!/usr/bin/env python3
"""Compare new tables to all139 current spanning194 graphs by exact canonical tuples.

python3 verify_novelty.py candidate.tm [other_candidate.tm ...] --output receipt.json
Only Python standard library; no repository needed after representatives are prepared.
"""
from pathlib import Path
import json,hashlib,argparse
from audit_inventory import parse,rooted,digest
BASE=Path(__file__).resolve().parent

def canonical(data):
 rows,states,start,declared=parse(data)
 roots=[q for q in states if rooted(rows,states,q)[1]==len(states)]
 if not roots:return None
 return min(rooted(rows,states,q,m,f,1)[0]for q in roots for m in (0,1)for f in(0,1))

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('candidate',nargs='+',type=Path);ap.add_argument('--output',type=Path,default=BASE/'fresh_novelty.json');a=ap.parse_args()
 mf=json.loads((BASE/'frontier194_manifest.json').read_text());known=[]
 for r in mf['tables']:
  b=(BASE/r['file']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256']
  c=canonical(b);assert c is not None and len(c)==388;assert digest(c)==r['strong_graph_class'];known.append((r,c))
 results=[];new=[]
 for p in a.candidate:
  b=p.read_bytes();r,states,start,declared=parse(b);c=canonical(b)
  assert c is not None
  matches=[d['class']for d,t in known if t==c]
  results.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'states':len(states),'start':start,'start_declared':declared,'strong_class':digest(c),'historical_matches':matches,'novel':not matches,'exact_tuple':c})
  new.append(c)
 distinct=all(new[i]!=new[j]for i in range(len(new))for j in range(i))
 out={'pin':mf['pin'],'historical_spanning194':len(known),'candidate_results':results,'mutually_distinct':distinct,'comparison':'Exact full BFS tuples minimized over arbitrary spanning roots, global L/R reflection, global0/1 exchange and erased halt-entry decoration. Two historical nonspanning byte forms excluded by the spanning invariant. No cryptographic-collision assumption used in tuple equality.'}
 a.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'historical_spanning194':len(known),'novel':[x['novel']for x in results],'mutually_distinct':distinct,'output':str(a.output)},indent=2))
 assert all(x['novel']for x in results)and distinct
if __name__=='__main__':main()
