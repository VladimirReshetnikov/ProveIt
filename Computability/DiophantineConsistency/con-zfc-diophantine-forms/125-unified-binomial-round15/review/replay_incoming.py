#!/usr/bin/env python3
"""Explicit independent replay of the exact incoming review payload receipts."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def require(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 receipt=json.loads((ROOT/'review/independent_payload_metrics.json').read_text());results={'status':'PASS','quartics':[],'circuits':[]}
 require(len(receipt['quartics'])==10 and len(receipt['circuits'])==4,'Incoming review coverage')
 for old in receipt['quartics']:
  eq=ROOT/'intake'/old['path'];poly=eq.with_name('polynomial.json')
  if not poly.exists():poly=eq.with_name('expanded_polynomial.json')
  e=json.loads(eq.read_text());p=json.loads(poly.read_text());acc=Counter()
  for row in e['residuals']:
   for c,m in row['terms']:
    require(type(c)==int and len(m)<=2,'Nonquadratic incoming row')
    for d,n in row['terms']:acc[tuple(sorted(m+n))]+=c*d
  acc={m:c for m,c in acc.items() if c};target={tuple(m):c for c,m in p['terms']}
  require(len(target)==len(p['terms']) and target==acc,'Incoming coefficient mismatch')
  used={i for m in acc for i in m};require(used==set(range(old['variables'])),'Incoming variable census')
  require(len(e['residuals'])==old['rows'] and len(acc)==old['terms'] and max(map(len,acc))==old['degree'] and max(map(abs,acc.values()))==old['coefficient_height'],'Incoming metric mismatch')
  require(sha(poly)==old['polynomial_sha256'],'Incoming polynomial pin mismatch');results['quartics'].append(old)
 for old in receipt['circuits']:
  p=ROOT/'intake'/old['path'];d=json.loads(p.read_text());nodes=d['nodes'];live=set();stack=[d['output']]
  while stack:
   i=stack.pop()
   if i in live:continue
   require(type(i)==int and 0<=i<len(nodes),'Incoming node index');live.add(i);n=nodes[i]
   if n[0] in ('add','sub','mul'):
    require(len(n)==3 and all(type(x)==int and 0<=x<i for x in n[1:]),'Incoming graph topology');stack.extend(n[1:])
   else:require(n[0] in ('integer','variable','coefficient'),'Incoming primitive')
  count=Counter(nodes[i][0] for i in live if nodes[i][0] in ('add','sub','mul'))
  vs=sorted(nodes[i][1] for i in live if nodes[i][0]=='variable')
  require(vs==sorted(d['variables']) and len(vs)==old['variables'],'Incoming graph variables')
  require(dict(count)==old['operation_counts'] and sum(count.values())==old['operations'],'Incoming operation count')
  require(sha(p)==old['sha256'],'Incoming graph pin mismatch');results['circuits'].append(old)
 a.output.write_text(json.dumps(results,indent=2)+'\n');print(json.dumps({'status':'PASS','quartics':10,'circuits':4,'checks_remain_active_under_optimization':True}))
if __name__=='__main__':main()
