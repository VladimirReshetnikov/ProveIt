#!/usr/bin/env python3
"""Exact novelty screen against fresh pinned literal/JSON/recursive-ZIP frontier.
Allows state renaming, any spanning start, tape reflection, symbol exchange,
and erased action decorations on halt-entry edges. This is a graph comparison,
not a blank-start halting equivalence or an arithmetic calibration.
"""
import argparse,collections,importlib.util,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('lit',BASE/'census_tools/literal_inventory.py')
lit=importlib.util.module_from_spec(spec);spec.loader.exec_module(lit)
def profile(data):
 rows,states,_=data;deg=collections.Counter(t for _,_,t in rows.values() if t in states)
 return collections.Counter((deg[q],sum(rows[q,b][2]==q for b in (0,1)),rows[q,0][2]==rows[q,1][2],sum(rows[q,b][2] not in states for b in (0,1))) for q in states)
def canonical(data):
 ans=None
 for q in data[1]:
  for mirror,compl in ((False,False),(True,False),(False,True),(True,True)):
   c=lit.canonical(data,q,mirror,compl)
   if c is None:continue
   c=tuple(tuple((0,'R',t) if t==-1 else (w,d,t) for w,d,t in pair) for pair in c)
   if ans is None or c<ans:ans=c
 return ans
def main():
 if not __debug__: raise SystemExit('Verification requires assertions; run without -O.')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('tables',nargs='+',type=Path);ap.add_argument('--frontier',type=Path,default=BASE);ap.add_argument('--output',type=Path,default=BASE/'novelty_receipt.json');args=ap.parse_args()
 allc=json.loads((args.frontier/'frontier194.json').read_text());summary=json.loads((args.frontier/'summary.json').read_text())
 prior=[]
 for c in allc:
  h=c['normalized_sha256s'][0];path=args.frontier/'tables'/(h+'.tm');d=lit.parse_table(path.read_bytes());assert d is not None
  prior.append((c['table_class'],h,d,profile(d),True))
 for r in summary['nonspanning_frontier_normalized_tables']:
  h=r['normalized_sha256'];d=lit.parse_table((args.frontier/'tables'/(h+'.tm')).read_bytes());assert d is not None
  prior.append(('nonspanning:'+h,h,d,profile(d),False))
 out=[];canonical_cache={};targets=[]
 for path in args.tables:
  data=lit.parse_table(path.read_bytes());assert data is not None and len(data[1])==194
  p=profile(data);target=canonical(data);assert target is not None,'Candidate has no spanning root'
  targets.append((str(path),target))
  records=[];matches=[]
  for cls,h,old,op,spanning in prior:
   if p!=op:
    witness=next(k for k in sorted(set(p)|set(op)) if p[k]!=op[k])
    records.append({'prior_table_class':cls,'different_profile':list(witness),'candidate_multiplicity':p[witness],'prior_multiplicity':op[witness]})
   elif not spanning:
    records.append({'prior_table_class':cls,'reason':'candidate admits a spanning root; prior does not'})
   else:
    if h not in canonical_cache:canonical_cache[h]=canonical(old)
    oc=canonical_cache[h]
    if target==oc:
     matches.append(cls);records.append({'prior_table_class':cls,'match':True})
    else:
     j=next(i for i,(a,b) in enumerate(zip(target,oc)) if a!=b)
     records.append({'prior_table_class':cls,'first_canonical_differing_state':j,'candidate_rows':target[j],'prior_rows':oc[j]})
  out.append({'candidate':str(path),'states':194,'prior_comparisons':len(prior),'known_matches':matches,'new_against_current_recognized_frontier':not matches,'separators':records})
  print(path,'matches',matches,'comparisons',len(prior),flush=True)
 mutual=[]
 for i,(left,a) in enumerate(targets):
  for right,b in targets[i+1:]:
   if a==b:mutual.append({'left':left,'right':right,'same_graph':True})
   else:
    j=next(k for k,(u,v) in enumerate(zip(a,b)) if u!=v)
    mutual.append({'left':left,'right':right,'same_graph':False,'first_canonical_differing_state':j,'left_rows':a[j],'right_rows':b[j]})
 result={'mutual_comparisons':mutual,'pinned_revision':summary['commit'],'scope':__doc__,'frontier_classes':len(allc),'nonspanning_encodings':len(summary['nonspanning_frontier_normalized_tables']),'results':out}
 args.output.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
