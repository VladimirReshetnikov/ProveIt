#!/usr/bin/env python3
"""Independent exhaustive labelled seven-factor partition/degree census."""
import argparse,itertools,json
from collections import Counter
from pathlib import Path
WEIGHTS=(12,78,332,726,898,834,65)
LABELS=('input_geometry_main','input_geometry_auxiliary','input_AND_main','input_AND_auxiliary','history_main','history_auxiliary','loader_checksum')
RETAINED_SOS_DEGREE=1936
if not __debug__:raise RuntimeError('Assertions required')
def partitions(n):
 # Restricted-growth strings: one and only one representative of each set partition.
 def generate(prefix,largest):
  if len(prefix)==n:
   yield tuple(tuple(i for i,b in enumerate(prefix) if b==j) for j in range(largest+1));return
  for b in range(largest+2):yield from generate(prefix+[b],max(largest,b))
 yield from generate([0],0)
def census():
 ps=list(partitions(len(WEIGHTS)));assert len(ps)==877 and len(set(ps))==877
 forms=[];hist=Counter()
 for p in ps:
  g=len(p);hist[g]+=1;weights=tuple(sum(WEIGHTS[i] for i in block) for block in p);cost=509+2*g
  forms.append({'partition':p,'group_weights':weights,'groups':g,'operations':cost,'anchor_group':None,'degree':max(RETAINED_SOS_DEGREE,2*max(weights))})
  for anchor in range(g):
   other=max((weights[j] for j in range(g) if j!=anchor),default=0)
   forms.append({'partition':p,'group_weights':weights,'groups':g,'operations':cost,'anchor_group':anchor,'degree':weights[anchor]+max(RETAINED_SOS_DEGREE,2*other)})
 assert dict(hist)=={1:1,2:63,3:301,4:350,5:140,6:21,7:1}
 assert len(forms)==4140
 minima={g:min(f['degree'] for f in forms if f['groups']==g) for g in range(1,8)}
 points=sorted(set((f['operations'],f['degree']) for f in forms))
 frontier=[(c,d) for c,d in points if not any(cc<=c and dd<=d and (cc<c or dd<d) for cc,dd in points)]
 assert frontier==[(511,4881),(513,3120),(515,2116),(517,1936)]
 frontier_records=[]
 for c,d in frontier:
  optimal=[f for f in forms if f['operations']==c and f['degree']==d]
  frontier_records.append({'operations':c,'degree':d,'number_of_optimal_labelled_forms':len(optimal),'forms':optimal})
 # Independent ordered-block assignment census for every group count. Quotient
 # only by permutations of occupied labels; no recursive partition generation.
 alternative={g:{'degree':None,'optimal_labelled_forms':0} for g in range(1,8)}
 seen=Counter()
 for g in range(1,8):
  # Fix the group of factor0 to0; each unordered partition appears(g-1)! times.
  best=10**9;hits=0
  for assignment in itertools.product(range(g),repeat=6):
   a=(0,)+assignment
   if len(set(a))!=g:continue
   sums=[sum(w for w,b in zip(WEIGHTS,a) if b==j) for j in range(g)]
   degrees=[max(RETAINED_SOS_DEGREE,2*max(sums))]+[sums[j]+max(RETAINED_SOS_DEGREE,2*max((sums[k] for k in range(g) if k!=j),default=0)) for j in range(g)]
   for d in degrees:
    if d<best:best=d;hits=1
    elif d==best:hits+=1
   seen[g]+=1
  factorial=1
  for i in range(1,g):factorial*=i
  assert seen[g]==hist[g]*factorial and hits%factorial==0 and best==minima[g]
  alternative[g]={'degree':best,'optimal_labelled_forms':hits//factorial}
  assert hits//factorial==sum(f['groups']==g and f['degree']==best for f in forms)
 return {'status':'PASS','weights':WEIGHTS,'labels':LABELS,'retained_SOS_exact_degree':RETAINED_SOS_DEGREE,'set_partitions':len(ps),'partitions_by_groups':dict(hist),'complete_finalizer_forms':len(forms),'frontier':frontier_records,'minimum_degree_by_groups':minima,'independent_ordered_assignment_census':alternative,'scope':'Exact optimum within the specified partition/SOS-or-single-anchor family; no global arithmetic-circuit optimality claim.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=census();a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ('status','set_partitions','complete_finalizer_forms','minimum_degree_by_groups','independent_ordered_assignment_census','frontier')},indent=2))
