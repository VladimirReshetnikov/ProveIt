"""Finite control-suffix classification with universally quantified registers.

Uses exactly the inherited affine rules through atom_orientation.py. A match
to the proposed suffix predicate is finite evidence, not a theorem that the
predicate is complete for all pointer lengths.
"""
from pathlib import Path
import itertools,json,time
import atom_orientation as a

selected={18,51,68,144,145,148}
rows=[]
for name,info in a.source['atoms'].items():
 q=info['state']
 if q not in selected:continue
 leaves=list(a.paths(a.changed(info['ast'])))
 began=time.monotonic();outcomes=[];mismatches=[];first_fail={}
 for n in range(1,9):
  for bits in itertools.product('01',repeat=n):
   prefix=''.join(bits)
   if '0000000' in prefix:continue
   t=a.virtual(prefix,q);a.affine.PADDING=max(64,max(len(prefix+s)for s,op in leaves)+10)
   failure=None;cases=0;skips=0
   for s,op in leaves:
    p=prefix+s
    if '0000000'in p:skips+=1;continue
    try:
     for zero,result in a.check_case(t,p,op):cases+=1
    except Exception as exc:
     failure={'pc':p,'op':op,'error':str(exc)};break
   valid=failure is None
   predicted=(not prefix.endswith('00')) if q==18 else prefix.endswith('0' if q in {51,144,148} else '1')
   if valid!=predicted:mismatches.append({'prefix':prefix,'actual_pass':valid,'predicted_pass':predicted,'failure':failure})
   outcomes.append({'prefix':prefix,'status':'PASS'if valid else'FAIL','primitive_cases_passed':cases,'skipped_paths':skips})
   if failure and prefix[-1]not in first_fail:first_fail[prefix[-1]]={'prefix':prefix,**failure}
 row={'state':q,'source_symbol':a.encode[name],'prefix_lengths':[1,8],'prefix_count':len(outcomes),
      'proposed_predicate':('not ends00'if q==18 else 'ends0'if q in {51,144,148} else'ends1'),
      'mismatches':mismatches,'first_failures_by_last_bit':first_fail,
      'pass_count':sum(x['status']=='PASS'for x in outcomes),'primitive_cases_passed':sum(x['primitive_cases_passed']for x in outcomes),
      'scope':'finite concrete outer prefixes; arbitrary register values and header slack through unchanged inherited affine induction rules',
      'seconds':time.monotonic()-began,'outcomes':outcomes}
 rows.append(row);print(json.dumps({k:v for k,v in row.items()if k!='outcomes'}),flush=True)
Path(__file__).with_name('atomic-suffix-results.json').write_text(json.dumps(rows,indent=2)+'\n')
