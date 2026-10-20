#!/usr/bin/env python3
"""Review existing result/prefix data only; do not execute search or simulator."""
from pathlib import Path
from collections import Counter,defaultdict
import gzip,hashlib,json
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
RUNS=[Path('/tmp/k219-two-row-run1'),Path('/tmp/k219-two-row-run2')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
allgroups=set();reviews=[]
for run in RUNS:
 result=json.loads((run/'result.json').read_text())
 assert result['status']=='COMPLETE_BOUNDED_SEARCH' and not result['hits']
 assert sha(run/'rejections.jsonl.gz')==result['rejections_sha256']
 for name,h in result['source_pins'].items():
  p=run/Path(name).name
  assert p.is_file() and sha(p)==h,(p,h)
 controls=json.loads((run/'controls.json').read_text())
 assert controls['status']=='PASS' and controls['all_complete_tables']==576
 assert controls['survivors']==6 and controls['synthesis']['covered_rejections']==570
 assert controls['independent_positive']['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'
 assert controls['independent_positive']['positive_old_new_block_histogram']==[[1,1,448],[3,1,64]]
 assert 'new halt without proved old halt' in controls['independent_negative']
 groups=defaultdict(list)
 with gzip.open(run/'rejections.jsonl.gz','rt') as f:
  for line in f:
   item=json.loads(line);groups[item['seed'],item['keep'],item['drop']].append(item)
 expected={(s,k,d) for s in ('baseline','row157') for k,d in result['pairs']}
 assert set(groups)==expected and not allgroups.intersection(expected)
 allgroups.update(expected)
 rows=[]
 for summary in result['results']:
  key=(summary['seed'],summary['keep'],summary['drop']);records=groups[key]
  path=run/('k219.native.tm' if key[0]=='baseline' else 'k219-row157.native.tm')
  table={}
  for line in path.read_text().splitlines():
   if line and not line.startswith('#'):
    a=line.split();table[int(a[0]),int(a[1])]=(int(a[2]),1 if a[3]=='R' else -1,int(a[4]))
  assert len(table)==438
  states={q for q,b in table};assert key[1] in states and key[2] in states
  targets=(states-{key[2]})|{254};assert len(targets)==219
  actions={(w,d,z) for w in (0,1) for d in (-1,1) for z in targets};assert len(actions)==876
  single=[set(),set()];both=set();empty=False;depths=Counter();count=0
  for x in records:
   a=tuple(None if v is None else tuple(v) for v in x['rows'])
   assert len(a)==2 and all(v is None or v in actions for v in a)
   depth=sum(v is not None for v in a);depths[str(depth)]+=1
   assert x['completions']==876**(2-depth);count+=x['completions']
   if depth==0:assert not empty;empty=True
   elif depth==1:
    b=0 if a[0] is not None else 1;assert a[b] not in single[b];single[b].add(a[b])
   else:assert a not in both;both.add(a)
   failure=x['failure'];q,b=failure['old_row'];word=failure['window']
   assert q in key[1:] and b in (0,1) and 0<=word<2**15 and ((word>>7)&1)==b
  assert not (single[0] and single[1]),'Two perpendicular one-action prefixes overlap'
  assert not empty or len(records)==1
  assert all(a0 not in single[0] and a1 not in single[1] for a0,a1 in both),'Complete table overlaps a shorter prefix'
  assert count==876**2==summary['expected_complete_tables']==summary['covered_rejections']
  assert len(records)==summary['rejection_leaves'] and summary['survivors']==0 and summary['status']=='COMPLETE'
  assert dict(depths)=={k:v for k,v in summary['pruned_by_assigned_count'].items() if v}
  rows.append({'seed':key[0],'keep':key[1],'drop':key[2],'disjoint_rejection_prefixes':len(records),'complete_assignments_covered':count})
 assert len(rows)==len(expected)
 reviews.append({'run':str(run),'result_sha256':sha(run/'result.json'),'stream_sha256':sha(run/'rejections.jsonl.gz'),'elapsed_seconds':result['elapsed_seconds'],'groups':rows})
out={'status':'EXISTING_RESULT_AND_PREFIX_COVERAGE_REVIEW_PASS','findings':[],'reviewer_role':'review_upstream_reflection; independent source peer and literal existing-data audit, no search/simulator rerun.','runs':reviews,'total_seed_pairs':len(allgroups),'total_complete_assignments':sum(x['complete_assignments_covered'] for r in reviews for x in r['groups']),'total_rejection_prefixes':sum(x['disjoint_rejection_prefixes'] for r in reviews for x in r['groups']),'scope':'Every actual logged prefix is in the finite action family; pairwise disjoint prefix cylinders cover all assignments. Failure trajectories were not replayed. Full simulated-prefix soundness relies on reviewed discovery source; no universal surviving candidate exists.','reviewer_source':{'path':str(Path(__file__)),'sha256':sha(Path(__file__))}}
p=Path('/tmp/k219-two-row-publication/result-review.json');p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='runs'},indent=2));print('receipt_sha256',sha(p))
