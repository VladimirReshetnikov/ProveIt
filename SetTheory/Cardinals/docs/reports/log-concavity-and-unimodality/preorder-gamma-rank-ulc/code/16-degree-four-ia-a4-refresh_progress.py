"""Refresh a4 progress from independently passed immutable audit receipts."""
from pathlib import Path
import json,collections
O=Path(__file__).parent;D=Path('/workspace/shared/preorder-gamma-degree4/four-attachment')
tasks=sorted(tuple(map(int,l.split())) for l in (D/'face_tasks.tsv').read_text().splitlines())
batches=[O/'small_faces_incremental_audit.json',*sorted(O.glob('medium_checkpoint*_batch_audit.json'))]
global_receipts=sorted(O.glob('global_gap*_receipt.json'));done=set();global_gaps=set()
for path in batches:
 r=json.loads(path.read_text());assert r['verdict'].startswith('complete face mapping approved')
 pending={sid for a in r['coverage'] for sid in a['pending_source_ids']}
 done|={task for sid,task in enumerate(tasks) if task[0] in r['selected_templates'] and sid not in pending}
for path in global_receipts:
 r=json.loads(path.read_text());assert r['verdict'].startswith('listed global integer-population gaps approved')
 for a in r['identities']:global_gaps.add((a['template'],a['gap']))
ordinary_path=O/'ordinary_global_gap_approvals.json'
if ordinary_path.exists():
 ordinary=json.loads(ordinary_path.read_text());assert ordinary['verdict']=='listed ordinary-proof global gap approvals'
 for a in ordinary['gaps']:global_gaps.add((a['template'],a['gap']))
done|={task for task in tasks if task[:2] in global_gaps}
left=set(tasks)-done;complete=[i for i in range(76) if not any(t==i for t,k,m in left)]
r={'scope':('all a4 canonical templates approved for every nonnegative integer population' if not left else 'a4 independently approved results only; full a4 positivity remains open'),'complete_templates':complete,'global_additional_gaps':sorted(global_gaps),'original_tasks':len(tasks),'approved_tasks':len(done),'remaining_tasks':len(left),'remaining_by_gap':dict(collections.Counter(k for t,k,m in left)),'dependencies':['face_orbit_audit.json',*[p.name for p in batches],*[p.name for p in global_receipts],*([ordinary_path.name] if ordinary_path.exists() else [])]}
(O/'incremental_progress.json').write_text(json.dumps(r,indent=2)+'\n');print('Complete:',len(complete),'Remaining:',len(left),'By gap:',r['remaining_by_gap'])
