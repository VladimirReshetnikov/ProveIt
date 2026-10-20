"""Read-only Git/member comparison, not checksum-manifest validation."""
from pathlib import Path
import collections,hashlib,io,json,subprocess,zipfile
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');OUT=Path(__file__).parent
MAP='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake187-placement.json'
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def obj(ref,path):return git('rev-parse',f'{ref}:{path}').decode().strip()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
commit=git('rev-parse','99fbf38bbd').decode().strip();p=json.loads(git('show',f'{commit}:{MAP}'))
plan=json.loads(Path('/tmp/zfc-intake187/procedure-all/placement-plan.json').read_text())
assert p['counts']==plan['counts'] and p['manuscript_order']==[141,142,143]
counts=collections.Counter();targets=set();new=set();aliases=0;original_trees=set();conversions=[]
for source,proposal in zip(p['sources'],plan['sources']):
 assert source['archive']==proposal['archive'] and source['arrival']==proposal['arrival']
 data=git('show',source['arrival']+':'+source['archive']);assert blob(data)==source['archive_blob']
 z=zipfile.ZipFile(io.BytesIO(data));members={x.filename:x for x in z.infolist() if not x.is_dir()}
 assert set(members)=={r['member'] for r in source['members']}
 for row,planned in zip(source['members'],proposal['members']):
  assert {k:v for k,v in row.items() if k!='placed_blob'}==planned
  raw=z.read(row['member']);assert len(raw)==row['bytes'] and blob(raw)==row['blob'];counts[row['role']]+=1
  role=row['role']
  if role in ('new','existing-alias','batch-alias'):
   target=row['target'];targets.add(target);expected=row.get('placed_blob',row['blob'])
   assert obj(commit,target)==expected and (ROOT/target).is_file()
   if expected!=row['blob']:conversions.append({'path':target,'original_blob':row['blob'],'placed_blob':expected})
   if role=='new':new.add(target)
  if role=='existing-alias':
   a=row['original_introduction'];assert obj(a['commit'],a['path'])==row['blob'];assert a['placement'] is True
   assert obj(row['current_ref'],row['target'])==row['blob'];original_trees.add(a['commit']);aliases+=1
  if role=='history-alias':
   a=row['history'];assert obj(a['commit'],a['path'])==row['blob'];aliases+=1
 archives={s['archive'] for s in p['sources']}
 changed=[l.split('\t',1) for l in git('diff-tree','--no-commit-id','--name-status','-r',commit).decode().splitlines()]
 assert {f for s,f in changed if s=='D'}==archives
 assert {f for s,f in changed if s=='A'}==new|{MAP}
 assert all(s in ('A','D') for s,f in changed)
 assert not any(x.name.lower().endswith('.zip') for x in (ROOT/'docs/incoming').rglob('*') if x.is_file())
assert dict(counts)==p['counts'] and sum(counts.values())==274
r={'status':'INDEPENDENT_PLACEMENT_TREE_REVIEW_PASS','placement_commit':commit,'member_count':274,'source_numbers':[141,142,143],'counts':dict(counts),'new_files':len(new),'distinct_current_targets':len(targets),'original_placement_trees_rechecked':sorted(original_trees),'original_or_historical_alias_bindings':aliases,'all_arrival_members_and_git_blobs_accounted':True,'all_archive_retirements_exact':True,'current_queue_archives':0,'attribute_conversion_records':conversions,'scope':'Own read-only Git blob/member comparison; no checksum-manifest validation, delivered execution, EOL modification, or repo mutation.','findings':[],'reviewer_source':{'path':str(Path(__file__)),'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}}
(OUT/'placement-review.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
