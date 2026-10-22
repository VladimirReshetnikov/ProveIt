from pathlib import Path
import hashlib,json,re
from urllib.parse import unquote
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');S=Path('/tmp/k215-phase13-root');O=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
m=read(S/'documentation-map.json');assert len(m['files'])==10
links=[];missing=[]
def targets(text):return set(re.findall(r'\[[^\]]*\]\(([^)]+)\)',text))
for row in m['files']:
 p=R/row['path'];assert sha(p)==row['sha256']and p.stat().st_size==row['bytes']
 before=Path('/tmp/k215-phase13-docs/before')/row['path'];prev=targets(before.read_text())if before.is_file()else set()
 for target in sorted(targets(p.read_text())-prev):
  if re.match(r'^[a-zA-Z]+://',target)or target.startswith('#'):continue
  q=(p.parent/unquote(target.split('#')[0])).resolve();entry={'document':row['path'],'target':target,'resolved':str(q),'exists':q.exists()};links.append(entry)
  if not q.exists():missing.append(entry)
assert len(missing)==1 and missing[0]['target']=='lean/README.md'
phase13=R/m['files'][0]['path'];assert 'pending publication; no saved-packet replay is claimed here yet' in phase13.read_text()
incoming=R/'docs/incoming/README.md';old=Path('/tmp/k215-phase13-docs/before/docs/incoming/README.md')
anchor='Batch 212 reconciles';assert incoming.read_text().split(anchor,1)[1]==old.read_text().split(anchor,1)[1]
runs=[Path('/tmp/k215-phase12-import-check/primary-run1'),Path('/tmp/k215-phase13-upstream-check/primary-run1')]
metrics=[]
for run in runs:
 inv=read(run/'inventory.json');rows={r['module']:r for r in inv['modules']};seen=set()
 def visit(n):
  if n=='Init'or n in seen:return
  seen.add(n)
  for d in rows[n]['imports']:visit(d)
 visit('BusyBeaver.ZFC.KEndpoint215');assert len(seen)==179
 size=0
 for n in seen:
  p=run/'workspace'/(n.replace('.','/')+'.lean');assert sha(p)==rows[n]['source_sha256'];size+=p.stat().st_size
 metrics.append(size)
assert metrics==[2129439,2105228]
files=[R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/n for n in ['DominatedImplication.lean','Lukasiewicz.lean']]
assert sum(p.stat().st_size for p in files)==18243 and sum(len(p.read_text().splitlines())for p in files)==401
adopt=read(S/'adoption.json');old=[r for r in adopt['files']if r['target'].endswith('.lean')]
assert sum(r['before_bytes']for r in old)==42454
assert all(sha(R/r['archived_before'])==r['before_sha256']for r in old)
assert sum(len((R/r['archived_before']).read_text().splitlines())for r in old)==811
wc=read(S/'warning-comparison.json');assert wc['status']=='PASS_ALL_FRESH_WARNINGS_PREEXIST'
for row in wc['files']:
 new=read(Path('/tmp/k215-phase13-upstream-check')/row['run']/'completed.json')[row['module']]
 old=read(Path('/tmp/k215-phase12-import-check')/row['run']/'completed.json')[row['module']]
 assert old['source_sha256']==new['source_sha256']==row['unchanged_source_sha256'];assert old['log_sha256']==row['old_log_sha256']and new['log_sha256']==row['new_log_sha256']
 ot=Path(old['log']).read_text();nt=Path(new['log']).read_text();assert sha(old['log'])==old['log_sha256']and sha(new['log'])==new['log_sha256']
 om=[s.split('warning:',1)[1]for s in ot.splitlines()if 'warning:'in s];nm=[s.split('warning:',1)[1]for s in nt.splitlines()if 'warning:'in s];assert om==nm and len(nm)==row['warnings']
assert sum(x['warnings']for x in wc['files'])==7
v={'status':'PASS_DOCUMENTATION_SCOPE_WITH_EXPLICIT_PENDING_PACKET_LINK','documentation_map_sha256':sha(S/'documentation-map.json'),'files':m['files'],'new_or_rewritten_local_links':links,'pending_links':missing,'selected_endpoint_bytes':metrics,'selected_endpoint_modules':179,'core_lukas_bytes':[42454,18243],'core_lukas_lines':[811,401],'all_seven_fresh_warning_occurrences_match_phase12':True,'incoming_history_after_current_queue_unchanged':True,'reader_sha256':sha(__file__),'scope':'Bounded read-only prose/new-link/metric/actual-claim review of10 assigned documents. Pending lean packet link is explicit and will require final additive resolution; no compiler, producer or canonical write.'}
(O/'review.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps({'status':v['status'],'sha256':sha(O/'review.json'),'links':len(links),'pending':len(missing)}))
