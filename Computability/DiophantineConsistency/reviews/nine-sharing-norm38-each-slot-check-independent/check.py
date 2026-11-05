#!/usr/bin/env python3
"""Read-only source, failed-provider and runner check; never runs Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-norm38-each-slot-check';B=D/'research/nine-sharing-norm38-slots-batched-retry01';T=Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'run.py','78d0525ff975850259ed0b48c0ceae45d627f375e9ab693d67afc2bf8b7356ab'),(P/'source-manifest.json','ad0aded0521481691a4e9e23158053e3634ce6f7b0314f99669378daf6ed2a8c'),(P/'src/DiophantineConsistency/Norm38EachSlot.lean','156374f2612d621b386039b93515a4cf3c3d3f750f15ada1eb3179863d9a5d90'),(B/'attempt01/state.json','5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc'),(B/'attempt01/outer-terminal-author-record.json','9525d892f120f5a9d24760043f8a02e80063b2ea181743c928139b0afd91011d')]:need(sha(p)==h,'pin '+str(p))
need(sha(T/'state.json')==sha(B/'attempt01/state.json'),'base state');state=json.loads((B/'attempt01/state.json').read_text());outer=json.loads((B/'attempt01/outer-terminal-author-record.json').read_text());need(state['status']=='FAILED' and len(state['rows'])==12 and state['failure']=="RuntimeError('compile failed Norm38SlotsAssembly')" and outer['outer_session_id']==51237 and outer['outer_exit_code']==1,'failed state/author exit')
failed=state['rows'][-1];need(failed['module']=='Norm38SlotsAssembly' and failed['deps']['exit']==0 and failed['compile']['exit']==-15 and failed['compile']['stop_reason']=='timeout' and not failed.get('object_sha256'),'failed assembly');need(sha(B/'attempt01/Norm38SlotsAssembly-compile.txt')==sha(T/'Norm38SlotsAssembly-compile.txt')==failed['compile']['log_sha256'],'failed log')
assembly=(B/'src/DiophantineConsistency/Norm38SlotsAssembly.lean').read_text();client=(P/'src/DiophantineConsistency/Norm38EachSlot.lean').read_text();frag=re.search(r'/-- The sum-of-squares theorem supplies.*?(?=\n/-- Proposed extraction)',assembly,re.S).group().rstrip();need(frag in client and len(re.findall(r'^theorem ',client,re.M))==1 and client.startswith('import DiophantineConsistency.Norm38SlotsBase\n'),'client theorem/context')
m=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(m)==1 and m[0]['module']=='DiophantineConsistency.Norm38EachSlot' and m[0]['imports']==re.findall(r'^import ([A-Za-z0-9_.]+)$',client,re.M) and m[0]['source_sha256']==sha(root/m[0]['source']),'client manifest');need(not os.path.lexists(T/'lib/DiophantineConsistency/Norm38EachSlot.olean'),'target collision')
manifest=json.loads((B/'source-manifest.json').read_text())['rows'];guards=0
for i,row in enumerate(state['rows'][:11]):
 n=row['module'];need(n==('Norm38SlotsBase' if i==0 else f'Norm38Slots{i-1:02}') and manifest[i]['module']=='DiophantineConsistency.'+n,'predecessor order');src=T/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==sha(root/manifest[i]['source'])==row['source_sha256']==manifest[i]['source_sha256'] and sha(T/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'producer '+n)
 for kind in ('deps','compile'):
  rec=row[kind];need(rec['exit']==0 and rec['stop_reason'] is None and not rec['monitor_errors'] and not rec['observed_descendant_pids'],'call '+n+kind);need(sha(T/(n+'-'+kind+'.txt'))==sha(B/'attempt01'/(n+'-'+kind+'.txt'))==rec['log_sha256'],'log '+n+kind)
 for path,v in row['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'absence '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
for path,target in state['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
runner=(P/'run.py').read_text();need("base['rows']=base['rows'][:11]" in runner and "base['rows'][-1]['compile']['stop_reason']=='timeout'" in runner and "for row in base['rows']:" in runner,'selection logic');q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','successful_provider_rows':11,'failed_assembly_excluded':True,'producer_guard_slots':guards,'overlay_links':len(state['overlay_links']),'scope':'Source and retained producer point checks; no Lean or complete extraction proof.'},sort_keys=True,indent=2))
