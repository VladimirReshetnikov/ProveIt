#!/usr/bin/env python3
"""Read-only review of successful slot groups and failed final assembly."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-slots-batched-retry01';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc'
outer=a/'outer-terminal-author-record.json';assert sha(outer)=='9525d892f120f5a9d24760043f8a02e80063b2ea181743c928139b0afd91011d';o=json.loads(outer.read_text());assert o['outer_session_id']==51237 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38SlotsAssembly')"
names=['Norm38SlotsBase']+[f'Norm38Slots{i:02d}' for i in range(10)]+['Norm38SlotsAssembly'];assert [r['module'] for r in s['rows']]==names
orig=(D/'research/nine-sharing-norm38-slot-extraction-draft/Norm38SlotExtraction.lean').read_text();stmt=lambda text,n:re.search(r'^theorem slot'+f'{n:02d}'+r'\b.*? := by',text,re.M|re.S).group()
for i in range(29):
 src=(q/'src/DiophantineConsistency'/f'Norm38Slots{i//3:02d}.lean').read_text();assert stmt(src,i)==stmt(orig,i)
assert sum(len(re.findall(r'^theorem slot\d\d\b',(q/'src/DiophantineConsistency'/f'Norm38Slots{i:02d}.lean').read_text(),re.M)) for i in range(10))==29
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
warning_count=0
for i,r in enumerate(s['rows']):
 n=r['module'];assert sha(q/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']
 for typ in ('deps','compile'):
  z=r[typ];check(a/(n+'-'+typ+'.txt'),z['log_sha256']);check(out/(n+'-'+typ+'.txt'),z['log_sha256']);assert not z['monitor_errors'] and not z['observed_descendant_pids']
 assert r['deps']['exit']==0 and r['deps']['stop_reason'] is None
 if i<11:
  assert r['compile']['exit']==0 and r['compile']['stop_reason'] is None;check(out/'lib/DiophantineConsistency'/(n+'.olean'),r['object_sha256']);warning_count+=(a/(n+'-compile.txt')).read_text().count('warning:')
 else:
  assert r['compile']['exit']==-15 and r['compile']['stop_reason']=='timeout' and r['compile']['timeout_seconds']==120
  assert (a/(n+'-compile.txt')).read_bytes()==b'' and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists()
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for v in r['dependencies'].values():check(v['path'],v['sha256'],v['realpath'])
print(json.dumps({'status':'PASS_RETAINED_BATCHED_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'author_outer_record_sha256':sha(outer),'author_recorded_outer_session':51237,'author_recorded_outer_exit':1,'passed_modules':{r['module']:r['object_sha256'] for r in s['rows'][:11]},'checked_slot_statements':29,'assembly_stop':'120-second timeout; exit -15; empty log','successful_compile_warnings':warning_count,'guard_slots':sum(len(r['direct_guard']) for r in s['rows']),'overlay_links':len(s['overlay_links']),'scope':'Retained logs, source statements, live provider points; no Lean replay or independently observed outer exit.'},indent=2,sort_keys=True))
