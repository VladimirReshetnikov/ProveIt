#!/usr/bin/env python3
"""Read-only audit of gate groups and failed final assembly."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-gates-batched-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-gates-batched-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='fc4e64a0bb36abdff0d51a21e29bebd4d8771f688f9a0a8fc56d700731317e65'
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38GatesAssembly')"
names=[f'Norm38Gates{i:02d}' for i in range(12)]+['Norm38GatesAssembly'];assert [r['module'] for r in s['rows']]==names
assert sha(a/'outer-terminal-author-record.json')=='bc7c2460940f8b86a3f86e6f2c0f61506ecf020b06b6f02e65862dd752e811b0'
outer=json.loads((a/'outer-terminal-author-record.json').read_text());assert outer['outer_session_id']==42976 and outer['outer_exit_code']==1 and 'not independently observed' in outer['observation_kind']
review=D/'reviews/nine-sharing-norm38-gates-batched-independent';z=subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(review/'result.json').read_bytes()
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
warnings=0
for i,r in enumerate(s['rows']):
 n=r['module'];assert sha(q/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']
 for typ in ('deps','compile'):
  m=r[typ];check(a/(n+'-'+typ+'.txt'),m['log_sha256']);check(out/(n+'-'+typ+'.txt'),m['log_sha256']);assert not m['monitor_errors'] and not m['observed_descendant_pids']
 assert r['deps']['exit']==0 and r['deps']['stop_reason'] is None and r['compile']['stop_reason'] is None
 if i<12:
  assert r['compile']['exit']==0;check(out/'lib/DiophantineConsistency'/(n+'.olean'),r['object_sha256']);warnings+=(a/(n+'-compile.txt')).read_text().count('warning:')
 else:assert r['compile']['exit']==1 and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists()
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for v in r['dependencies'].values():check(v['path'],v['sha256'],v['realpath'])
assert sha(a/'Norm38GatesAssembly-compile.txt')=='f3d63406f34662ff384ecab409d95a6252353db1676ffe7f5ee478951e6a1293'
text=(a/'Norm38GatesAssembly-compile.txt').read_text();assert 'error: Application type mismatch' in text and 'gate80 p ports w hp hz' in text and '∀ (a : Gate (Fin 81)), True' in text
print(json.dumps({'status':'PASS_GATE_BATCH_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'outer_author_record_sha256':sha(a/'outer-terminal-author-record.json'),'author_recorded_session':42976,'author_recorded_exit':1,'successful_gate_modules':{r['module']:r['object_sha256'] for r in s['rows'][:12]},'individual_gates':60,'successful_compile_warnings':warnings,'guard_slots':sum(len(r['direct_guard']) for r in s['rows']),'overlay_links':len(s['overlay_links']),'scope':'Retained source/log/object and current direct-guard point checks; no Lean replay or independent historical outer exit.'},indent=2,sort_keys=True))
