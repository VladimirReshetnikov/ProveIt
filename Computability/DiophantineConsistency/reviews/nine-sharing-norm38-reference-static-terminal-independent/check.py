#!/usr/bin/env python3
"""Read-only audit of the failed static-reference combined-import attempt."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-reference-static-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-static-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='6f98ce113b61aa6989ae43525095ace9018969e630ca3980553b9614e6afdd47'
assert sha(a/'Norm38ReferenceStatic-compile.txt')=='48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a'
assert sha(a/'outer-terminal-author-record.json')=='c8d98f151bdc3df318e9de0c36e013ea8c989baf567726eda4f955bedc85bd20'
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38ReferenceStatic')" and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Norm38ReferenceStatic'
src=q/'src/DiophantineConsistency/Norm38ReferenceStatic.lean';assert sha(src)==sha(out/'src/DiophantineConsistency/Norm38ReferenceStatic.lean')==r['source_sha256']=='994f70fbefebfe77d654ab45dd2de5ef68efcdf20090d80d4dc9e776c3a4a099'
for typ in ('deps','compile'):
 v=r[typ];assert not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(a/('Norm38ReferenceStatic-'+typ+'.txt'))==sha(out/('Norm38ReferenceStatic-'+typ+'.txt'))==v['log_sha256']
assert r['deps']['exit']==0 and r['deps']['stop_reason'] is None
assert r['compile']['exit']==-6 and r['compile']['stop_reason'] is None
assert sha(q/'run.py')=='a2e43339422eb9a1d35e6d9806c93404cf2ad9bb1c37113e43f9e355b56c007e' and "'-M2800'" in (q/'run.py').read_text()
log=(a/'Norm38ReferenceStatic-compile.txt').read_text();assert 'lean::memory_exception' in log and 'excessive memory consumption' in log and "'interpreter'" in log
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency/Norm38ReferenceStatic.olean').exists()
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
expected={'DiophantineConsistency.SharingTopology38':'90661b7bf1e7be709ad2d32e67447e6e05a3d698c975a3e5632566b91fdcca38','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}
for n,h in expected.items():v=r['dependencies'][n];assert v['sha256']==h==sha(v['path']) and str(Path(v['path']).resolve())==v['realpath']
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==91135 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
survey=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_preflight.py')],capture_output=True);assert survey.returncode==0 and not survey.stderr and json.loads(survey.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_FAILED_REFERENCE_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'compile_log_sha256':sha(a/'Norm38ReferenceStatic-compile.txt'),'author_recorded_outer_session':91135,'author_recorded_exit':1,'compile_exit':-6,'monitor_stop':None,'peak_sampled_session_rss_bytes':r['compile']['peak_session_rss_bytes'],'direct_guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Retained source/logs and current point-in-time guards; independent survey is after the failure, not the runner postflight; no Lean replay or independent outer observation.'},indent=2,sort_keys=True))
