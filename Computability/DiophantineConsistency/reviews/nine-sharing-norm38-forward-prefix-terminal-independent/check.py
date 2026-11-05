#!/usr/bin/env python3
"""Read-only audit of the checked forward witness prefix."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-forward-prefix-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-forward-prefix-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='71326dc89477d47cca893654dca94000877096b87a28ffd1086649677aa52d71';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['base_state_sha256']=='42bf82193bf5eef3af518b5a6cffb240ab531975e82fd42afb2e531f675cc07c';r=s['rows'][0];assert r['module']=='Norm38ForwardPrefix'
src=q/'src/DiophantineConsistency/Norm38ForwardPrefix.lean';assert sha(src)==sha(out/'src/DiophantineConsistency/Norm38ForwardPrefix.lean')==r['source_sha256']=='9662cd703c6ba4b8e0a164ac57d05223871070bcf1667bfd246c01425c4f6266';obj=out/'lib/DiophantineConsistency/Norm38ForwardPrefix.olean';assert sha(obj)==r['object_sha256']=='aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'
for typ in ('deps','compile'):
 z=r[typ];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/('Norm38ForwardPrefix-'+typ+'.txt'))==sha(out/('Norm38ForwardPrefix-'+typ+'.txt'))==z['log_sha256']
assert (a/'Norm38ForwardPrefix-compile.txt').read_bytes()==b''
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
state=R/'nine-sharing-seed38-weighted-retry/attempt01/state.json';assert sha(state)=='a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534';w=json.loads(state.read_text());x=next(x for x in w['rows'] if x['module']=='ForwardWitness38');assert w['status']=='PASS' and x['deps']['exit']==x['compile']['exit']==0
base=Path('/tmp/nine-sharing-seed38-weighted-retry-20261105');assert sha(base/'src/DiophantineConsistency/ForwardWitness38.lean')==x['source_sha256'] and sha(base/'lib/DiophantineConsistency/ForwardWitness38.olean')==x['object_sha256']=='085639f8f95d4929a0851b4fb2fb8abb68f1cda4a1ee8645dadbcaa92b421b6b'
for typ in ('deps','compile'):assert sha(base/('ForwardWitness38-'+typ+'.txt'))==x[typ]['log_sha256']
dep=r['dependencies']['DiophantineConsistency.ForwardWitness38'];assert dep['sha256']==x['object_sha256'] and sha(dep['path'])==dep['sha256'] and str(Path(dep['path']).resolve())==dep['realpath']
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==91908 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
prior=D/'reviews/nine-sharing-norm38-forward-prefix-check-independent';z=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(prior/'result.json').read_bytes()
print(json.dumps({'status':'PASS_FORWARD_PREFIX_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':sha(obj),'author_recorded_outer_session':91908,'outer_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Retained source/log/object and producer point checks; no Lean replay or independent historical outer-session observation.'},indent=2,sort_keys=True))
