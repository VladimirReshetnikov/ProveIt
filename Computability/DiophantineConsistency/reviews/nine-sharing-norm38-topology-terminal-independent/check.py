#!/usr/bin/env python3
"""Read-only audit of the generic topology terminal receipt."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-topology-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-topology-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='ac766e23a56ec4a7c97b8c17d4703b9d20f9081a4af0681987f7c206a7f2d2a0'
assert sha(a/'SharingTopology38-compile.txt')=='7536f517d21b412171c34d6f8975ae580b07e910836f9909dc0809c862597b22' and sha(a/'outer-terminal-author-record.json')=='c167aadfca69264b446dfafe4f8853f9244988fcf9baadffd3a45713c2671726'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['base_state_sha256']=='a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534';r=s['rows'][0];assert r['module']=='SharingTopology38'
source=q/'src/DiophantineConsistency/SharingTopology38.lean';assert sha(source)==sha(out/'src/DiophantineConsistency/SharingTopology38.lean')==r['source_sha256']=='4f65679c11953a056041e244566296c8189145fd252fd4c319d623adc8c14a31'
obj=out/'lib/DiophantineConsistency/SharingTopology38.olean';assert sha(obj)==r['object_sha256']=='90661b7bf1e7be709ad2d32e67447e6e05a3d698c975a3e5632566b91fdcca38'
for typ in ('deps','compile'):
 z=r[typ];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/('SharingTopology38-'+typ+'.txt'))==sha(out/('SharingTopology38-'+typ+'.txt'))==z['log_sha256']
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
dep=r['dependencies']['DiophantineConsistency.NormAssignment38'];assert dep['sha256']=='74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'==sha(dep['path']) and str(Path(dep['path']).resolve())==dep['realpath']
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(a/'SharingTopology38-compile.txt').read_text());assert len(reports)==2
assert reports[0][0]=='DiophantineConsistency.SharingTopology38.ringRun_agrees_of_topological' and {x.strip() for x in reports[0][1].split(',')}=={'propext'}
assert reports[1][0]=='DiophantineConsistency.SharingTopology38.static_assignment_fixed' and {x.strip() for x in reports[1][1].split(',')}=={'propext','Quot.sound'}
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==81522 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
prior=D/'reviews/nine-sharing-norm38-topology-check-independent';z=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(prior/'result.json').read_bytes()
print(json.dumps({'status':'PASS_TOPOLOGY_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'source_sha256':r['source_sha256'],'object_sha256':sha(obj),'author_recorded_outer_session':81522,'outer_exit':0,'axiom_reports':reports,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Retained source/log/object and current direct-provider checks; no Lean replay or independent historical outer exit.'},indent=2,sort_keys=True))
