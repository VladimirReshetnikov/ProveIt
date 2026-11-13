#!/usr/bin/env python3
"""Read-only terminal/provider audit for the forward constructor gate batch."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-forward-gates-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-forward-gates-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='42bf82193bf5eef3af518b5a6cffb240ab531975e82fd42afb2e531f675cc07c';assert sha(a/'outer-terminal-author-record.json')=='84245b8a57e7e922968c08bb9deb8aace1735fa41d5a5d0c9f8bcfef140320fb';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==82631 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='1ca0968a7e2acfbd398302581e30f3c02caebcf2a4c81081ba73e0b913ea8b72';names=[f'Norm38ForwardGates{i:02d}' for i in range(12)]+['Norm38ForwardGatesAssembly'];assert [r['module'] for r in s['rows']]==names
review=D/'reviews/nine-sharing-norm38-forward-gates-independent';z=subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(review/'result.json').read_bytes()
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
def guards(g):
 for p,v in g.items():
  if v is None:assert not os.path.lexists(p)
  else:check(p,v['sha256'],v['realpath'])
for p,v in s['overlay_links'].items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
warnings=0
for row in s['rows']:
 n=row['module'];assert sha(q/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']
 for typ in ('deps','compile'):
  z=row[typ];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];check(a/(n+'-'+typ+'.txt'),z['log_sha256']);check(out/(n+'-'+typ+'.txt'),z['log_sha256'])
 check(out/'lib/DiophantineConsistency'/(n+'.olean'),row['object_sha256']);guards(row['direct_guard']);warnings+=(a/(n+'-compile.txt')).read_text().count('warning:')
 for v in row['dependencies'].values():check(v['path'],v['sha256'],v['realpath'])
assert s['rows'][-1]['object_sha256']=='70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685' and warnings==50
weighted=R/'nine-sharing-seed38-weighted-retry/attempt01/state.json';assert sha(weighted)=='a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534';w=json.loads(weighted.read_text());assert w['status']=='PASS';base=Path('/tmp/nine-sharing-seed38-weighted-retry-20261105')
for name in ('ForwardWitness38','NormAssignment38'):
 matches=[x for x in w['rows'] if x['module']==name];assert len(matches)==1;r=matches[0];assert r['deps']['exit']==r['compile']['exit']==0
 check(base/'src/DiophantineConsistency'/(name+'.lean'),r['source_sha256']);check(base/'lib/DiophantineConsistency'/(name+'.olean'),r['object_sha256']);guards(r['direct_guard'])
 for typ in ('deps','compile'):check(base/(name+'-'+typ+'.txt'),r[typ]['log_sha256'])
 for x in s['rows'][:12]:
  dep=x['dependencies']['DiophantineConsistency.'+name];assert dep['sha256']==r['object_sha256'];check(dep['path'],dep['sha256'],dep['realpath'])
print(json.dumps({'status':'PASS_FORWARD_GATE_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'assembly_object_sha256':s['rows'][-1]['object_sha256'],'author_recorded_outer_session':82631,'author_recorded_exit':0,'stages':len(names),'individual_gate_facts':60,'successful_compile_warnings':warnings,'guard_slots':sum(len(r['direct_guard']) for r in s['rows']),'overlay_links':len(s['overlay_links']),'scope':'Retained source/logs/objects and direct provider point checks; no Lean replay, axiom report, or independently observed historical outer exit.'},indent=2,sort_keys=True))
