#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-p73-share91-graph-check';out=Path('/tmp/ordinary13-p73-share91-graph-attempt01-20261111')
def sha(q):return hashlib.sha256(Path(q).read_bytes()).hexdigest()
for n,h in {'README.md':'249052420c8eff6858f6e0f000be0e5c20669e7ef29f7b1c6700df802512098c','run.py':'e0fc1c173d3c53df58befb90aa87dbf0926b471a3800cc7a56337e6dcf3972a2','plan.json':'436298c31a3d851beaba2a1bbc2c0b7dd27a4a9c41af1871dbcfff696d8a3347','controls.py':'31f8dcb15bcef4f7f7579d84fcb12c01023eaeffc5483b932ba6edf04d3a1cbf','capture_controls.py':'614053577131a1f8f3e3ffa008e19a64929b8933168d9112f89409c59300685f','controls-observation.json':'3e9fa20c1c722592d73072e9aea98009f791d4f5bdd5c79238c5352caafae67a'}.items():assert sha(p/n)==h
assert not os.path.lexists(out)
plan=json.loads((p/'plan.json').read_text());entries=plan['entries'];prefix='DiophantineConsistency.Compact44.'
assert [e['module'] for e in entries]==[prefix+'FreeJ13',prefix+'P73Graph','P73Shared91'] and [len(e['reports']) for e in entries]==[12,12,3]
for e in entries:
 src=repo/e['source'];assert sha(src)==e['source_sha256']
 imports=[]
 for l in src.read_text().splitlines():
  m=re.match(r'^\s*import\s+([^\n-]+)',l)
  if m:imports.extend(m[1].split())
 reports=re.findall(r'^#print axioms\s+(\S+)',src.read_text(),re.M)
 assert imports==e['imports'] and reports==e['reports'] and len(reports)==len(set(reports))
assert len({x for e in entries for x in e['reports']})==27
roots=[out/'lib',Path('/tmp/p72-current-base-extension-attempt02-20261105/lib'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
assert set(plan['fixed_direct_routes'])=={prefix+'FreeJSumSquares',prefix+'FreeJSignedTransport','Mathlib.Tactic.LinearCombination','Init'}
for n,v in plan['fixed_direct_routes'].items():
 candidates=[q/(n.replace('.','/')+'.olean') for q in roots if (q/(n.replace('.','/')+'.olean')).is_file()]
 assert candidates and str(candidates[0].resolve())==v['realpath'] and sha(candidates[0])==v['sha256']
frozen=json.loads((p/'controls-observation.json').read_text());assert frozen['status']=='NON_LEAN_CONTROLS_RECORDED' and frozen['output_path_absent'] and frozen['controls']['exit_code']==0 and frozen['read_only_inspection']['exit_code']==0 and frozen['guarded_preflight']['exit_code']==1 and 'disk_floor' in frozen['guarded_preflight']['stderr']
for f,h in frozen['source_sha256'].items():assert sha(p/f)==h
def call(*args):return subprocess.run([sys.executable,'-I','-S','-B',*map(str,args)],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
a=call(p/'controls.py');assert a.returncode==0 and not a.stderr
lines=a.stdout.decode().splitlines();x,y=map(json.loads,lines);assert x['status']=='PASS_SYNTHETIC_CONTROLS' and y['status']=='PASS_NON_LEAN_CONTROLS' and y['synthetic_monitor_stop']=='disk_floor' and y['synthetic_child_exit']<0
r=call(p/'run.py','--inspect');assert r.returncode==0 and not r.stderr;obs=json.loads(r.stdout);assert obs['status']=='READ_ONLY_INSPECTION_NOT_LAUNCH_APPROVAL' and obs['stages']==3 and obs['disk_stop_bytes']==5100000000
z=call(p/'run.py','--preflight');assert (z.returncode==0 and json.loads(z.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT') or (z.returncode!=0 and any(a in z.stderr.decode() for a in ('disk_floor','host_memory_floor','total_timeout')))
assert not os.path.lexists(out)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','stages':3,'axiom_report_names':27,'synthetic_controls':'PASS','inspection_resource_refusal':obs['resource_refusal'],'fresh_inspection_disk_bytes':obs['disk_free'],'guarded_preflight_exit':z.returncode,'guarded_preflight_refusal':z.stderr.decode().splitlines()[0] if z.returncode else None,'output_path_absent':True,'scope':'No Lean launched; validated runner design and non-Lean controls, not build readiness or theorem success.'},indent=2))
