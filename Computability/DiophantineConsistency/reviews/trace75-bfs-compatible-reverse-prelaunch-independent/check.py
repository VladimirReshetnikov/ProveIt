from pathlib import Path
import hashlib,json,os,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-compatible-reverse-rebuild'; pre=h/'observations/preflight-attempt01'; pol=h/'observations/policy-attempt01/result.json'; direct=h/'observations/direct-preflight-attempt01/result.json';parent=root/'research/trace75-bfs-compatible-provider-rebuild/observations/attempt01/result.json';po=root/'research/trace75-bfs-compatible-provider-rebuild/observations/outer-attempt01/terminal.json';sp=root/'research/trace75-bfs-compatible-reverse-plan/observations/source-plan-attempt01/result.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={h/'run.py':'ab63a29930ae26f77ffe652ff79c3828188c135dad3de7aa49faecc7fafde60e',h/'run-outer.py':'8c4d04d256de98ca6df83aece66dd0a758186dca945eafccde80e8a0e629c904',pre/'terminal.json':'7cc06a8eee165d76129b28d3d10ef965902332cdebd35e7459e9d84196208ad9',pol:'ab83c1db993d3b1942053d533f77078581157127298d3225847f54991e896168',direct:'182a4d3224c5e6fd257f953452c3680d6a5ff1f5ad30ddbd5d88a04b403e7f59',parent:'04cd437011c9a8b753a310da6c7691f229f9758b9050fdba9b61b812697fbc3c',po:'8714c2ca237d88faa4bc373ed827ede93ee9cb2b4af9d77f0217d5363e3bd964'}
for p,d in pins.items():assert sha(p)==d,p
pr=json.loads(parent.read_text());pt=json.loads(po.read_text());assert pr['status']=='PASS' and pt['exit']==0 and pt['child_status']=='PASS' and pt['child_result_sha256']==pins[parent] and pt['inputs_before']==pt['inputs_after'] and pt['wrapper_sha256_before']==pt['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(1977,81,13) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(sp.read_text()); assert len(plan['stages'])==13;stage_names=[r['module'] for r in plan['stages']];assert len(set(stage_names))==13 and stage_names[-1]=='Trace75BFSHaltGraph'
base=Path(pr['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');
for row in plan['stages']:
 for k in ('source','snapshot','receipt','stdout','stderr'):assert sha(row[k])==row[k+'_sha256']
 assert not os.path.lexists(base/(row['module'].replace('.','/')+'.olean'))
d=json.loads(direct.read_text()); assert len(d['direct'])==15 and not d['changed_historical_hashes']
for n,v in d['direct'].items():
 candidates=[p/(n.replace('.','/')+'.olean') for p in (base,pack,core) if os.path.lexists(p/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and str(candidates[0])==v['path'] and str(candidates[0].resolve())==v['resolved'] and sha(candidates[0])==v['sha256'];print(n,'first',candidates[0])
outside=json.loads(outbase.read_text());extra=json.loads(ex.read_text());assert extra['module'] not in outside;outside[extra['module']]=extra['record'];assert len(outside)==81
for n,bundle in outside.items():
 p=Path(bundle['.olean']['path']);candidates=[q/(n.replace('.','/')+'.olean') for q in (base,pack,core) if os.path.lexists(q/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0]==p and p.is_file()
 for suffix,v in bundle.items():
  q=Path(str(p)[:-6]+suffix)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve(strict=True))==v['resolved'] and sha(q)==v['sha256']
with tempfile.TemporaryDirectory(prefix='trace75-reverse-final-policy-') as tmp:
 p=Path(tmp);[shutil.copyfile(h/n,p/n) for n in ('run.py','test-policy.py')];r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'test-policy.py')],capture_output=True,text=True);assert r.returncode==0,(r.stdout,r.stderr)
print('PASS parent receipts, preflight, 19 actual-function controls, 13 stages, 15 direct selections and all 81 outside bundles')
