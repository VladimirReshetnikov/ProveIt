from pathlib import Path
import hashlib,json,os,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-compatible-forward-rebuild';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';parent=root/'research/trace75-bfs-compatible-reverse-rebuild/observations/attempt01/result.json';po=root/'research/trace75-bfs-compatible-reverse-rebuild/observations/outer-attempt01/terminal.json';plan=root/'research/trace75-bfs-compatible-forward-plan/observations/plan-attempt01/result.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={h/'run.py':'5d611d4a5f06377d6ac5aad46dce3e1123473f8f5c4bb610abbd5ae967d35ffe',h/'run-outer.py':'6466ae90dd81a1dec083668e1e6f1333f2b6ec038b05571b6ac7760faa1572f3',pre/'terminal.json':'b36e7f54e7dac68c86f3d1461bced5a1e3d6012558bbf439684e90dce8e70a60',pol:'306494bddf763b4e9a32fbd1d6942aa6b4a08bc8919b3477d79e4a58251950ef',parent:'9cf2209e033a0baeab5e1ecac3c9aee0f13afffade6c6a716a7661eeff17ba49',po:'c71a9ff6e609126cdbcb6e8bce99e914cbbaefa870827ed7518d5115a63ec55b',plan:'baa12a3a2a04ecfa32e0f925c8a79a4b2f7b520691a6c506a851b6f7a3473199'}
for p,d in pins.items():assert sha(p)==d,p
pr=json.loads(parent.read_text());pt=json.loads(po.read_text());assert pr['status']=='PASS' and pt['exit']==0 and pt['child_status']=='PASS' and pt['child_result_sha256']==pins[parent] and pt['inputs_before']==pt['inputs_after'] and pt['wrapper_sha256_before']==pt['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(1990,81,21) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==22 and all(z['checks'].values())
d=json.loads(plan.read_text());assert len(d['stages'])==21 and len(d['direct'])==42;stage_names=[r['module'] for r in d['stages']];assert len(set(stage_names))==21 and stage_names[-1]=='Trace75BFSModelHalt'
base=Path(pr['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
for row in d['stages']:
 for k in ('source','snapshot','receipt','stdout','stderr'):assert sha(row[k])==row[k+'_sha256']
 assert not os.path.lexists(base/(row['module'].replace('.','/')+'.olean'))
for n,v in d['direct'].items():
 candidates=[p/(n.replace('.','/')+'.olean') for p in (base,pack,core) if os.path.lexists(p/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file();first=candidates[0];assert sha(first)==v['bundle']['.olean']['sha256']==v['old_sha256']
 for suffix,item in v['bundle'].items():
  q=Path(str(first)[:-6]+suffix)
  if item is None:assert not os.path.lexists(q)
  else:assert q.is_file() and sha(q)==item['sha256']
 print(n,'first',first)
outside=json.loads(outbase.read_text());extra=json.loads(ex.read_text());assert extra['module'] not in outside;outside[extra['module']]=extra['record'];assert len(outside)==81
for n,bundle in outside.items():
 p=Path(bundle['.olean']['path']);candidates=[q/(n.replace('.','/')+'.olean') for q in (base,pack,core) if os.path.lexists(q/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0]==p and p.is_file()
 for suffix,v in bundle.items():
  q=Path(str(p)[:-6]+suffix)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve(strict=True))==v['resolved'] and sha(q)==v['sha256']
with tempfile.TemporaryDirectory(prefix='trace75-forward-final-policy-') as tmp:
 p=Path(tmp);[shutil.copyfile(h/n,p/n) for n in ('run.py','test-policy.py')];r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'test-policy.py')],capture_output=True,text=True);assert r.returncode==0,(r.stdout,r.stderr)
print('PASS parent receipts, preflight, 22 actual-function controls, 21 source stages, all 42 direct selections/companions and 81 outside bundles')
