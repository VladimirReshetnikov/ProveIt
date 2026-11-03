from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-natural-seed-rebuild';ph=root/'research/trace74-boundary-natural-seed-plan';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';presult=ph/'observations/plan-attempt01/result.json';parentdir=root/'research/trace74-boundary-recurrence-cast-rebuild/observations/attempt02';parent=parentdir/'result.json';po=root/'research/trace74-boundary-recurrence-cast-rebuild/observations/outer-attempt02/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'e1f5921f2cfad151d226950b297f7e0d8b92b80dfcc017b3174bccf0e1abd640',presult:'06ef42a1dfc3aacd417d0ffc533e851f5244a307649207e44b0db6c9a9c116fc',h/'run.py':'f9620254f4ec717c6f2f8e0db155439588b213b198d4618d5b0f139738f4caf9',h/'run-outer.py':'772380f9fa68a24aab910012e1bc91f05d35186573f0ab978c747cda13624296',pre/'terminal.json':'cbc190b38fe8659893612f42dd73fd7d9e934b5724b84d81dc17a5b37ca82622',pol:'f4102d09294a63c03d8e451f36a618047dddbb147671f92cc2e1d6ed4a32e06c',parent:'cce7b3d8df37a80548e4af08f6942a0c354719b7e130a8ce32eef21e4136c3df',po:'050c84caa01ec85c80c9b5cd02b8ac8cf3426ef6729c821f03577071b40f83b8',root/'reviews/trace74-boundary-recurrence-cast-result-independent/README.md':'9ccf37daaf27ecd1a4241463c581d9b27a0e014b0a9db2175aef190758a52b1d'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2027,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==23 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundaryNaturalSeed'] and len(plan['direct'])==1
base=Path(r['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
for i,row in enumerate(rows):
 src=Path(row['source']);assert sha(src)==row['source_sha256'] and not os.path.lexists(base/(row['module']+'.olean'));imports=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M);assert imports==row['imports'] and not set(imports)&set(names[i:]);reports=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M);assert reports==row['reports']==['Trace74BoundaryNaturalSeed.interval','Trace74BoundaryNaturalSeed.slacks']
for n,v in plan['direct'].items():
 candidates=[p/(n.replace('.','/')+'.olean') for p in (base,pack,core) if os.path.lexists(p/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and v['kind']=='project' and str(candidates[0])==v['path'] and str(candidates[0].resolve(strict=True))==v['resolved'] and sha(candidates[0])==v['sha256'];print(n,'first',candidates[0])
outside=json.loads(outbase.read_text());extra=json.loads(ex.read_text());assert extra['module'] not in outside;outside[extra['module']]=extra['record'];assert len(outside)==81
for n,bundle in outside.items():
 p=Path(bundle['.olean']['path']);candidates=[q/(n.replace('.','/')+'.olean') for q in (base,pack,core) if os.path.lexists(q/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0]==p and p.is_file()
 for suffix,v in bundle.items():
  q=Path(str(p)[:-6]+suffix)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve(strict=True))==v['resolved'] and sha(q)==v['sha256']
with tempfile.TemporaryDirectory(prefix='trace74-boundary-final-policy-') as tmp:
 p=Path(tmp);[shutil.copyfile(h/n,p/n) for n in ('run.py','test-policy.py')];q=subprocess.run([sys.executable,'-I','-S','-B',str(p/'test-policy.py')],capture_output=True,text=True);assert q.returncode==0,(q.stdout,q.stderr)
print('PASS source plan, parent/outer, 2027/81/1 preflight, 1 ordered source, 1 first selection, 81 outside bundles and 23 copied actual-function controls')

assert sha(root/'research/trace74-boundary-natural-seed-draft/Trace74BoundaryNaturalSeed.lean')=='d94229597d11921a7fb0a174334b6ff497836301e1a0a39ecbb8020f5a5d33f0'
assert sha(root/'reviews/trace74-boundary-natural-seed-draft-independent/README.md')=='28f05f526b59d46ca28c4801351417064ac4e1ce97ca40fdda980524d868aa6c'
print('PASS reviewed finite natural source and audit pins')
