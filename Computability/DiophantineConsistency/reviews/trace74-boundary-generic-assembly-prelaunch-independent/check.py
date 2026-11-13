from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-generic-assembly-rebuild';ph=root/'research/trace74-boundary-generic-assembly-plan';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';presult=ph/'observations/plan-attempt01/result.json';parentdir=root/'research/trace74-boundary-generic-cast-transfer-rebuild/observations/attempt02';parent=parentdir/'result.json';po=root/'research/trace74-boundary-generic-cast-transfer-rebuild/observations/outer-attempt02/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'335aae4e0ec9225d2a2763283c2a47e204a7918ee9826d6e105724502b8d79ab',presult:'375a76452332ac0bc71c1cce929448e4a2620bd417ffce8f29dbf640e3b43b5f',h/'run.py':'0fb34fc6ff1983604768ef1987e8e5189cf02caac68c2c8c4dcaebc48831ce33',h/'run-outer.py':'b2d3e1479a47d0e675dff2acbfc0dfa77d81daee7a9c0cd03d27ab8185586320',pre/'terminal.json':'de041b946ab91af47e9e380afd30be83839965f4941383b70db8e36a5c9c1738',pol:'c952c5fb9200088ccd33a62169a8045edf64f1e3390617ccf87b1be730c54e37',parent:'ed4232c251d11d84e531b9d06a79f2e490dd3df8fb40f08e00cca6fcae107865',po:'027a818b8edadc367943fb6c17321a08e68566d1023649cc1e3e972241b4dfdf',root/'reviews/trace74-boundary-generic-cast-transfer-result-independent/README.md':'9a20b57ca6b3f77cae0f1c945288cffbda033a06a97106477787b09f9dae87a5'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2029,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundaryGenericAssembly'] and len(plan['direct'])==2
base=Path(r['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
for i,row in enumerate(rows):
 src=Path(row['source']);assert sha(src)==row['source_sha256'] and not os.path.lexists(base/(row['module']+'.olean'));imports=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M);assert imports==row['imports'] and not set(imports)&set(names[i:]);reports=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M);assert reports==[row['report']]
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
print('PASS source plan, parent/outer, 2029/81/1 preflight, 1 ordered source, 2 first selections, 81 outside bundles and 19 copied actual-function controls')

assert sha(root/'research/trace74-boundary-generic-assembly-draft/Trace74BoundaryGenericAssembly.lean')=='06b5a101b3638a13af86e9a20c04c7c338a9cf98c0dba53a7e908cf0c9469835'
assert sha(root/'reviews/trace74-boundary-generic-assembly-draft-independent/README.md')=='e3b1716a5778f73754cc605b14f939ef34a6663ef2bb1ffe166781685f428406'
print('PASS reviewed assembly source and source audit pins')
