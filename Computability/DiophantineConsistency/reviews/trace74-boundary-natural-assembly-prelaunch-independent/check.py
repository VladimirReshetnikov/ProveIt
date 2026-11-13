from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-natural-assembly-rebuild';ph=root/'research/trace74-boundary-natural-assembly-plan';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';presult=ph/'observations/plan-attempt01/result.json';parentdir=root/'research/trace74-boundary-natural-seed-rebuild/observations/attempt01';parent=parentdir/'result.json';po=root/'research/trace74-boundary-natural-seed-rebuild/observations/outer-attempt01/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'2c397dd2788ab1c3c6ef9180b585b2bb0f594ff56ecb33459fde91cdfbc75048',presult:'07faae48c4de89c74de4034490bd5108ecfce5329c63f9728e62be01d4f21eed',h/'run.py':'9e231746a4431db56b063a4beff8c1e8717906a6c0f24035e4aa463b82acb1f7',h/'run-outer.py':'d7a171bda0c3cf56620b0ab3a5664e938b1e63ecaa01371d3c0d7356eb4309fe',pre/'terminal.json':'b3e38d6612a30f70e58cd2c90b0657a13ce013210c35541cf318077c18963c4e',pol:'1afd5d8c612fb383fbefed41714ccc3a53e61cd2ec62fa925666223352bed27c',parent:'f76e0a3263df655f5f35315ff60bbe9d7aeb203f792b156f6c1f3c9aa7f9bb5c',po:'f5bcc7d4c507ef0cf8c46b9f88b7692b59edd43de8e5e7c561fdf5ad73ce0bc6',root/'reviews/trace74-boundary-natural-seed-result-independent/README.md':'ddd6ace8f0d78fcd512d4dbd49534a7feca1277bda03666d9e88b278d3c515e9'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2028,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundaryNaturalAssembly'] and len(plan['direct'])==2
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
print('PASS source plan, parent/outer, 2028/81/1 preflight, 1 ordered source, 2 first selections, 81 outside bundles and 19 copied actual-function controls')

assert sha(root/'research/trace74-boundary-natural-assembly-draft/Trace74BoundaryNaturalAssembly.lean')=='870afa2cd0393b453c5ec7d225e44193293083c0b032e033b70c1627fa4e032c'
assert sha(root/'reviews/trace74-boundary-natural-assembly-draft-independent/README.md')=='d99e8fbc294665f23e5732b032761278b26a3230bccc73b16dcbde7fce3474a3'
print('PASS reviewed assembly source and source audit pins')
