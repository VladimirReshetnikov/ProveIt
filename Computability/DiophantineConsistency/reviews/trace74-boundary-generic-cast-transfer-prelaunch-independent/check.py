from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-generic-cast-transfer-rebuild';ph=root/'research/trace74-boundary-generic-cast-transfer-plan';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';presult=ph/'observations/plan-attempt01/result.json';parentdir=root/'research/trace74-boundary-natural-seed-rebuild/observations/attempt01';parent=parentdir/'result.json';po=root/'research/trace74-boundary-natural-seed-rebuild/observations/outer-attempt01/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'bf00464d5a3148d5f9c79b590e9c1c9358efb5c7ce3c2a546755d513660b88ed',presult:'6fce8485f44e145c051963f5392a39db5874c9bdf2d5f759c0916ac24cac65d5',h/'run.py':'4c062c4ece52c2370433d0986d1dc17b421271164e98e5294038fa27ddb58a72',h/'run-outer.py':'529ed7d8b86bf9916fb6c45754043ef35331775a4e29fb8cba0df4e7fee8b155',pre/'terminal.json':'c7d15e3e830c3252967a9029e9237f26370802ee2f8142ab0c0f4be9dc74b1ea',pol:'3039a0fb12e0cbed141db1cc6a6d302f3b0bef391a1b913f37831a5577a0afb2',parent:'f76e0a3263df655f5f35315ff60bbe9d7aeb203f792b156f6c1f3c9aa7f9bb5c',po:'f5bcc7d4c507ef0cf8c46b9f88b7692b59edd43de8e5e7c561fdf5ad73ce0bc6',root/'reviews/trace74-boundary-natural-seed-result-independent/README.md':'ddd6ace8f0d78fcd512d4dbd49534a7feca1277bda03666d9e88b278d3c515e9'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2028,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundaryGenericCastTransfer'] and len(plan['direct'])==1
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
print('PASS source plan, parent/outer, 2028/81/1 preflight, 1 ordered source, 1 first selection, 81 outside bundles and 19 copied actual-function controls')

assert sha(root/'research/trace74-boundary-generic-cast-transfer-draft/Trace74BoundaryGenericCastTransfer.lean')=='0b8cec5b1d8d5cf237fdc098007d50e2da60d5db3112692949851bf536b3c824'
assert sha(root/'reviews/trace74-boundary-generic-cast-transfer-draft-independent/README.md')=='5757894e8ee34009c3176d6ff8c747843338bd3ba7979a1f6ccf862139405e6b'
print('PASS reviewed transfer source and source audit pins')
