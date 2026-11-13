from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-seed-specialization-rebuild';ph=root/'research/trace74-boundary-seed-specialization-plan';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';presult=ph/'observations/plan-attempt01/result.json';parentdir=root/'research/trace74-boundary-generic-assembly-rebuild/observations/attempt01';parent=parentdir/'result.json';po=root/'research/trace74-boundary-generic-assembly-rebuild/observations/outer-attempt01/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'3e655a218a4e7cd5aa18fa2f89f71ec2b7a75bf4e6d2e19a0deff0fb8e43aa79',presult:'6012f8f4027ca0f58c1ba5858a8b68d9530a163fb8397ba6fabff0b8d909ec5f',h/'run.py':'b7a0e71dd129219a580b031b7a4f0522353e5fc9e08a98741f5fa1882bf6d608',h/'run-outer.py':'47f9ccc0d0c13a1a1704f9d00dedd15f949b46646617b44f643e476633d250b6',pre/'terminal.json':'658e91ff6514ed15c4dc023a367c8428f746568adaff581db4f6679e5eabb9c2',pol:'acf1cdfe640c9f5ecf85439712632636d183269444dbef7605acc3e459f75e2e',parent:'4172c5c24f47dff32dae9c12968f2de3d476d0df11db1d840b6fa6c0ae32e649',po:'c4e9049257292df510e90788b3f9acc5343830ca3d27efddeea052f73d310609',root/'reviews/trace74-boundary-generic-assembly-result-independent/README.md':'0800e9b5d157660c46d7c3997958d255d38cfd3d3dcc98ef701eee2daca71e5d'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2030,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundarySeedSpecialization'] and len(plan['direct'])==2
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
print('PASS source plan, parent/outer, 2030/81/1 preflight, 1 ordered source, 2 first selections, 81 outside bundles and 19 copied actual-function controls')

assert sha(root/'research/trace74-boundary-seed-specialization-draft/Trace74BoundarySeedSpecialization.lean')=='5b1f957dbd201f54fd80c58492f7ce058a372d528d73488156adac3896db02d9'
assert sha(root/'reviews/trace74-boundary-seed-specialization-draft-independent/README.md')=='1a985d6acf0b2d1e99b5e0c35fedaee2265df8208f4bca9655bf14def8da55d0'
print('PASS reviewed specialization source and source audit pins')
