from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-witness-rebuild';ph=root/'research/trace74-boundary-witness-plan';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';presult=ph/'observations/plan-attempt01/result.json';parentdir=root/'research/trace74-boundary-compatible-rebuild/observations/attempt03';parent=parentdir/'result.json';po=root/'research/trace74-boundary-compatible-rebuild/observations/outer-attempt03/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'0f5a39239d1bf544de0d9fcf61ab96b91a13fd4173d26631a498f7aef380bf44',presult:'25c93f7ad9856a589304ae8bc2a693e51c4a5b9fd2aa01c804f434a2aefd4303',h/'run.py':'14a9268298a5425521dacce7aec1b16524c36e8a27d63d38b9f6fe128c4c9f4c',h/'run-outer.py':'7c05cffef7ef858572fffaa39141348d7f13adcc703424e9daf4a631b170066b',pre/'terminal.json':'cf5c7b0899abdc2553b031d1c5b1ccb7611b363a498cab3854d33dbef52952a2',pol:'0adf94cba9106138cbb13be73336db0957ebc13f9c3076d380a6d680218c3106',parent:'aa17ffeb0a2446d44392d986af54a9cd687dd544c67dc145a87c77f600e7a2d3',po:'2493accc873ec46391494ef5125de3b61d460b4bef61fb56f54f966ccbc036d0',root/'reviews/trace74-boundary-compatible-result-independent/README.md':'cfce71fa601910a41c86106b8421ddff024d906a711ae02ab5de3c61abc2e14b'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2021,81,5) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundaryParentWitness','Trace74BoundaryPartsWitness','Trace74BoundaryNaturalWitness','Trace74BoundaryGraphWitness','Trace74BoundarySeedConditional'] and len(plan['direct'])==6
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
print('PASS source plan, parent/outer, 2021/81/5 preflight, 5 ordered sources, 6 first selections, 81 outside bundles and 19 copied actual-function controls')

for n,digest in {'Trace74BoundaryParentWitness':'dc780057f82b0984ed59c83803d1cef4a457130f9cb4817e73ce4c4eb05d94e3','Trace74BoundaryPartsWitness':'808a5a1eb21284da2bd634ea2db4bf47f35c9c113fa3883fde3f55fdab8e7592','Trace74BoundaryNaturalWitness':'2beb80ae33a4cfa9474de6d59f58e7a382d9278804178674e76f8181ddcce931','Trace74BoundaryGraphWitness':'013b77ea41dc550edd2a7bef4cd0d402489854cc6f30da722237aa0b1556725e','Trace74BoundarySeedConditional':'5b04df0029b7575b9ce3b100b8a26c98a4526dade5e264211e5295e50c76bae3'}.items():assert sha(root/'research/trace74-boundary-witness-draft'/(n+'.lean'))==digest
assert sha(root/'reviews/trace74-boundary-witness-draft-independent/README.md')=='e7b221e58721eefc36f537b84dc1fc5fc9d28ce71df02bee725285682df2a66e'
print('PASS five independently reviewed source bytes and draft audit')
