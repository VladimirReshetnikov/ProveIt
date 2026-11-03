from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-compatible-rebuild';ph=root/'research/trace74-boundary-compatible-plan';pre=h/'observations/preflight-attempt03';pol=h/'observations/policy-attempt03/result.json';presult=ph/'observations/plan-attempt02/result.json';parentdir=root/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01';parent=parentdir/'result.json';po=root/'research/trace75-bfs-ipra-final-assembly-plan/observations/outer-attempt01/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'bd8ecd6ff3861f7b2d5ccb651332ddad5a538537a5ce1990835c58c7d9db4662',presult:'5bff6c675c26e8f6921bc0736945c38eaa5b3df561381a5fefdaf2ac63936cde',h/'run-v3.py':'c60ec396fde0a5beb10d6438331e3262706883c8a668620d3246848bec7ecea2',h/'run-outer-v3.py':'8009379c0bf88ba1990d2cef784917ba6d91a4818916f25f11b39906cf8b4b5a',pre/'terminal.json':'07a3070cf9017ed54042602faf10b1db55e04918720c9a9d0ba0dddab495940a',pol:'e4ea6865bcd6bbdb76b1ae8ab7c14a67e4affa1fb06bdd0c0423e80eeb8dc4db',parent:'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c',po:'2188db777c5fe442be871c30d29943de70fe0c1d20325d49b00bb9886e56c69d',root/'reviews/trace75-bfs-final-assembly-result-independent/README.md':'d99de3ef2a5bd0b08af624e2421f4cc10f6eb9a9886eb67a94016a237d6b2c6b'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run-v3.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2016,81,5) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run-v3.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74Mask','Trace74BoundaryParent','Trace74BoundaryParts','Trace74BoundaryNatural','Trace74BoundaryGraph'] and len(plan['direct'])==6
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
 p=Path(tmp);[shutil.copyfile(h/n,p/n) for n in ('run-v3.py','test-policy-v3.py')];q=subprocess.run([sys.executable,'-I','-S','-B',str(p/'test-policy-v3.py')],capture_output=True,text=True);assert q.returncode==0,(q.stdout,q.stderr)
print('PASS source plan, parent/outer, 2016/81/5 preflight, 5 ordered sources, 6 first selections, 81 outside bundles and 19 copied actual-function controls')

draft=root/'research/trace74-boundary-parent-binding-draft';v2=root/'research/trace74-boundary-parent-binding-v2'
for n in ('Trace74BoundaryParts.lean','Trace74BoundaryNatural.lean','Trace74BoundaryGraph.lean'): assert (draft/n).read_bytes()==(v2/n).read_bytes()
a=(draft/'Trace74BoundaryParent.lean').read_text();b=(v2/'Trace74BoundaryParent.lean').read_text();assert a.replace("fin_cases j <;> simp [oldVal,w,old,hmask'] <;> ring","fin_cases j <;> simp [oldVal,w,old,hmask']")==b
a=(h/'run-v2.py').read_text();b=(h/'run-v3.py').read_text();assert a.replace('trace75-bfs-compatible-provider-plan/observations/plan-attempt02/result.json','trace75-bfs-compatible-provider-plan/observations/plan-attempt01/result.json')==b
print('PASS four source deltas and restored parent plan path')
