from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-seed-model-facts-rebuild';ph=root/'research/trace74-boundary-seed-model-facts-plan';pre=h/'observations/preflight-attempt02';pol=h/'observations/policy-attempt02/result.json';presult=ph/'observations/plan-attempt02/result.json';parentdir=root/'research/trace74-boundary-seed-specialization-rebuild/observations/attempt01';parent=parentdir/'result.json';po=root/'research/trace74-boundary-seed-specialization-rebuild/observations/outer-attempt01/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan-v2.py':'9a35d170fc601d475badc6be682bb2421fee960733054ef38a1560207448f034',presult:'81bc8444512cea4165bbd415d2646c7a8fe9816349ca8c330bf7b89cb1871936',h/'run-v2.py':'aa66e84a368b623440727f777f55d4afbe537c8c85423825d1d682487b7af097',h/'run-outer-v2.py':'c41d011308426ccf352e0c70e8b0b6e84c4c0c8c6b047de122402ece6335c6ae',pre/'terminal.json':'54f52014d9d32f5b231b3a441d5ecb72bca0ce747a66f9df2ae36d968bb35a18',pol:'53c6a49a081dce324f4c75291a0ba26c04682d5790f856d773a0ef16ac684140',parent:'cb5339ea9547b274009117466cb68ba56ba4d452eaccf21333949562c0cbd3d3',po:'775418302bea11deb6e7d0cd8d6630cae02cd5645f3980594921decd1d78f9ae',root/'reviews/trace74-boundary-seed-specialization-result-independent/README.md':'f6d8d0ac136014b81e31310f683521b1cd7fe20ba1dfd79a2b03981a635869ba'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run-v2.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2031,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run-v2.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundarySeedModelFacts'] and len(plan['direct'])==2
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
 p=Path(tmp);[shutil.copyfile(h/n,p/n) for n in ('run-v2.py','test-policy-v2.py')];q=subprocess.run([sys.executable,'-I','-S','-B',str(p/'test-policy-v2.py')],capture_output=True,text=True);assert q.returncode==0,(q.stdout,q.stderr)
print('PASS source plan, parent/outer, 2031/81/1 preflight, 1 ordered source, 2 first selections, 81 outside bundles and 19 copied actual-function controls')

assert sha(root/'research/trace74-boundary-seed-model-facts-draft/Trace74BoundarySeedModelFacts.lean')=='ed4740c50c0a3f1fa7f953cd40faa1b4560124d8fd92177df8ec0dc7ae6be30b'
assert sha(root/'reviews/trace74-boundary-seed-model-facts-draft-independent/README.md')=='e0dfdf9da530dc7cb06b22087f5d4d8fce4487de045bcc38765b7d4c34c9b989'
name='DiophantineConsistency.ArithmeticStandardCasts';assert name in r['closures']['Trace75BFSFixedIPRA']['project'] and name in r['closures']['DirectBFSBandCarry']['project'] and r['serialized_headers'][name]==['Init','Init','DiophantineConsistency.ArithmeticBinaryPopulation']
print('PASS reviewed model facts source and arithmetic casts inside captured parent closures')

assert sha(root/'research/trace74-boundary-seed-model-facts-draft-v2/Trace74BoundarySeedModelFacts.lean')=='554ec943d367e4684cc9c60c51e0a15f7f3272ec2878f37f01e858620a0d7457' and sha(root/'reviews/trace74-boundary-seed-model-facts-draft-v2-independent/README.md')=='fa5028106b87911ed672c507c259a00f2020406e3ee547d22cc2145361642891'
old=h/'observations/attempt01';oo=h/'observations/outer-attempt01/terminal.json';assert sha(old/'result.json')=='e23814992f4ee1972fce2639bc091389aa2d09cbce0fd066dd24f3cc5e108cff' and sha(oo)=='ea46990ba172bf79c27231212b2bef9fee50477dd3cd6f5c8e3bc5b40669eb09'
r0=json.loads((old/'result.json').read_text());o0=json.loads(oo.read_text());assert r0['status']=='FAILED' and o0['exit']==1 and o0['child_status']=='FAILED' and o0['child_result_sha256']==sha(old/'result.json') and len(r0['stages'])==1 and r0['stages'][0]['exit']==1
for ext in ('stdout','stderr'):assert sha(old/('stage-01.'+ext))==r0['stages'][0][ext+'_sha256']
err=(old/'stage-01.stdout').read_text();assert 'sorryAx' in err and 'Nat.cast_sub hle' in err and 'unsolved goals' in err
print('PASS reviewed v2 repairs and prior failed attempt/sorryAx exclusion')
