from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-witness-rebuild';ph=root/'research/trace74-boundary-witness-plan';pre=h/'observations/preflight-attempt03';pol=h/'observations/policy-attempt02/result.json';presult=ph/'observations/plan-attempt02/result.json';parentdir=root/'research/trace74-boundary-compatible-rebuild/observations/attempt03';parent=parentdir/'result.json';po=root/'research/trace74-boundary-compatible-rebuild/observations/outer-attempt03/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan-v2.py':'fd776393856722fec6cabb08cbc187ecea27f181bb8c69613a5e5ca86226af4b',presult:'552e19a1cdb8112996a1d20e11f7528a8c1885128e9d3e29a9b82fd07a0a3b42',h/'run-v2.py':'4ff2717553b468f707c49b8b0948e44a87670db387b1a989381ee2203fd55b55',h/'run-outer-v3.py':'fb6d9f2f50b624bef82131e1f991bce851b55fce61c6534cc1f9f306ae384197',pre/'terminal.json':'5e059384a4d22617b8653e0f6f662c48c770c8957cca6728b617cc0fca1782aa',pol:'795c6a744be9ec3883fca5c42cd7bb6d096c24bd145ca77918ab23a8a22ea830',parent:'aa17ffeb0a2446d44392d986af54a9cd687dd544c67dc145a87c77f600e7a2d3',po:'2493accc873ec46391494ef5125de3b61d460b4bef61fb56f54f966ccbc036d0',root/'reviews/trace74-boundary-compatible-result-independent/README.md':'cfce71fa601910a41c86106b8421ddff024d906a711ae02ab5de3c61abc2e14b'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run-v2.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2021,81,4) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run-v2.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundaryParentWitness','Trace74BoundaryPartsWitness','Trace74BoundaryNaturalWitness','Trace74BoundaryGraphWitness'] and len(plan['direct'])==6
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
print('PASS source plan, parent/outer, 2021/81/4 preflight, 4 ordered sources, 6 first selections, 81 outside bundles and 19 copied actual-function controls')

for n,digest in {'Trace74BoundaryParentWitness':'dc780057f82b0984ed59c83803d1cef4a457130f9cb4817e73ce4c4eb05d94e3','Trace74BoundaryPartsWitness':'808a5a1eb21284da2bd634ea2db4bf47f35c9c113fa3883fde3f55fdab8e7592','Trace74BoundaryNaturalWitness':'2beb80ae33a4cfa9474de6d59f58e7a382d9278804178674e76f8181ddcce931','Trace74BoundaryGraphWitness':'013b77ea41dc550edd2a7bef4cd0d402489854cc6f30da722237aa0b1556725e','Trace74BoundarySeedConditional':'5b04df0029b7575b9ce3b100b8a26c98a4526dade5e264211e5295e50c76bae3'}.items():assert sha(root/'research/trace74-boundary-witness-draft'/(n+'.lean'))==digest
assert sha(root/'reviews/trace74-boundary-witness-draft-independent/README.md')=='e7b221e58721eefc36f537b84dc1fc5fc9d28ce71df02bee725285682df2a66e'
print('PASS five independently reviewed source bytes and draft audit')

old=h/'observations/attempt01';oldouter=h/'observations/outer-attempt01/terminal.json'
assert sha(old/'result.json')=='253f56b0df87d41b487f85405f4912ca5c745578a2302a93eaaaf785cf4f555f' and sha(oldouter)=='69e6a0bbedea877a2d5f339b774414cf144f90b36fa075cfa43c2512718cb203'
a=json.loads((old/'result.json').read_text());o=json.loads(oldouter.read_text());assert a['status']=='FAILED' and o['exit']==1 and o['child_status']=='FAILED' and o['child_result_sha256']==sha(old/'result.json') and len(a['stages'])==5 and all(x['status']=='PASS' for x in a['stages'][:4]) and a['stages'][4]['exit']==1
for i,stage in enumerate(a['stages'],1):
 for ext in ('stdout','stderr'):assert sha(old/('stage-%02d.'%i+ext))==stage[ext+'_sha256']
error=(old/'stage-05.stdout').read_text();assert 'unsolved goals' in error and 'excessive memory' in error and 'positive_boundary_of_source' in error
oldplan=json.loads((ph/'observations/plan-attempt01/result.json').read_text());assert rows==oldplan['stages'][:4]
print('PASS exact unchanged four-stage rows and failed fifth stage excluded')
