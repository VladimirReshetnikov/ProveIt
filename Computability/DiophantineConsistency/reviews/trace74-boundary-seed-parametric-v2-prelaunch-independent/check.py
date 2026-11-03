from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-seed-parametric-rebuild';ph=root/'research/trace74-boundary-seed-parametric-plan';pre=h/'observations/preflight-attempt02';pol=h/'observations/policy-attempt02/result.json';presult=ph/'observations/plan-attempt02/result.json';parentdir=root/'research/trace74-boundary-witness-rebuild/observations/attempt02';parent=parentdir/'result.json';po=root/'research/trace74-boundary-witness-rebuild/observations/outer-attempt02/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan-v2.py':'3685780eb354861630cd7294ccfd535329b31bc817ae48c02916a67ff9748563',presult:'fc353484b3d45c8b1a28b505ab83ef2a15c14a0159cb5641643381e12239a2da',h/'run-v2.py':'afec052c5a378e6adc1c1112d071d4264777da2d044e645a3b3754e05d7cb9ad',h/'run-outer-v2.py':'9637a44205491fc298f3fa7be3dd01690e2e23896ec5f0897960d90ffedcb9a3',pre/'terminal.json':'0e9254a94ff4bfcd0685278c506f70761395d7e0852bfb5e884a6c4d2f5055e4',pol:'790b3619cec38ee9e082471676969f6a7934059c1fd3624141af70b129681639',parent:'fcebf5b3e7cb675854b00c0959175980643efb642640a7b2dd9f15bf0972dbc8',po:'db0859e487a22b53e4dd869145e2ace15290fe242e900c757735f82a3130ab19',root/'reviews/trace74-boundary-witness-result-independent/README.md':'33fc5d7e79463eda0b587a77ade9590f663cacc8519b9eda9d7f15c5f578337c'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run-v2.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2025,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run-v2.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundarySeedParametric'] and len(plan['direct'])==1
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
print('PASS source plan, parent/outer, 2025/81/1 preflight, 1 ordered source, 1 first selection, 81 outside bundles and 19 copied actual-function controls')

assert sha(root/'research/trace74-boundary-seed-parametric-draft/Trace74BoundarySeedParametric.lean')=='b5437f37f950554cb09a885bba6cccc3638816607412f3f38024ef0f8bdff1cd'
assert sha(root/'reviews/trace74-boundary-seed-parametric-draft-independent/README.md')=='6b5e2f355b889dcdec7a1f8859377e07d89e7841883c18abc9a56ff326bd55ed'
print('PASS reviewed source and source-level audit pins')

a=(root/'research/trace74-boundary-seed-parametric-draft/Trace74BoundarySeedParametric.lean').read_text();b=(root/'research/trace74-boundary-seed-parametric-draft-v2/Trace74BoundarySeedParametric.lean').read_text();assert a.replace('simp [q,b,ports31,source31,h21,add_comm]','simp [q,b,ports31,source31,add_comm]')==b and sha(root/'research/trace74-boundary-seed-parametric-draft-v2/Trace74BoundarySeedParametric.lean')=='84e6f461b44f44534e643b52d3d24e38e5eb3303cfd33f6186703a9e761dca10'
old=h/'observations/attempt01';outer=h/'observations/outer-attempt01/terminal.json'
assert sha(old/'result.json')=='deb4e658cc6061960c60ad484cb579d13d5f802b1828bea10e976694b08d9aa2' and sha(outer)=='3beb4523ec056ddfecb63ede4d62a94601ffc38a69949fb75d13baab4fdb0f4a'
r=json.loads((old/'result.json').read_text());o=json.loads(outer.read_text());assert r['status']=='FAILED' and o['exit']==1 and o['child_status']=='FAILED' and o['child_result_sha256']==sha(old/'result.json') and len(r['stages'])==1 and r['stages'][0]['exit']==0
for ext in ('stdout','stderr'):assert sha(old/('stage-01.'+ext))==r['stages'][0][ext+'_sha256']
assert 'warning: This simp argument is unused:' in (old/'stage-01.stdout').read_text()
print('PASS source-only simp removal and preserved warning-rejected Lean exit zero')
