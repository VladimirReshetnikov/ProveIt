from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-recurrence-cast-rebuild';ph=root/'research/trace74-boundary-recurrence-cast-plan';pre=h/'observations/preflight-attempt01';pol=h/'observations/policy-attempt01/result.json';presult=ph/'observations/plan-attempt01/result.json';parentdir=root/'research/trace74-boundary-seed-parametric-rebuild/observations/attempt02';parent=parentdir/'result.json';po=root/'research/trace74-boundary-seed-parametric-rebuild/observations/outer-attempt02/terminal.json';outbase=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={ph/'plan.py':'c595fb9724fbb5588f2a6389affdd463ac5d7dabd4a3cce9b95fd6f5f8678da6',presult:'f0216799603cf084b7cfe6407f6ac303deda1f9a63b6677aa623751c75855bc8',h/'run.py':'3451a2b18f8e582d7a75ec655dd48c92cdb78e19f401c504d478ee879f8d6c97',h/'run-outer.py':'5aeb09875fb51bafc5777bde25f5b41c4578c2309d50f34161d0424669607782',pre/'terminal.json':'ede0529cff7814a2745355f3f29a0548f11fe5527201573831a5fa130ea8aec0',pol:'27fe6fa18b25dab918a07a51230119321f3e59e8c7631f24d5ec9be9b805637b',parent:'2f43ae10b79aca99bf5ce5d93edb177ee0384aed9151a9f3449a05cce579db4d',po:'5548ff10648b5f4e984a7512f5459009fca68ae797a5d7a26188586171402092',root/'reviews/trace74-boundary-seed-parametric-result-independent/README.md':'90c76e3061cb386e1eb5fb10d8f575f205c0e934f2c781da97584f65fd9ddbce'}
for p,d in pins.items():assert sha(p)==d,p
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_before']==x['runner_after']==pins[h/'run.py'] and x['wrapper_before']==x['wrapper_after']
for n in ('stdout','stderr'):assert sha(pre/n)==x[n+'_sha256']
assert not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2026,81,1) and len(p['inherited_four'])==4
z=json.loads(pol.read_text());assert z['status']=='PASS' and z['runner_sha256']==pins[h/'run.py'] and len(z['checks'])==19 and all(z['checks'].values())
plan=json.loads(presult.read_text());rows=plan['stages'];names=[x['module'] for x in rows];assert names==['Trace74BoundaryRecurrenceCast'] and len(plan['direct'])==1
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
print('PASS source plan, parent/outer, 2026/81/1 preflight, 1 ordered source, 1 first selection, 81 outside bundles and 19 copied actual-function controls')

assert sha(root/'research/trace74-boundary-recurrence-cast-draft/Trace74BoundaryRecurrenceCast.lean')=='94d1c036f3cc94030b8f95395bc0f6274a823692d93c45a0c87e886571a58ea6'
assert sha(root/'reviews/trace74-boundary-recurrence-cast-draft-independent/README.md')=='df59371dc4a1b621fe732c9e36f45848194058f102e5e2342c158cc99650a9d4'
print('PASS reviewed recurrence cast source and audit pins')
