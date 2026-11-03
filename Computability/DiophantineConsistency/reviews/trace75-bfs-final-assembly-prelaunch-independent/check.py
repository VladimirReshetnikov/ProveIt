from pathlib import Path
import ast,hashlib,json,os,re,shutil,subprocess,sys,tempfile
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-bfs-ipra-final-assembly-plan';pre=h/'observations/preflight-attempt01';policy=h/'observations/policy-attempt01';op=h/'observations/outer-policy-attempt01';parentdir=root/'research/trace75-bfs-compatible-forward-rebuild/observations/attempt01';parent=parentdir/'result.json';po=root/'research/trace75-bfs-compatible-forward-rebuild/observations/outer-attempt01/terminal.json';outsidepath=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json';ex=root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={h/'run.py':'f2d43b531adb692b2bbcf27fd8c25ce79df121c85b689a9e46defcc5913130ac',h/'run-outer.py':'cb9de001416de6373cc77e6a6c15877cbbcc864edbf395c1fd899c9d4cd8f2b7',pre/'terminal.json':'6fb87657d5f7abc4f8f3defaf2915cb474edab21a9718f75f1e7d2454f7a4e1d',policy/'result.json':'14858d9503ee16d68ad94fc7bea28c1185d628450f3242fbc96cd825de4a62d6',op/'terminal.json':'2f2e099a3c5d6aa00e2e14f8966a44dc93963aad10daeddbc217a3108c906e40',parent:'f8d6388911e101a7dfae2547907bc6f9245950fa953c3a4769eff00c140fc3d8',po:'5b286234c26c06db503ff6a485aeac2a9e57afc76205c189a30bb8e07e7316c5'}
for p,d in pins.items():assert sha(p)==d,p
names={'RPLAN':'research/trace75-bfs-compatible-reverse-plan/observations/source-plan-attempt01/result.json','SPLAN':'research/trace75-bfs-ipra-final-assembly-plan/plan.json','FORWARD_PLAN':'research/trace75-bfs-compatible-forward-plan/observations/plan-attempt01/result.json','CANON':'Lean/DiophantineConsistency/TenPositiveTrace75Syntax.lean','EXTRA':'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json','BFS':'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json','INITIAL':'research/direct-bfs-80-coherent-rebuild/observations/attempt01/initial-project.json','OUTSIDE':'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json','CPLAN':'research/trace75-bfs-compatible-provider-plan/observations/plan-attempt01/result.json','HELPER':'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'}
env={n:root/p for n,p in names.items()};env['LEAN']=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');tree=ast.parse((h/'run.py').read_text());node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='PINS' for t in n.targets));assert isinstance(node,ast.Dict)
for k,v in zip(node.keys,node.values):assert isinstance(k,ast.Name) and sha(env[k.id])==ast.literal_eval(v),k.id
r=json.loads(parent.read_text());outer=json.loads(po.read_text());assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==pins[parent] and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']
x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_sha256']==pins[h/'run.py'];assert sha(pre/'stdout')==x['stdout_sha256'] and sha(pre/'stderr')==x['stderr_sha256'] and not (pre/'stderr').read_bytes();p=json.loads((pre/'stdout').read_text());assert p['status']=='PREFLIGHT_PASS' and (p['parent'],p['outside'],p['stages'])==(2011,81,5) and len(p['inherited_four'])==4
for folder,control in [(policy,h/'test-policy.py'),(op,h/'test-outer.py')]:
 rec=json.loads((folder/('result.json' if folder==policy else 'terminal.json')).read_text());assert rec['exit']==0 and sha(control)==rec['control_sha256'] and sha(folder/'stdout')==rec['stdout_sha256'] and sha(folder/'stderr')==rec['stderr_sha256'];out=json.loads((folder/'stdout').read_text());assert out['status']=='PASS' and all(out['tests'].values())
base=Path(r['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');plan=json.loads((h/'plan.json').read_text());stages=plan['stages'];names=[x['module'] for x in stages];assert len(names)==len(set(names))==5
for i,row in enumerate(stages):
 s=root/row['source'];assert sha(s)==row['sha256'] and not os.path.lexists(base/(row['module'].replace('.','/')+'.olean'));imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',s.read_text(),re.M);assert imports==row['imports'] and not set(imports)&set(names[i:]);assert len(re.findall(r'^#print axioms\s+',s.read_text(),re.M))==[1,1,1,6,5][i]
external=sorted({n for row in stages for n in row['imports']}-set(names));assert len(external)==8
for n in external:
 candidates=[p/(n.replace('.','/')+'.olean') for p in (base,pack,core) if os.path.lexists(p/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and candidates[0].is_relative_to(base);print(n,'first',candidates[0],sha(candidates[0]))
outside=json.loads(outsidepath.read_text());extra=json.loads(ex.read_text());assert extra['module'] not in outside;outside[extra['module']]=extra['record'];assert len(outside)==81
for n,bundle in outside.items():
 p=Path(bundle['.olean']['path']);candidates=[q/(n.replace('.','/')+'.olean') for q in (base,pack,core) if os.path.lexists(q/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0]==p and p.is_file()
 for suffix,v in bundle.items():
  q=Path(str(p)[:-6]+suffix)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve(strict=True))==v['resolved'] and sha(q)==v['sha256']
with tempfile.TemporaryDirectory(prefix='trace75-assembly-final-policy-') as tmp:
 p=Path(tmp)
 for n in ('run.py','run-outer.py','test-policy.py','test-outer.py'):shutil.copyfile(h/n,p/n)
 for n,count in [('test-policy.py',19),('test-outer.py',6)]:
  t=subprocess.run([sys.executable,'-I','-S','-B',str(p/n)],capture_output=True,text=True);assert t.returncode==0,(n,t.stdout,t.stderr);z=json.loads(t.stdout);assert z['status']=='PASS' and len(z['tests'])==count and all(z['tests'].values())
print('PASS forward receipts, 2011/81/5 preflight, 5 sources, 8 direct selections, 81 outside bundles and copied actual policy/outer tests')
