from pathlib import Path
import ast,hashlib,json,os,re,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-bfs-halt-graph-prototype'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={'Trace75BFSHaltGraph.lean':'9ad0f1b7a90c8305d95978024881382a6b88e9c3794cdc7c1447c4220a29957d','run-v3.py':'5d32b766ba402d9ed2c926fda5ec7f0e78a93bfea8854b90b517a63532222909','run-outer.py':'b2b411ef12b83235c69f212a6876ccce1eb7466ce15f9923b1dbcbb7ca2a28ee','test-policy.py':'3c110ab59b21453e3e26e13a5e96aeb0d01d2d66bf8a3bf5a3301ab9e67a2a30','observations/policy-attempt01/result.json':'2952f35d52ec93354938bc820e47fea8c905621b186d3d869e88d16f90ca812e'}
for n,d in pins.items():assert sha(h/n)==d
policy=json.loads((h/'observations/policy-attempt01/result.json').read_text()); assert len(policy['checks'])==11 and all(policy['checks'].values()) and policy['runner_sha256']==pins['run-v3.py'] and policy['test_sha256']==pins['test-policy.py']
tree=ast.parse((h/'run-v3.py').read_text()); f=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='report_ok'); box={}; exec(compile(ast.Module(body=[f],type_ignores=[]),'policy','exec'),box); fn=box['report_ok']
good="'Trace75BFSHaltGraph.halt_zero_of_model_ports' depends on axioms: [propext, Classical.choice, Quot.sound]\n"; assert fn(good,'')
for out,err in [(good+'warning(lean.x): x\n',''),(good.replace('Quot.sound','sorryAx'),''),(good+good,''),('',''),(good,'bad'),(good.replace('Trace75BFSHaltGraph','DirectBFSHalt80Graph'),''),(good.replace('Quot.sound','Quot.sound, other'),'')]:assert not fn(out,err)
old=json.loads((h/'observations/directbfshalt80-attempt02/terminal.json').read_text()); assert old['exit']==0 and old['reason'] is None and old['pins']==old['after'] and old['direct_imports']==old['direct_imports_after']
mods=re.findall(r'^import\s+([^\s]+)',(h/'Trace75BFSHaltGraph.lean').read_text(),re.M); assert mods==['DirectBFSHaltPellSeed','Trace75PackingReverseGraph','CompactRankResidueJoin','Direct80RankLower']
for n,rec in zip(mods,old['direct_imports']):
 assert n==rec['module']; candidates=[Path(p)/(n+'.olean') for p in old['lean_path'].split(':') if os.path.lexists(Path(p)/(n+'.olean'))]; first=candidates[0]; assert first.is_file() and str(first.resolve())==rec['path'] and sha(first)==rec['sha256']; print(n,'first',first)
assert len(old['stage_receipts'])==59
for e in old['stage_receipts']:assert sha(e['path'])==e['sha256']
overlay=root/'research/trace75-unscaled-reverse-graph-prototype/observations/overlay-attempt01/result.json'; assert sha(overlay)==old['pins']['overlay_manifest']=='60f41f892354d0fb1fab6b07e15c1881a34a1e1fc9d3e9da6f2c5079d33e6845'
with tempfile.TemporaryDirectory(prefix='trace75-halt-policy-audit-') as tmp:
 p=Path(tmp); (p/'observations/policy-attempt01').mkdir(parents=True)
 for n in ('run-v3.py','run-outer.py','Trace75BFSHaltGraph.lean','observations/policy-attempt01/result.json'):shutil.copyfile(h/n,p/n)
 (p/'run-v3.py').write_text((p/'run-v3.py').read_text()+'\n# modified\n')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run-outer.py'),'--attempt','attempt03'],capture_output=True,text=True)
 assert r.returncode!=0 and 'input pin mismatch' in r.stderr and not (p/'observations/outer-attempt03').exists() and not (p/'observations/directbfshalt80-attempt03').exists()
print('PASS four direct first selections; 59 historical stage receipt hashes; overlay manifest; actual policy mutations; copied wrapper rejects altered runner')
