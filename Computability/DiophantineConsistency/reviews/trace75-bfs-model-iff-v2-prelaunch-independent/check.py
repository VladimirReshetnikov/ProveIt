from pathlib import Path
import ast,hashlib,json,os,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-bfs-model-iff-prototype'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={'Trace75BFSModelIff.lean':'056683d3dc060692817d8af6d40800417d5c6f254dfa9333577527641e7a388c','run-v2.py':'b2a4546f408db202e6295043fb9c67bf04493cd99768c57f85584607af81a2ef','run-outer-v2.py':'2d22d64d9747fad05b2d86a76a3e190665a05cd3a067043fdcc45aefb44f1df3','test-policy-v2.py':'92b981ab66f7ad119d4c11346b35e7a32aeb9f1e6023d183fd69fdf12e32fbba','observations/policy-attempt02/result.json':'495a3ba302e9217d1ecae5d8b2203b8af9089b844d38728d436d0cd688eba086'}
for n,d in pins.items():assert sha(h/n)==d
policy=json.loads((h/'observations/policy-attempt02/result.json').read_text()); assert len(policy['checks'])==11 and all(policy['checks'].values()) and policy['runner_sha256']==pins['run-v2.py'] and policy['test_sha256']==pins['test-policy-v2.py']
tree=ast.parse((h/'run-v2.py').read_text()); fnnode=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='report_ok'); box={};exec(compile(ast.Module(body=[fnnode],type_ignores=[]),'policy','exec'),box); fn=box['report_ok']; good="'Trace75BFSModelIff.positive_model_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n";assert fn(good,'')
for out,err in [(good+'warning(lean.x): x\n',''),(good.replace('Quot.sound','sorryAx'),''),(good+good,''),('',''),(good,'bad'),(good.replace('Trace75BFSModelIff','Other'),''),(good.replace('Quot.sound','Quot.sound, other'),'')]:assert not fn(out,err)
envnode=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='env' for t in n.targets)); env=eval(compile(ast.Expression(envnode),'env','eval'),{'__builtins__':{},'lib':Path('/tmp/direct90-ipra-join-b66u_qqo/lib'),'pkg':Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')})
mods={'Trace75BFSHaltGraph':'93e589ad5e0151f262966bbee34c7a27b35b1e192c4a4de1679fcc8a0716014d','Trace75BFSModelHalt':'f3334e5e331cf93540fc45b92d221c4879bc2c0847068b38d96eae83561f56ae','CompactSymbolicBetaCast':'4da9ee64cb8258c8885d9194ca48d96f3cab806d2c0e2cadefc06fe63e95fd39','CompactSymbolicMaskData':'bce797f5b40fa75f130af592ed0c41e755f888ce9693538d1020cbd230004437'}
for n,d in mods.items():
 candidates=[Path(p)/(n+'.olean') for p in env['LEAN_PATH'].split(':') if os.path.lexists(Path(p)/(n+'.olean'))]; first=candidates[0]; assert first.is_file() and sha(first)==d; print(n,'first',first,'target',first.resolve())
for p,d in [('trace75-bfs-halt-graph-prototype/observations/outer-attempt03/result.json','719738b12906e3105d3d3df0dfb6ad2757396a9387278ef3c7ebb11e548b3f1f'),('trace75-bfs-model-halt-prototype/observations/attempt01/result.json','f07f6309693b7259e15bd149a14c2da5e96e50c62b5fc82c43ca60d4fa416a4a'),('trace75-unscaled-reverse-graph-prototype/observations/overlay-attempt01/result.json','60f41f892354d0fb1fab6b07e15c1881a34a1e1fc9d3e9da6f2c5079d33e6845')]:assert sha(root/'research'/p)==d
with tempfile.TemporaryDirectory(prefix='trace75-modeliff-wrapper-audit-') as tmp:
 p=Path(tmp); (p/'observations/policy-attempt02').mkdir(parents=True)
 for n in ('run-v2.py','run-outer-v2.py','Trace75BFSModelIff.lean','observations/policy-attempt02/result.json'):shutil.copyfile(h/n,p/n)
 (p/'run-v2.py').write_text((p/'run-v2.py').read_text()+'\n# modified\n'); r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run-outer-v2.py'),'--attempt','attempt01'],capture_output=True,text=True)
 assert r.returncode!=0 and 'input pin mismatch' in r.stderr and not (p/'observations/outer-attempt01').exists() and not (p/'observations/modeliff-attempt01').exists()
print('PASS source/runner/outer/policy, four first direct pins, directional receipts and overlay manifest, actual policy mutations, copied wrapper rejection')
