from pathlib import Path
import ast,hashlib,json,os,subprocess,sys,tempfile,shutil
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-bfs-model-iff-prototype'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins={'Trace75BFSModelIff.lean':'056683d3dc060692817d8af6d40800417d5c6f254dfa9333577527641e7a388c','run-v3.py':'abf2711130afe21e3f5a679f8a6275eb514cce98d0c70ae7a27806eebbb4db4e','run-outer-v3.py':'a9863903a204a9223e8168427a23fe4d6710b2d20c653a519bcf5a192b22fb1d','observations/policy-attempt03/result.json':'ff38e6a6f0aafc0d4c07cad52d8bb62b4c531f8dabe6906d97f4e006d02739e1','observations/modeliff-attempt01/terminal.json':'911274ab2f03f41c70cdde60cebc962d8337fd6d65f90bbc80c10949f0d3e83e','observations/outer-attempt01/result.json':'99642025538e93999fb13373ec0f7d24192aec91767fe8d35a5b32f219b30bdf'}
for n,d in pins.items():assert sha(h/n)==d
policy=json.loads((h/'observations/policy-attempt03/result.json').read_text());assert len(policy['checks'])==11 and all(policy['checks'].values()) and policy['runner_sha256']==pins['run-v3.py']
tree=ast.parse((h/'run-v3.py').read_text()); f=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='report_ok'); box={};exec(compile(ast.Module(body=[f],type_ignores=[]),'policy','exec'),box);fn=box['report_ok']; good="'Trace75BFSModelIff.positive_model_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n";assert fn(good,'')
for out,err in [(good+'warning(lean.x): x\n',''),(good.replace('Quot.sound','sorryAx'),''),(good+good,''),('',''),(good,'bad'),(good.replace('Trace75BFSModelIff','Other'),''),(good.replace('Quot.sound','Quot.sound, other'),'')]:assert not fn(out,err)
baseline=ast.literal_eval(next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='fresh_baseline' for t in n.targets))); assert len(baseline)==21
for directory,files in baseline.items():
 p=Path(directory); assert p.is_dir() and not p.is_symlink() and {x.name for x in p.iterdir()}==set(files)
 for n,d in files.items(): assert (p/n).is_file() and not (p/n).is_symlink() and sha(p/n)==d
envnode=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='env' for t in n.targets)); env=eval(compile(ast.Expression(envnode),'env','eval'),{'__builtins__':{},'lib':Path('/tmp/direct90-ipra-join-b66u_qqo/lib'),'pkg':Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')}); paths=env['LEAN_PATH'].split(':')
producer=json.loads((root/'research/trace75-bfs-model-halt-prototype/observations/attempt01/result.json').read_text()); producer_roots=producer['env']['LEAN_PATH'].split(':')[:21];assert list(baseline)==producer_roots and paths[1:22]==producer_roots
mods={'Trace75BFSHaltGraph':'93e589ad5e0151f262966bbee34c7a27b35b1e192c4a4de1679fcc8a0716014d','Trace75BFSModelHalt':'f3334e5e331cf93540fc45b92d221c4879bc2c0847068b38d96eae83561f56ae','CompactSymbolicBetaCast':'4da9ee64cb8258c8885d9194ca48d96f3cab806d2c0e2cadefc06fe63e95fd39','CompactSymbolicMaskData':'bce797f5b40fa75f130af592ed0c41e755f888ce9693538d1020cbd230004437'}
for n,d in mods.items():
 candidates=[Path(p)/(n+'.olean') for p in paths if os.path.lexists(Path(p)/(n+'.olean'))];first=candidates[0];assert first.is_file() and sha(first)==d; print(n,'first',first,'target',first.resolve())
for directory,files in baseline.items():
 for n,d in files.items():
  if not n.endswith('.olean'):continue
  matches=[Path(p)/n for p in paths[22:] if (Path(p)/n).is_file()];assert all(sha(m)==d for m in matches),(n,matches)
failed=json.loads((h/'observations/modeliff-attempt01/terminal.json').read_text()); assert failed['exit']!=0 and "unknown module prefix 'Trace75BFSOriginalWord'" in (h/'observations/modeliff-attempt01/stdout').read_text()
with tempfile.TemporaryDirectory(prefix='trace75-modeliff-v3-wrapper-audit-') as tmp:
 p=Path(tmp);(p/'observations/policy-attempt03').mkdir(parents=True)
 for n in ('run-v3.py','run-outer-v3.py','Trace75BFSModelIff.lean','observations/policy-attempt03/result.json'):shutil.copyfile(h/n,p/n)
 (p/'run-v3.py').write_text((p/'run-v3.py').read_text()+'\n# altered\n');r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run-outer-v3.py'),'--attempt','attempt02'],capture_output=True,text=True);assert r.returncode!=0 and 'input pin mismatch' in r.stderr and not (p/'observations/outer-attempt02').exists() and not (p/'observations/modeliff-attempt02').exists()
print('PASS 21 full root inventories/producer order/top-level overlap, four direct pins, failed attempt, report controls, copied wrapper rejection')
