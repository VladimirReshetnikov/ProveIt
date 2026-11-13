#!/usr/bin/env python3
"""Independent real-artifact audit, without compiling Lean."""
import hashlib,importlib.util,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';P=BASE/'compact44-clean-carry-reset-prototype';E=P/'evidence';OUT=Path('/tmp/ipra-compact-clean-carry-pair-01');PARENT=Path('/tmp/ipra-compact-heterogeneous-carry-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');HERE=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
receipt=E/'receipt.json';r=json.loads(receipt.read_bytes());obs=json.loads((E/'terminal-observation.json').read_bytes());assert H(receipt)=='c3252567d1997f9f247c9d144e5b6acb772be0df31bbb27029685877e18cc60c' and (OUT/'receipt.json').read_bytes()==receipt.read_bytes()
assert obs['session_id']==57568 and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['receipt_sha256']==H(receipt) and obs['protected_head']=='4e975da47ae8ca8a947cf8e16cb84131662086cc'
assert r['status']=='PASS_PAIRED_COMPACT_CLEAN_CARRY_RESET' and r['driver_sha256']=='52398e50ee91cca62829739abde44205a852574d6812ce4ba38a4c0d6b7d33d4' and H(P/'replay.py')==r['driver_sha256']
for name in ('receipt.json','terminal-observation.json','author.log','peer.log'):
 p=E/name;q=subprocess.run(['git','show','8e3bc09053:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True);assert q.stdout==p.read_bytes(),name
sp=importlib.util.spec_from_file_location('driver',P/'replay.py');d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d)
assert r['fixed_inputs_sha256']=={str(p):h for p,h in d.PINS.items()}
for p,h in d.PINS.items():assert H(p)==h,str(p)
scan,parent=d.verify();assert parent==r['parent_audit']
source=OUT/'frozen/DiophantineConsistency/CompactCarryReset.lean';assert source.is_file() and not source.is_symlink() and H(source)==H(P/'CompactCarryReset.lean')=='f80d473cb579a24086ae29e560cce33a8ed282bf90ce7458302ec8a3d244928d'
expected="'CompactCarryReset.digit_after_bounded_predecessor' depends on axioms: [propext, Classical.choice, Quot.sound]\n'CompactCarryReset.clean_after_bounded_predecessor' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
assert len(r['runs'])==2;rows=[];allstems={PACKAGE/'Init'}
for side,item in zip(('author','peer'),r['runs']):
 assert item['label']==side and item['compiler_exit']==0 and item['deps_exit']==0 and item['stop_reason'] is None and item['source_sha256']==H(source)
 obj=OUT/side/'lib/DiophantineConsistency/CompactCarryReset.olean';seed=OUT/side/'lib/DiophantineConsistency/CompactHeterogeneousCarry.olean';old=PARENT/side/'CompactHeterogeneousCarry.olean'
 assert obj.is_file() and not obj.is_symlink() and H(obj)==item['object_sha256']=='1c0d48a81ebc0340e9476f04ee81f2b9cd2dd3ecfdc7b12169b623cad5ee3e5c'
 assert seed.is_file() and not seed.is_symlink() and H(seed)==H(old)=='9f666c0181717d70486d4323692ccc5bd9c28f7a0a6b92aedb4074c2e2d43462'
 assert item['stdout']==expected and (E/(side+'.log')).read_text()==expected and (OUT/side/'compiler.log').read_text()==expected and H(E/(side+'.log'))==item['log_sha256']
 assert set(item['deps_stdout'].splitlines())=={str(PACKAGE/'Init.olean'),str(seed)}
 assert item['command']==[str(d.LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(OUT/'frozen'),str(source),'-o',str(obj)]
 parentlib=PARENT/side/'lib';lib=OUT/side/'lib';oldobjs={x.relative_to(parentlib).as_posix():x for x in parentlib.rglob('*.olean') if x.is_file()};newobjs={x.relative_to(lib).as_posix():x for x in lib.rglob('*.olean') if x.is_file()};assert len(oldobjs)==115 and set(newobjs)==set(oldobjs)|{'DiophantineConsistency/CompactHeterogeneousCarry.olean','DiophantineConsistency/CompactCarryReset.olean'}
 for rel,p in oldobjs.items():assert H(p)==H(newobjs[rel]),(side,rel)
 allstems.update((Path(str(obj)[:-6]),Path(str(seed)[:-6]),Path(str(old)[:-6])))
 rows.append({'side':side,'object_sha256':H(obj),'inherited_objects_checked':len(oldobjs),'sampled_peak_rss_bytes':item['sampled_peak_rss_bytes']})
assert len(allstems)==7
expectedkeys={str(stem)+suffix for stem in allstems for suffix in d.SUFFIXES};guards=r['direct_and_output_guards'];assert set(guards)==expectedkeys and len(guards)==70
for name,value in guards.items():
 p=Path(name)
 if value is None:assert not os.path.lexists(p),name
 else:assert p.is_file() and str(p.resolve())==value['realpath'] and H(p)==value['sha256'],name
print(json.dumps({'status':'PASS_INDEPENDENT_CLEAN_CARRY_PAIR_AUDIT','evidence_commit':'8e3bc09053','receipt_sha256':H(receipt),'recorded_outer_session':57568,'recorded_outer_exit':0,'parent_rerun_exit':0,'runs':rows,'direct_and_output_guard_slots':70,'lean_launched':False,'scope':'Conditional IΣ₁ carry reset with supplied finite family, CarryInput, predecessor, slack and optional target bound. No graph instantiation, word construction, machine or PRA/iPRA theorem. Inherited provider, sampled resource, dynamic import and between-check boundaries remain.'},indent=2))
