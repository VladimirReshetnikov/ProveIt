#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';PLAN=BASE/'free-j-symbolic-congruence-closure-plan';OLD=BASE/'free-j-first-congruence-closure-plan';SRC=BASE/'free-j-symbolic-congruence-prototype/FreeJGraphCongruenceExplore.lean';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

for name in ('scan.py','scan.json','README.md'):
 p=PLAN/name; q=subprocess.run(['git','show','66eebf0216:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True); assert hashlib.sha256(q.stdout).hexdigest()==H(p),(name,'plan drift')
expected=json.loads((PLAN/'scan.json').read_bytes()); first=json.loads((OLD/'scan.json').read_bytes()); q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120);assert q.returncode==0 and not q.stderr and json.loads(q.stdout)==expected
q=subprocess.run([sys.executable,'-I','-S','-O','-B',str(PLAN/'scan.py')],capture_output=True,text=True,timeout=120);assert q.returncode!=0 and 'requires nonoptimized' in q.stderr
for k in ('objects','direct_project_companion_slots','package_init','imports'):assert expected[k]==first[k],k
sha='d748f8bbad7a45a328322eec1acd4643bc3e2c3f40d015b6b653f790fd8978d0';assert H(SRC)==sha
q=subprocess.run(['git','show','f3afbc380f:'+SRC.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True);assert hashlib.sha256(q.stdout).hexdigest()==sha
objects=expected['objects'];assert len(objects)==143
for z in objects:
 for side in ('author_resolved','peer_resolved'):
  p=Path(z[side]);assert p.is_file() and H(p)==z['sha256']
slots=expected['direct_project_companion_slots'];assert len(slots)==40
for path,v in slots.items():
 p=Path(path)
 if v is None:assert not os.path.lexists(p)
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256']
print(json.dumps({'status':'PASS_INDEPENDENT_SYMBOLIC_CONGRUENCE_SOURCE_CLOSURE','scan_commit':'66eebf0216','source_commit':'f3afbc380f','source_sha256':sha,'matching_objects_per_side':143,'direct_slots_checked':40,'normal_scan_exit':0,'optimized_scan_rejected':True,'lean_launched':False,'scope':'Point-in-time source and provider inventory only; no parent audit rerun, coherent paired compilation, retained K binding, word construction, machine correctness or iPRA proof.'},indent=2))
