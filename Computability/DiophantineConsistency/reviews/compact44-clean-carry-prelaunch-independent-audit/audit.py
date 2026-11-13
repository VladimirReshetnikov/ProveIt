#!/usr/bin/env python3
"""Independent exact-byte, pin and no-Lean fake-wrapper checks."""
import hashlib,importlib.util,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent
DRIVER=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-clean-carry-reset-prototype/replay.py'
D='52398e50ee91cca62829739abde44205a852574d6812ce4ba38a4c0d6b7d33d4'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(DRIVER)==D
old=subprocess.run(['git','show','135406f6b5:'+DRIVER.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout
assert hashlib.sha256(old).hexdigest()==D
sp=importlib.util.spec_from_file_location('candidate',DRIVER);d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d)
for p,h in d.PINS.items():assert H(p)==h,('input pin',str(p))
cases=['good','seed_collision','seed_companion','output_symlink','missing_output','output_companion','output_collision','final_output_companion','peer_mismatch','late_source_drift','frozen_symlink','seed_mutation','seed_companion_creation','wrong_report','wrong_axiom','warning','sorry','compiler_exit','stop_reason','parent_drift','final_source_drift','missing_required','wrong_deps','deps_exit','deps_stderr'];results=[]
for case in cases:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'fake-wrapper.py'),case],text=True,capture_output=True,timeout=120)
 if q.returncode or q.stderr:raise ValueError(('fake wrapper failed',case,q.returncode,q.stderr,q.stdout))
 data=json.loads(q.stdout.strip().splitlines()[-1]);assert data['case']==case and data['accepted']==(case=='good')
 if case=='good':assert data['calls']=={'comp':2,'deps':2,'verify':2}
 results.append({'case':case,'accepted':data['accepted'],'compilers':data['calls']['comp'],'dependency_queries':data['calls']['deps']})
print(json.dumps({'status':'PASS_INDEPENDENT_CLEAN_CARRY_PRELAUNCH_FAKE_REVIEW','driver_commit':'135406f6b5','driver_sha256':D,'fixed_pins_checked':len(d.PINS),'fake_cases':results,'lean_launched':False,'scope':'Exact-byte, input-pin and fake-wrapper checks; separate actual parent verify is recorded in verify.log. No real Lean build. Initial native loader, externally stable HEAD, exclusive Lean slot, sampled resources and package, dynamic import and between-check limits remain.'},indent=2))
