#!/usr/bin/env python3
"""Independent no-Lean fake-wrapper and exact-byte radix prelaunch review."""
import hashlib,importlib.util,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent;DRIVER=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-graph-derived-radix-prototype/replay.py';D='2f5aa4f8916f37263ab0534baed737137ee3a59083440f8063ba01749c7bec10'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(DRIVER)==D
rel=DRIVER.relative_to(ROOT).as_posix();old=subprocess.run(['git','show','21c8e39318:'+rel],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(old).hexdigest()==D
sp=importlib.util.spec_from_file_location('candidate',DRIVER);d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d)
for p,h in d.PINS.items():assert H(p)==h,('input pin',str(p))
cases=['good','wrong_report','wrong_axiom','warning','sorry','compiler_exit','stop_reason','missing_output','wrong_deps','deps_exit','deps_stderr','missing_required','missing_required_3','missing_required_6','source_drift','parent_drift','sibling_mismatch','collision','symlink_output','late_source_drift','frozen_symlink','dependency_mutation','companion_creation','output_mutation'];results=[]
for case in cases:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'fake-wrapper.py'),case],text=True,capture_output=True,timeout=120)
 if q.returncode or q.stderr:raise ValueError(('fake wrapper failed',case,q.returncode,q.stderr,q.stdout))
 data=json.loads(q.stdout.strip().splitlines()[-1]);assert data['case']==case and data['accepted']==(case=='good')
 if case=='good':assert data['calls']=={'comp':6,'deps':6,'verify':2}
 results.append({'case':case,'accepted':data['accepted'],'compilers':data['calls']['comp'],'dependency_queries':data['calls']['deps']})
print(json.dumps({'status':'PASS_INDEPENDENT_GRAPH_RADIX_PRELAUNCH_FAKE_REVIEW','driver_commit':'21c8e39318','driver_sha256':D,'fixed_pins_checked':len(d.PINS),'fake_cases':results,'lean_launched':False,'scope':'No-Lean exact-byte and fake-wrapper checks; actual full parent verify is recorded separately. Real Lean compilation is untested. Clean initial loader, externally stable HEAD, sole Lean and sampled/package/dynamic/between-check limits remain.'},indent=2))
