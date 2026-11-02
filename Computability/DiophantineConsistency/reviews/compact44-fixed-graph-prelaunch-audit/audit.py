#!/usr/bin/env python3
"""Independent no-Lean fake-wrapper and exact-byte prelaunch checks."""
import hashlib,importlib.util,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent
DRIVER=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-fixed-graph-digits-prototype/replay.py'
DRIVER_SHA='2d026507536e6059adafdbd2b41a959da046dfbb9467d34207f1b80a1f2f08ae'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
if sha(DRIVER)!=DRIVER_SHA:raise ValueError('driver drift')
rel=DRIVER.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','3d331cd3bb:'+rel],cwd=ROOT,capture_output=True,check=True).stdout
if hashlib.sha256(blob).hexdigest()!=DRIVER_SHA:raise ValueError('commit bytes mismatch')
sp=importlib.util.spec_from_file_location('candidate',DRIVER);d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d)
for p,h in d.PINS.items():
 if sha(p)!=h:raise ValueError(('input pin drift',str(p)))
cases=['good','wrong_report','wrong_axiom','warning','sorry','compiler_exit','stop_reason','missing_output','wrong_deps','deps_exit','deps_stderr','missing_required','missing_required_6','missing_required_12','source_drift','parent_drift','sibling_mismatch','collision','symlink_output','late_source_drift','frozen_symlink','dependency_mutation','companion_creation','output_mutation']
results=[]
for case in cases:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'fake-wrapper.py'),case],text=True,capture_output=True,timeout=120)
 if q.returncode or q.stderr:raise ValueError(('fake wrapper failed',case,q.returncode,q.stderr,q.stdout))
 data=json.loads(q.stdout.strip().splitlines()[-1])
 if data['case']!=case or data['accepted']!=(case=='good'):raise ValueError(('fake result mismatch',case,data))
 if case=='good' and data['calls']!={'comp':12,'deps':12,'verify':2}:raise ValueError(('good fake loop count',data))
 results.append({'case':case,'accepted':data['accepted'],'compilers':data['calls']['comp'],'dependency_queries':data['calls']['deps']})
print(json.dumps({'status':'PASS_INDEPENDENT_FIXED_GRAPH_PRELAUNCH_FAKE_REVIEW','driver_sha256':DRIVER_SHA,'driver_commit':'3d331cd3bb','fixed_pins_checked':len(d.PINS),'fake_cases':results,'lean_launched':False,'scope':'No-Lean exact-byte and fake-wrapper checks; parent verify is recorded separately, and real Lean compilation is untested. Clean initial native loader, external stable HEAD and sole Lean slot required; resource monitoring is sampled, lean --deps has leader-only timeout, and package/dynamic/between-check limits remain.'},indent=2))
