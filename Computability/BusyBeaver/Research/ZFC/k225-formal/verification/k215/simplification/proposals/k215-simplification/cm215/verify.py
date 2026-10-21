#!/usr/bin/env python3
"""Rebuild the CM215 relative proof in a clean directory; no network access.

Usage: python3 verify.py --lean /path/to/lean --output /new/output
Add --repo /path/to/pinned/ProveIt after that checkout has KDense215 compiled
in Computability/BusyBeaver/Lean/.lake/build/lib/lean to also verify the exact
repository-table bridge. No source file or input table is modified.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time

if not __debug__:
    raise SystemExit('Run with Python assertions enabled.')

HERE=Path(__file__).resolve().parent
REV='b6c7087477e51c017003bd729e712c8969733223'
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--lean',default='lean')
ap.add_argument('--repo',type=Path)
ap.add_argument('--output',required=True,type=Path)
a=ap.parse_args()
output=a.output.resolve();output.mkdir(parents=True,exist_ok=False)
lean=shutil.which(a.lean) or str(Path(a.lean).resolve())
version=subprocess.run([lean,'--version'],check=True,capture_output=True,text=True).stdout.strip()
assert '4.32.0' in version,version
sources=['PositiveStuttering.lean','CM215Data.lean','CM215Transfer.lean',
         'CM215CoreBridge.lean','BusyBeaver/Core.lean']
repo_build=None
if a.repo:
 repo=a.repo.resolve()
 head=subprocess.run(['git','-C',str(repo),'rev-parse','HEAD'],check=True,capture_output=True,text=True).stdout.strip()
 assert head==REV,head
 upstream=repo/'Computability/BusyBeaver/Lean/BusyBeaver/Core.lean'
 assert upstream.read_bytes()==(HERE/'BusyBeaver/Core.lean').read_bytes()
 repo_build=repo/'Computability/BusyBeaver/Lean/.lake/build/lib/lean'
 assert (repo_build/'BusyBeaver/ZFC/KDense215.olean').is_file()
 sources.append('CM215RepoBridge.lean')
results=[]
with tempfile.TemporaryDirectory(prefix='cm215-proof-') as td:
 work=Path(td)
 for p in sources+['generate_cm215_data.py','upstream/k215.native.tm','upstream/marker215.native.tm']:
  dest=work/p;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(HERE/p,dest)
 subprocess.run([sys.executable,'generate_cm215_data.py'],cwd=work,check=True)
 assert (work/'CM215Data.lean').read_bytes()==(HERE/'CM215Data.lean').read_bytes()
 assert (work/'cm215_state_map.json').read_bytes()==(HERE/'cm215_state_map.json').read_bytes()
 ordered=['BusyBeaver/Core.lean','PositiveStuttering.lean','CM215Data.lean',
          'CM215Transfer.lean','CM215CoreBridge.lean']
 if repo_build:ordered.append('CM215RepoBridge.lean')
 for p in ordered:
  env=dict(os.environ)
  # Root resolution is by package, so the repository comes first only for
  # the final module; all other modules use the vendored exact Core source.
  env['LEAN_PATH']=(str(repo_build)+os.pathsep if p=='CM215RepoBridge.lean' else '')+str(work)
  start=time.monotonic()
  proc=subprocess.run([lean,'-o',str(Path(p).with_suffix('.olean')),p],cwd=work,env=env,capture_output=True,text=True)
  secs=time.monotonic()-start
  log=proc.stdout+proc.stderr
  (output/(p.replace('/','_')+'.log')).write_text(log)
  record={'source':p,'sha256':hashlib.sha256((HERE/p).read_bytes()).hexdigest(),
          'exit_code':proc.returncode,'seconds':round(secs,3),'stdout_stderr':log}
  results.append(record)
  assert proc.returncode==0,record
  assert 'sorryAx' not in log,record
  assert 'warning:' not in log,record
summary={'status':'LEAN_KERNEL_PASS','lean_version':version,'repository_revision':REV,
         'repository_bridge_checked':bool(repo_build),'modules':results,
         'new_proof_lines':sum(len((HERE/p).read_text().splitlines()) for p in ['PositiveStuttering.lean','CM215Transfer.lean','CM215CoreBridge.lean','CM215RepoBridge.lean']),
         'generated_data_lines':len((HERE/'CM215Data.lean').read_text().splitlines()),
         'inherited_core_lines':len((HERE/'BusyBeaver/Core.lean').read_text().splitlines()),
         'formal_claim':'Exact CM215 and exact published K215 are equihalting; all-tape/head theorem from state0; existing ZFC calibration may be supplied to inherit_calibration.',
         'not_claimed':'Fresh compilation of the entire existing K215-to-ZFC closure, unconditional nonhalting, a new215 table, or a214 table.'}
(output/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='modules'},indent=2))
