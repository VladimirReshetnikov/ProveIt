#!/usr/bin/env python3
"""Reproduce protected-output guard gaps of the original monitor/coordinator."""
import hashlib,json,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];TASK=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/monitor'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
original={}
for n in ('monitor.py','paired.py','test_monitor.py','test_paired.py'):
 p=TASK/n;original[n]=subprocess.check_output(['git','show','49377c7490:'+str(p.relative_to(ROOT))],cwd=ROOT)
with tempfile.TemporaryDirectory(prefix='ipra-monitor-original-review-') as td:
 top=Path(td);archived=top/'archived';archived.mkdir()
 for n,raw in original.items():(archived/n).write_bytes(raw)
 snapshot=top/'snapshot';snapshot.mkdir();(snapshot/'manifest.json').write_text('{}');provider=top/'provider';provider.mkdir();(provider/'receipt.json').write_text('{}');foundation=top/'foundation.json';foundation.write_text('{}');dummy=top/'dummy.py';dummy.write_text('')
 # A deliberately invalid snapshot digest prevents any child launch. The old
 # coordinator still creates its directory and failed-state file in provider.
 pairout=provider/'unwanted-pair';cmd=[sys.executable,str(archived/'paired.py'),'--output',str(pairout),'--snapshot',str(snapshot),'--snapshot-sha256','0','--provider-receipt',str(provider/'receipt.json'),'--provider-sha256',H(provider/'receipt.json'),'--foundation-input',str(foundation),'--expected-axiom-reports','0','--builder',str(dummy),'--comparator',str(dummy)]
 proc=subprocess.run(cmd,capture_output=True,text=True,timeout=10);assert proc.returncode==1 and json.loads((pairout/'pair-state.json').read_text())['status']=='FAILED'
 # Preflight stop prevents child launch but the old monitor writes its own
 # terminal state inside the snapshot before checking any protected roots.
 run=snapshot/'unwanted-monitor';cmd=[sys.executable,str(archived/'monitor.py'),'--run-dir',str(run),'--reserve-bytes','999999999999999999','--','/bin/true'];proc=subprocess.run(cmd,capture_output=True,text=True,timeout=10);assert proc.returncode==1 and json.loads((run/'terminal.json').read_text())['status']=='STOPPED_BEFORE_LAUNCH'
r={'status':'PASS_INDEPENDENT_ORIGINAL_MONITOR_PATH_REVIEW','source_commit':'49377c7490','monitor_sha256':hashlib.sha256(original['monitor.py']).hexdigest(),'paired_sha256':hashlib.sha256(original['paired.py']).hexdigest(),'pair_nested_provider_created_before_bad_pin_rejection':True,'monitor_nested_snapshot_created_before_preflight_stop':True,'scope':'Isolated fake roots; no Lean project build, provider mutation or network action.'};out=HERE/'original-receipt.json'
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['status'],H(out))
