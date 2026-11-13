#!/usr/bin/env python3
"""Exercise final wrapper paths and actual optimized-builder failure boundary."""
import hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];TASK=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/monitor';BUILDER=ROOT/'Computability/DiophantineConsistency/research/fresh-project-closure/rebuild.py';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
if len(sys.argv)!=2:raise ValueError('exact reviewed commit required')
commit=sys.argv[1]
for name in ('monitor.py','paired.py','path_guard.py','test_monitor.py','test_paired.py'):
 p=TASK/name;assert subprocess.check_output(['git','show',commit+':'+str(p.relative_to(ROOT))],cwd=ROOT)==p.read_bytes()
with tempfile.TemporaryDirectory(prefix='ipra-monitor-corrected-review-') as td:
 t=Path(td);snap=t/'snapshot';snap.mkdir();(snap/'manifest.json').write_text(json.dumps({'status':'INVALID','root':str(t),'order':[],'sources':{},'project_modules':0,'target':'not-present'}));pr=t/'provider-root';pr.mkdir();overlay=t/'overlay';overlay.mkdir();provider=t/'provider.json';provider.write_text(json.dumps({'root':str(pr),'overlay':str(overlay),'manifest_sha256':'invalid','status':'INVALID','exit_code':99,'declared_external_guard':{},'foundation_artifacts':{}}));fi=t/'foundation.json';fi.write_text(json.dumps({'lean_sha256':'invalid'}));comp=t/'comparator.py';comp.write_text('import json;print(json.dumps({"status":"MATCHED_PASS","rows":2}))\n')
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
 def args(out,builder):return [sys.executable,str(TASK/'paired.py'),'--output',str(out),'--snapshot',str(snap),'--snapshot-sha256',H(snap/'manifest.json'),'--provider-receipt',str(provider),'--provider-sha256',H(provider),'--foundation-input',str(fi),'--expected-axiom-reports','0','--builder',str(builder),'--comparator',str(comp),'--reserve-bytes','0','--budget-bytes','1000000','--interval','.02','--grace','.1']
 # With inherited PYTHONOPTIMIZE, the wrapper must refuse before creating its
 # output, hence before any builder process can start.
 opt=t/'optimized-pair';badenv=env.copy();badenv['PYTHONOPTIMIZE']='1';p=subprocess.run(args(opt,BUILDER),env=badenv,capture_output=True,text=True,timeout=10);assert p.returncode!=0 and not opt.exists() and 'optimized Python' in p.stderr
 # Run the actual historical builder through the wrapper on the same invalid
 # fake snapshot: its assertion must execute and reject the input. No Lean runs.
 normal=t/'normal-pair';p=subprocess.run(args(normal,BUILDER),env=env,capture_output=True,text=True,timeout=20);state=json.loads((normal/'pair-state.json').read_text());assert p.returncode!=0 and state['status']=='FAILED' and len(state['runs'])==1 and state['runs'][0]['builder_exit']!=0 and 'AssertionError' in (normal/'author/child.log').read_text() and not (normal/'author/child-output/state.json').exists()
 # Successful fake builder asserts the actual subprocess environment, and the
 # coordinator must record the guard module in fixed inputs.
 fake=t/'builder.py';fake.write_text('import argparse,json,os,pathlib,sys\np=argparse.ArgumentParser();p.add_argument("--output");a,_=p.parse_known_args()\nassert sys.flags.optimize==0 and "PYTHONOPTIMIZE" not in os.environ\no=pathlib.Path(a.output);o.mkdir();(o/"state.json").write_text(json.dumps({"status":"PASS","optimize":sys.flags.optimize}))\n');good=t/'good-pair';p=subprocess.run(args(good,fake),env=env,capture_output=True,text=True,timeout=20);state=json.loads((good/'pair-state.json').read_text());assert p.returncode==0 and state['status']=='MATCHED_PASS' and all(x['builder_exit']==0 for x in state['runs']) and str(TASK/'path_guard.py') in state['fixed_inputs_sha256']
 for out in (snap/'bad-pair',pr/'bad-pair',overlay/'bad-pair'):
  p=subprocess.run(args(out,fake),env=env,capture_output=True,text=True,timeout=10);assert p.returncode!=0 and not out.exists()
 link=t/'link';link.symlink_to(t/'target',target_is_directory=True);(t/'target').mkdir();out=link/'bad-pair';p=subprocess.run(args(out,fake),env=env,capture_output=True,text=True,timeout=10);assert p.returncode!=0 and not out.exists()
 # Standalone monitor accepts additional caller-provided protected roots.
 out=snap/'bad-monitor';p=subprocess.run([sys.executable,str(TASK/'monitor.py'),'--run-dir',str(out),'--protect',str(snap),'--reserve-bytes','0','--','/bin/true'],env=env,capture_output=True,text=True,timeout=10);assert p.returncode!=0 and not out.exists()
 out=t/'optimized-monitor';p=subprocess.run([sys.executable,str(TASK/'monitor.py'),'--run-dir',str(out),'--reserve-bytes','0','--','/bin/true'],env=badenv,capture_output=True,text=True,timeout=10);assert p.returncode!=0 and not out.exists()
r={'status':'PASS_INDEPENDENT_CORRECTED_MONITOR_CONTROLS','commit':commit,'monitor_sha256':H(TASK/'monitor.py'),'paired_sha256':H(TASK/'paired.py'),'path_guard_sha256':H(TASK/'path_guard.py'),'inherited_optimized_pair_rejected_before_output':True,'actual_historical_builder_assertion_observed':True,'fake_builder_optimization_disabled':True,'snapshot_provider_overlay_output_rejected':True,'symlink_ancestor_rejected':True,'standalone_monitor_explicit_protection_rejected':True,'scope':'Fake inputs and a real invalid-input builder invocation; no Lean compilation, real provider use, project build, hard quota or continuous reserve.'};out=HERE/'corrected-receipt.json'
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['status'],H(out))
