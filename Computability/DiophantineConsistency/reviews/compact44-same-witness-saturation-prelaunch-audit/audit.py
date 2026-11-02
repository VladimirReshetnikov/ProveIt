#!/usr/bin/env python3
"""No-Lean audit of the pinned paired driver and independent fake controls."""
import hashlib, importlib.util, json, os, subprocess, sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke with python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
root=here.parents[1]
driver=root/'research/ordinary12-ipra-bridge/compact44-same-witness-saturation-pair-prototype/replay.py'
expected='0fa6af3af3c3dbf9af4513237fb81bf83f0c1a6db679f8f20dd891a5c473921b'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(cond,msg):
    if not cond:raise ValueError(msg)
need(driver.is_file() and sha(driver)==expected,'reviewed driver drift')
spec=importlib.util.spec_from_file_location('reviewed',driver);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for path,digest in m.PINS.items():need(path.is_file() and sha(path)==digest,('input drift',str(path)))
preflight=json.loads((here/'observations/parent-preflight.stdout').read_bytes())
need(preflight=={'status':'PASS_SAME_WITNESS_SATURATION_READ_ONLY_PREFLIGHT','driver_sha256':expected,'expected_head':'2433689aa3348737311b432baa295aba204ce14b','source_modules':3,'parent_audit_status':'PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT','lean_launched':False},'preflight evidence mismatch')
need((here/'observations/parent-preflight.stderr').read_bytes()==b'','preflight stderr')
run=subprocess.run([sys.executable,'-I','-S','-B',str(here/'fake-wrapper.py')],capture_output=True,timeout=180)
need(run.returncode==0 and not run.stderr and run.stdout==(here/'observations/fake-controls.log').read_bytes(),('independent fake loop',run.returncode,run.stderr))
lines=run.stdout.decode().splitlines()
for case in ('verify_only','good','duplicate_init','triple_init','output_symlink','missing_output','dependency_mutation','dependency_companion','frozen_late_bytes','late_companion','output_companion_last','output_companion_peer'):
    need(any(line.startswith(case+' PASS ') for line in lines),('missing control',case))
opt=subprocess.run([sys.executable,'-I','-S','-B','-O',str(driver),'--help'],capture_output=True,timeout=30)
need(opt.returncode!=0 and b'without optimization' in opt.stderr,'optimized driver accepted')
print(json.dumps({'status':'PASS_INDEPENDENT_SAME_WITNESS_SATURATION_PRELAUNCH','reviewed_commit':'1585d69dad','driver_sha256':expected,'recorded_preflight_head':preflight['expected_head'],'recorded_preflight_session':57195,'recorded_preflight_exit':0,'lean_launched':False,'source_modules':3,'fake_success_children':6,'fake_control_lines':len(lines),'additional_controls':['triple_init','output_symlink','missing_output','dependency_mutation','dependency_companion','frozen_late_bytes'],'optimized_driver_rejected':True,'fixed_input_pins_checked':len(m.PINS),'limits':'Fake processes and point-in-time guards; separately retained real parent preflight. Clean initial loader, stable HEAD, sole Lean and independent artifact review still required.'},sort_keys=True))
