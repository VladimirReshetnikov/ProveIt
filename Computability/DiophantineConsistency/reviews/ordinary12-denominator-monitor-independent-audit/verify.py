#!/usr/bin/env python3
"""Replay independent fake-process controls and authenticate exact snapshots."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
PINS={'monitor-reviewed-bcf.py':'bcf08ab90070b83b2f30c1f0116c7088e1791a5679a4310b3b0375ad47dc5a2b',
      'monitor-corrected-ea4.py':'ea404d70c32a939423a792e856b3fd0cbe78aa93056b6a2d8e08bf7bd46c2c9e',
      'monitor-final-c5.py':'c5cc9ec88c7c7cf7b6ec47b26281259c698dbadbb7c87a96b68433e3bcb5d3b0',
      'composition-source-e8.lean':'e8e3b87727d21969a7d5d5380e9b21b141e56357fc1c5a0e0268a5c262947715'}


def need(ok,msg):
    if not ok:raise ValueError(msg)


def main():
    for name,h in PINS.items():need(hashlib.sha256((HERE/name).read_bytes()).hexdigest()==h,'snapshot '+name)
    old=(HERE/'monitor-corrected-ea4.py').read_bytes();new=(HERE/'monitor-final-c5.py').read_bytes()
    a=b'033da71d1b729fe51c9b24f3f42e1830f739d6ac207ea19a5d207e356de12b31'
    b=b'e8e3b87727d21969a7d5d5380e9b21b141e56357fc1c5a0e0268a5c262947715'
    need(old.count(a)==1 and old.replace(a,b)==new,'final driver differs beyond source pin')
    first=json.loads((HERE/'attempt01-terminal.json').read_bytes());second=json.loads((HERE/'attempt02-terminal.json').read_bytes())
    need(first['wrapper_actual_exit']==1 and first['child_actual_exit'] is None and first['status']=='FAILED_MONITOR_RACE_NO_PROOF_RECEIPT', 'first failed attempt')
    need(second['wrapper_actual_exit']==second['failed_compiler_exit']==1 and second['status']=='AUTHOR_COMPOSITION_COMPILER_FAILURE_NO_PAIRED_PROOF', 'second failed attempt')
    checks=[]
    for filename,status in [('test_sigterm.py','CONFIRMED_SIGTERM_GAP_WITH_CLEANUP'),
                            ('test_exception.py','PASS_CONFIRMED_TERM_IGNORING_DESCENDANT_EXCEPTION_CONTROL'),
                            ('test_corrected_signals.py','PASS_CORRECTED_EXTERNAL_SIGNAL_CONTROLS'),
                            ('test_thresholds.py','PASS_FAIL_CLOSED_FAKE_RESOURCE_CONTROLS')]:
        result=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/filename)],capture_output=True,text=True,timeout=40)
        need(result.returncode==0,'control exit '+filename+' '+result.stderr)
        value=json.loads(result.stdout);need(value['status']==status,'control status '+filename)
        checks.append({'script':filename,'exit':result.returncode,'result':value})
    print(json.dumps({'status':'PASS_INDEPENDENT_DENOMINATOR_MONITOR_REVIEW','snapshot_sha256':PINS,
      'final_driver_only_source_pin_changed':True,'first_attempt_wrapper_exit':1,'first_attempt_child_exit_observed':False,
      'second_attempt_wrapper_exit':1,'second_attempt_failed_compiler_exit':1,
      'original_author_controls_recheck_session':14750,'original_author_controls_recheck_exit':0,'checks':checks,
      'scope':'Fake-process sampled controls only; no Lean build, no hard quota, aggregate RSS, escaped-process guarantee or race-free process identity.'},indent=2))


if __name__=='__main__':main()
