#!/usr/bin/env python3
"""Replay independent fake-process RSS and signal controls."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
EXPECTED='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def main():
    need(hashlib.sha256((HERE/'driver-2c8.py').read_bytes()).hexdigest()==EXPECTED,'driver snapshot')
    earlier=json.loads((HERE/'rebuild03-terminal.json').read_bytes())
    need(earlier['wrapper_actual_exit']==1 and earlier['stopped_compiler_actual_exit']==0 and
         earlier['status']=='FAILED_CLOSED_RSS_SAMPLE_NO_PAIRED_PROOF' and
         earlier['stop_reason']=='rss_unavailable_while_unreaped','previous failed-closed run')
    results=[]
    for script,status in [('rss_controls.py','PASS_INDEPENDENT_RSS_RETRY_CONTROLS'),
                          ('signal_controls.py','PASS_CORRECTED_EXTERNAL_SIGNAL_CONTROLS')]:
        p=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/script)],capture_output=True,text=True,timeout=30)
        need(p.returncode==0,'control exit '+script+' '+p.stderr)
        result=json.loads(p.stdout);need(result['status']==status and result['driver_sha256']==EXPECTED,'control result '+script)
        results.append({'script':script,'exit':p.returncode,'result':result})
    print(json.dumps({'status':'PASS_INDEPENDENT_BOUNDED_RSS_RETRY_REVIEW','driver_sha256':EXPECTED,
      'prior_wrapper_exit':1,'prior_stopped_compiler_exit':0,'prior_run_accepted':False,'checks':results,
      'scope':'Fake-process controls and point-in-time driver snapshot only; no Lean replay, execution-time manifest authentication, aggregate RSS or hard quota.'},indent=2))


if __name__=='__main__':main()
