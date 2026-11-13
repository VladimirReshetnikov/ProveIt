#!/usr/bin/env python3
"""Fail-closed resource controls with temporary fake children only."""
import collections
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile

DRIVER=Path(__file__).resolve().parent/'monitor-corrected-ea4.py'
EXPECTED='ea404d70c32a939423a792e856b3fd0cbe78aa93056b6a2d8e08bf7bd46c2c9e'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def main():
    need(hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'driver pin')
    spec=importlib.util.spec_from_file_location('audited_threshold_monitor',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    with tempfile.TemporaryDirectory(prefix='monitor-threshold-audit-') as td:
        root=Path(td);seen=[];env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
        cmd=[sys.executable,'-I','-S','-c','import time;time.sleep(20)']
        def sample(value):
            def reader(pid):seen.append(pid);return value
            return reader
        cases=[]
        for label,reader,timeout in [('missing',sample(None),180),('rss',sample(int(3.5*1024**3)+1),180),('timeout',sample(1),-1)]:
            code,peak,reason=m.monitored(cmd,env,root/(label+'.log'),timeout=timeout,rss_reader=reader)
            expected={'missing':'rss_unavailable_while_unreaped','rss':'sampled_rss_above_3.5GiB','timeout':'timeout'}[label]
            need(reason==expected and code!=0,'fail-closed '+label)
            pid=seen[-1];need(not Path(f'/proc/{pid}').exists(),'fake leader not reaped '+label)
            cases.append({'case':label,'child_exit':code,'reason':reason,'leader_reaped':True})
        original=m.shutil.disk_usage
        try:
            m.shutil.disk_usage=lambda _:collections.namedtuple('Usage','total used free')(1,1,0)
            code,peak,reason=m.monitored(cmd,env,root/'disk.log',rss_reader=sample(1))
        finally:m.shutil.disk_usage=original
        need(reason=='sampled_free_below_4GiB' and code!=0 and not Path(f'/proc/{seen[-1]}').exists(),'fail-closed disk')
        cases.append({'case':'disk','child_exit':code,'reason':reason,'leader_reaped':True})
    print(json.dumps({'status':'PASS_FAIL_CLOSED_FAKE_RESOURCE_CONTROLS','driver_sha256':EXPECTED,'cases':cases,
          'scope':'Injected samples and fake direct leaders only; no process-tree RSS, continuous sampling or hard quota claim.'},indent=2))


if __name__=='__main__':main()
