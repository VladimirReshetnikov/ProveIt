#!/usr/bin/env python3
"""Exercise sampled monitor stop reasons using harmless sleeping children."""
import importlib.util
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[4]
SOURCE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
spec=importlib.util.spec_from_file_location('monitor_control',SOURCE)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
cmd=[sys.executable,'-I','-S','-c','import time;time.sleep(30)']
with tempfile.TemporaryDirectory(prefix='prefix-resource-control-') as t:
    root=Path(t);env=os.environ.copy()
    code,peak,reason=m.monitored(cmd,env,root/'rss.log',rss_reader=lambda _:4*1024**3)
    if code==0 or reason!='sampled_rss_above_3.5GiB':raise ValueError(('RSS control',code,peak,reason))
    old=m.shutil.disk_usage
    try:
        m.shutil.disk_usage=lambda _:SimpleNamespace(free=0)
        code,peak,reason=m.monitored(cmd,env,root/'disk.log',rss_reader=lambda _:1024)
    finally:m.shutil.disk_usage=old
    if code==0 or reason!='sampled_free_below_4GiB':raise ValueError(('disk control',code,peak,reason))
    code,peak,reason=m.monitored(cmd,env,root/'timeout.log',timeout=.1,rss_reader=lambda _:1024)
    if code==0 or reason!='timeout':raise ValueError(('timeout control',code,peak,reason))
print('PASS_SAMPLED_RSS_DISK_TIMEOUT_CONTROLS')
