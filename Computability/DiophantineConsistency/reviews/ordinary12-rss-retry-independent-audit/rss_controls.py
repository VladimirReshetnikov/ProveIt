#!/usr/bin/env python3
"""Actual fake-child controls of the bounded missing-RSS retry."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
DRIVER=HERE/'driver-2c8.py'
EXPECTED='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def main():
    need(hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'driver pin')
    spec=importlib.util.spec_from_file_location('rss_retry_review',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    orig=m.Path
    class Fake:
        def __init__(self,value):self.value=value
        def read_text(self):return 'Name:\tfake\nVmRSS:\t'+self.value+' kB\n'
    try:
        m.Path=lambda _:Fake('0');need(m.rss_bytes(1) is None,'zero RSS must be unavailable')
        m.Path=lambda _:Fake('23');need(m.rss_bytes(1)==23*1024,'positive RSS conversion')
    finally:m.Path=orig
    env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None);cases=[]
    with tempfile.TemporaryDirectory(prefix='rss-retry-audit-') as tmp:
      root=Path(tmp)
      def run(label,duration,reader):
        cmd=[sys.executable,'-I','-S','-c',f'import time;time.sleep({duration})']
        start=time.monotonic();code,peak,reason=m.monitored(cmd,env,root/(label+'.log'),rss_reader=reader)
        return code,peak,reason,round(time.monotonic()-start,3)
      c,p,r,e=run('persistent',5,lambda _:None)
      need(c!=0 and p==0 and r=='rss_unavailable_while_unreaped' and .8<=e<4,'persistent unmeasurable child')
      cases.append({'case':'persistent_missing','child_exit':c,'reason':r,'elapsed_seconds':e})
      calls=[]
      def recovering(pid):
        calls.append(pid);return None if len(calls)<=2 else 8192
      c,p,r,e=run('transient',1.2,recovering)
      need(c==0 and p==8192 and r is None and len(calls)>=3,'transient recovery')
      cases.append({'case':'transient_then_valid','child_exit':c,'reason':r,'calls':len(calls),'peak':p})
      def delayed_missing(_):time.sleep(.35);return None
      c,p,r,e=run('fast-no-sample',.1,delayed_missing)
      need(c==0 and p==0 and r=='no_rss_observation','fast exit without a sample')
      cases.append({'case':'exit_without_sample','child_exit':c,'reason':r,'peak':p})
      calls=[]
      def exit_after_sample(pid):
        calls.append(pid)
        if len(calls)==1:return 8192
        time.sleep(.5);return None
      c,p,r,e=run('exit-after-sample',1.15,exit_after_sample)
      need(c==0 and p==8192 and r is None and len(calls)>=2,'exit race after valid sample')
      cases.append({'case':'exit_after_valid_sample','child_exit':c,'reason':r,'peak':p})
    print(json.dumps({'status':'PASS_INDEPENDENT_RSS_RETRY_CONTROLS','driver_sha256':EXPECTED,'zero_rss_is_unavailable':True,
      'cases':cases,'scope':'Actual fake leaders and injected RSS observations; no Lean build, continuous bound, process-tree RSS or adversarial race guarantee.'},indent=2))


if __name__=='__main__':main()
