#!/usr/bin/env python3
"""No-Lean negative and process-fixture checks for the draft client packet."""
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
r=load('client_control_runner',HERE/'runner.py');s=load('client_control_supervisor',HERE/'extension_supervisor.py');owned=load('client_control_owned',HERE/'owned.py')
results={}
def expect(label,fn,word):
    try:fn()
    except Exception as exc:
        if word not in repr(exc):raise
        results[label]=repr(exc)
    else:raise RuntimeError('unexpected acceptance '+label)

good="'Sample.x' depends on axioms: [propext, Quot.sound]\n"
assert r.reports(good,['Sample.x'])==[('Sample.x','propext, Quot.sound')]
results['expected_axioms_accepted']=True
expect('forged_axiom_name',lambda:r.reports(good,['Other.x']),'axiom names mismatch')
expect('unexpected_axiom',lambda:r.reports("'Sample.x' depends on axioms: [sorryAx]\n",['Sample.x']),'sorry')
expect('warning_rejected',lambda:r.reports(good+'warning: injected\n',['Sample.x']),'warning')
expect('non_whitelisted_axiom',lambda:r.reports("'Sample.x' depends on axioms: [Alien.axiom]\n",['Sample.x']),'unexpected axiom')
class Child:
    def __init__(self):self.n=0
    def wait(self):
        self.n+=1
        if self.n==1:raise RuntimeError('transient wait failure')
        return 17
child=Child();old=s.time.sleep;s.time.sleep=lambda _:None
try:code,errors=s.wait_owned(child)
finally:s.time.sleep=old
assert child.n==2 and code==17 and errors
results['supervisor_wait_retries_and_records_exception']=True
samples=[]
code,_,receipt=owned.run([sys.executable,'-c','pass'],cwd=HERE,env=os.environ,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,
                          timeout=10,disk_check=lambda pid:samples.append(pid) or True,poll_interval=.03)
assert code==0 and samples and receipt['pid']==samples[0] and receipt['session_drained'] and receipt['direct_child_reaped']
results['owned_success_sample_and_reap']=True
expect('late_finish_rejected',lambda:owned.run([sys.executable,'-c','import time; time.sleep(.08)'],
    cwd=HERE,env=os.environ,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,
    timeout=.03,disk_check=lambda pid:True,poll_interval=.2),'finished outside resource bounds')
assert not r.OUT.exists() and not s.OUT.exists() and not s.COORD_OUT.exists()
for label,path in [('runner_refuses_running_base',HERE/'runner.py'),('supervisor_refuses_running_base',HERE/'extension_supervisor.py')]:
    p=subprocess.run([sys.executable,'-I','-S','-B',str(path)],capture_output=True,text=True,timeout=60)
    assert p.returncode and 'base watchdog has not completed successfully' in p.stderr, (label,p.returncode,p.stderr)
    results[label]={'exit':p.returncode,'stderr':p.stderr.strip()}
assert not r.OUT.exists() and not s.OUT.exists() and not s.COORD_OUT.exists()
optimized=subprocess.run([sys.executable,'-I','-O','-S','-B',str(HERE/'controls.py')],capture_output=True,text=True)
assert optimized.returncode and 'refusing optimized Python' in optimized.stderr
results['optimized_controls_refused']=True
receipt={'status':'PASS','controls':results,'scope':'No Lean; fixture controls and preterminal refusal only.',
         'files_sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in ('runner.py','owned.py','extension_supervisor.py','controls.py')}}
with (HERE/'controls-observation.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(receipt,sort_keys=True))
