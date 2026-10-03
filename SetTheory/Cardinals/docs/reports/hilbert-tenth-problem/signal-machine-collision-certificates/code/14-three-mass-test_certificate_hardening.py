#!/usr/bin/env python3
"""Strict JSON numeric types and caller-owned descriptor mutation regressions."""
import argparse,copy,hashlib,importlib.util,json,sys
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent);a=p.parse_args();S=a.source_dir.resolve();R=a.output_dir.resolve();R.mkdir(parents=True,exist_ok=True)
def source(n):
    path=S/(n+'_snapshot.py')
    return path if path.exists() else S/(n+'.py')
def module(n):
    s=importlib.util.spec_from_file_location(n,source(n));m=importlib.util.module_from_spec(s);sys.modules[n]=m;s.loader.exec_module(m);return m
C=module('certificate');K=module('checker');checks=[];defects=[]
def reject(label,f):
    try:f()
    except (ValueError,TypeError):checks.append(label);return
    defects.append(label)
for counter in (True,False,1.0,0.0,'0',None):
    reject('instruction counter '+repr(counter),lambda counter=counter:C.Machine(('run','halt'),'halt',(C.Instruction('run','halt','inc',counter),)).validate())
# Do not let a caller mutate a once-created source machine by editing its lists.
states=['run','halt'];instructions=[C.Instruction('run','halt','nop',0)];m=C.Machine(states,'halt',instructions);states.append('foreign');instructions.clear()
if tuple(m.states)!=('run','halt') or len(m.instructions)!=1:defects.append('caller-owned Machine lists retained')
else:checks.append('Machine source descriptors snapshotted')
# All exported source/specification data must be detached from caller mutation.
m=C.Machine(('run','halt'),'halt',(C.Instruction('run','halt','nop',0),));inp={'mode':'fixed_raw','N':1};out={'mode':'free'};time={'mode':'free'};cert=C.export_certificate(m,'run',1,inp,out,time);before=copy.deepcopy(cert)
inp['N']=999;out['name']='changed';time['name']='changed'
if cert!=before:defects.append('caller-owned input/output/time specifications retained')
else:checks.append('export specifications deep copied')
cert=C.export_certificate(m,'run',1,{'mode':'fixed_raw','N':1},{'mode':'free'},{'mode':'free'});cert['expanded_polynomial']=C.expand_polynomial(cert);w=C.make_witness(cert);K.check(cert,w)
paths=[]
def collect(x,path=()):
    if type(x) is int:paths.append(path)
    elif isinstance(x,dict):
        for k,v in x.items():collect(v,path+(k,))
    elif isinstance(x,list):
        for k,v in enumerate(x):collect(v,path+(k,))
collect(cert)
for path in paths:
    original=cert
    for k in path:original=original[k]
    for converted in ([float(original)] + ([bool(original)] if original in (0,1) else [])):
        c=copy.deepcopy(cert);target=c
        for k in path[:-1]:target=target[k]
        target[path[-1]]=converted
        reject('serialized pseudo-integer '+repr(path)+' '+type(converted).__name__,lambda c=c:K.check(c,w))
report={'status':'PASS' if not defects else 'DEFECT_FOUND','source_sha256':{n:hashlib.sha256(source(n).read_bytes()).hexdigest() for n in ('certificate','checker')},'checks_passed':len(checks),'defects':defects,'strict_numeric_rejections':len(checks)-sum(not x.startswith('serialized') for x in checks)}
(R/'hardening-receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
