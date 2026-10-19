#!/usr/bin/env python3
"""Bind the recorded full runtime results to the exact packaged inputs and code.

This checks evidence identity and its finite case census; use verify_runtime.py
to reconstruct the universal induction calculations from scratch.
"""
from pathlib import Path
import argparse,hashlib,json


def require(value,message):
    if not value:raise ValueError(message)


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def check(package):
    receipts=[]
    for name,table,source,count,total,rows in [
        ('k230','inputs/k230.tm','inputs/sites230_logical.json',6660,1605903,460),
        ('k228','machines/k228_original_labels.tm','machines/sites228.json',6656,1614426,456),
    ]:
        path=package/'evidence'/('runtime_'+name+'.json')
        r=json.loads(path.read_text())
        require(r['status']=='UNIVERSAL_MATHEMATICAL_PASS','Incomplete runtime receipt')
        require(r['table_sha256']==sha(package/table),'Runtime table hash mismatch')
        require(r['source_sha256']==sha(package/source),'Runtime source hash mismatch')
        for key,f in [('checker_sha256','verify_runtime.py'),('engine_sha256','symbolic_runtime.py'),('helper_sha256','source_semantics.py')]:
            require(r[key]==sha(package/'code'/f),'Runtime code hash mismatch: '+f)
        cpath=path.parent/r['cases_file']
        require(sha(cpath)==r['cases_sha256'],'Case-array hash mismatch')
        cases=json.loads(cpath.read_text());sites=json.loads((package/source).read_text())
        expected={(i,b) for i,(_,op,arg) in enumerate(sites) for b in ((False,True) if op=='CD' else(False,))}
        require(len(cases)==count==r['cases']==len(expected),'Wrong complete case count')
        require({(c['site_index'],c['positive']) for c in cases}==expected,'Missing guarded source case')
        require(sum(c['symbolic_steps'] for c in cases)==total==r['symbolic_steps'],'Wrong rule census')
        require(max(c['symbolic_steps'] for c in cases)==415==r['maximum_symbolic_steps'],'Wrong proof maximum')
        require(min(c['duration'][0] for c in cases)==13==r['minimum_actual_steps'],'Wrong positive progress')
        require(r['unused_rows']==[] and len(r['used_rows'])==rows==r['rows'],'Incomplete row coverage')
        receipts.append(dict(machine=name,cases=count,rules=total,rows=rows,status=r['status']))
    return receipts


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package',type=Path,default=Path(__file__).resolve().parent.parent)
    a=ap.parse_args()
    print(json.dumps(dict(status='PASS_RECORDED_RUNTIME_IDENTITY_AND_CENSUS',receipts=check(a.package)),indent=2))
