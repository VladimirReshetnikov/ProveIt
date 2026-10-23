#!/usr/bin/env python3
"""Rebuild and audit the complete delivered synthesis, using only stdlib.

Finite audit results do not decide consistency, solvability, or the inherited
unbounded compiler theorem. The mathematical proof is report.tex/report.pdf.
"""
from pathlib import Path
import gzip
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'
PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def read(path):
    return json.loads((ROOT/path).read_text())

def run(relative, *arguments):
    script=ROOT/relative
    env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    p=subprocess.run([sys.executable,str(script),*map(str,arguments)],
                     cwd=script.parent,env=env,capture_output=True,text=True)
    logfile=relative.replace('/','_').replace('.py','.log.txt')
    (EVIDENCE/logfile).write_text(p.stdout+p.stderr)
    require(p.returncode==0,f'{relative} failed; see evidence/{logfile}')
    print(f'PASS {relative}',flush=True)
    return {'script':relative,'exit_code':p.returncode,'log':logfile}

def check_nodes(data, count, operations, degree):
    nodes=data['nodes']; live=set();todo=[data['output']]
    for index,n in enumerate(nodes):
        if n['kind'] in ('add','sub','mul'):
            require(0<=n['left']<index and 0<=n['right']<index,'Bad node order')
    while todo:
        index=todo.pop()
        if index in live:continue
        live.add(index);n=nodes[index]
        if n['kind'] in ('add','sub','mul'):todo.extend([n['left'],n['right']])
    variables=[n['name'] for n in nodes if n['kind']=='variable']
    require(len(variables)==len(set(variables))==count,'Wrong variable count')
    require(set(variables)==set(data['variables']),'Variable-list discrepancy')
    require(len(live)==len(nodes),'Dead nodes present')
    actual=sum(n['kind'] in ('add','sub','mul') for n in nodes)
    require(actual==operations,'Wrong operation count')
    require(data['exact_degree']==degree,'Wrong declared degree')
    return {'variables':count,'operations':actual,'exact_degree':degree,
            'fixed_leaves':sum(n['kind']=='fixed' for n in nodes),
            'all_nodes_live':True}

def main():
    EVIDENCE.mkdir(exist_ok=True)
    steps=[]
    steps.append(run('compiler/build_coefficients.py'))
    steps.append(run('compiler/audit_independent.py'))
    binding_path=ROOT/'compiler/coefficients/COEFFICIENT_BINDING.json'
    steps.append(run('positive/optimize_positive.py','--coefficient-binding',binding_path))
    steps.append(run('positive/review_signed_reductions.py'))
    steps.append(run('integer15/build_signed15.py'))
    steps.append(run('integer16/build_signed16.py'))
    steps.append(run('integer15/check_new_lemmas.py'))

    results={}
    results['integer15']=check_nodes(read('integer15/generated/signed15.json'),
                                     15,1541,813056*5**33+4184)
    results['integer16']=check_nodes(read('integer16/generated/signed16.json'),
                                     16,1550,406528*5**33+10008)
    binding=read('compiler/coefficients/COEFFICIENT_BINDING.json')
    digest=hashlib.sha256(binding_path.read_bytes()).hexdigest()
    for name,ops in [('positive12_product108',108),('positive12_system104',104),
                     ('positive12_shifted_system103',103)]:
        data=read('positive/'+name+'.json')
        require(len(data['source'])==ops,'Positive circuit operation count')
        require(len(data['witnesses'])==12,'Positive witness count')
        require(data['coefficient_binding']==binding,'Partial or stale coefficient tuple')
        require(data['binding_file_sha256']==digest,'Binding hash mismatch')
        location=ROOT/'positive'/data['coefficient_binding_file']
        require(location.resolve()==binding_path.resolve(),'Unresolvable binding file')
        results[name]={'variables':12,'operations':ops,'binding_sha256':digest}
    raw_total=0
    for item in binding['files']:
        raw=gzip.decompress((binding_path.parent/item['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==item['sha256'],'Payload hash mismatch')
        require(len(raw)==item['bytes'],'Payload byte length')
        require(int.from_bytes(raw,'little').bit_length()==item['bit_length'],'Payload bits')
        raw_total+=len(raw)
    require(raw_total==533099,'Unexpected total coefficient bytes')
    results['compiler']={'base_exponent':1064921,'raw_bytes':raw_total,
                         'gzip_bytes':binding['total_gzip_bytes'],
                         'full_binding_sha256':digest}
    report={'status':'PASS','source_commit':PIN,'steps':steps,'results':results,
            'scope':'Finite reproducibility, circuit, degree, identity and binding audits; no consistency decision or new end-to-end formal certificate.'}
    (EVIDENCE/'VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'RESULTS.json').write_text(json.dumps({'source_commit':PIN,**results},indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
