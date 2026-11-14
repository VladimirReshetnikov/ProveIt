#!/usr/bin/env python3
"""Fast offline checks for the delivered PA196 research packet.

These checks establish the explicitly listed finite facts. They do not
claim to verify a new binary machine or a PA consistency biconditional.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent

def need(test,message):
    if not test:raise ValueError(message)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def run(script,*args):
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    r=subprocess.run([sys.executable,str(script),*map(str,args)],check=True,capture_output=True,text=True,env=env)
    return json.loads(r.stdout)

def table(path,expected,halt):
    rows={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in rows and b in (0,1) and w in (0,1) and d in ('L','R'),'Invalid TM row')
        rows[q,b]=(w,d,z)
    states={q for q,b in rows}
    need(len(states)==expected and len(rows)==2*expected,'State/row census failed')
    need(set(rows)=={(q,b)for q in states for b in (0,1)},'Partial machine')
    need({z for w,d,z in rows.values()}-states=={halt},'Wrong terminal control')
    return {'working_states':len(states),'rows':len(rows),'halt':halt,'sha256':sha(path)}

def main():
    manifest=HERE/'SHA256SUMS.json'
    if manifest.exists():
        for name,digest in json.loads(manifest.read_text()).items():
            need(sha(HERE/name)==digest,'File identity differs: '+name)
    need(sha(HERE/'data/pa196.tm')=='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8','Wrong PA196 input')
    tables={n:table(HERE/'data'/f'{n}.tm',count,halt)for n,count,halt in [('pa196',196,196),('pa209',209,215)]}
    audit=load_module('source_audit',HERE/'source_reductions/audit_source_graphs.py')
    original=audit.lean_rows(HERE/'data/Program.lean');g,info=audit.audit(original)
    summary={'upstream':info}
    for name,count in [('source157',157),('layout158',158),('essential158',158)]:
        path=HERE/'source_reductions'/f'{name}.json';rows=json.loads(path.read_text());gg,ii=audit.audit(rows)
        need(gg==g,'Complete source CFG differs: '+name)
        need([r[1:]for r in rows]==[r[1:]for r in original],'Leaf operation sequence differs')
        need(ii['distinct_internal_nodes']==count and len(rows)==3812,'Wrong source count')
        ii['sha256']=sha(path);summary[name]=ii
    # Independently parse the generated definitions-only Lean witness.
    generated=audit.lean_rows(HERE/'source_reductions/Compact157.lean')
    need(generated==json.loads((HERE/'source_reductions/source157.json').read_text()),'Lean data do not encode the supplied source')
    # Nonvacuous graph comparison control: change one register operand.
    altered=[r[:] for r in original];i=next(i for i,r in enumerate(altered)if r[1]=='CI');altered[i][2]=(altered[i][2]+1)%9
    need(audit.audit(altered)[0]!=g,'Negative graph control failed')
    comparison=run(HERE/'comparison/verify_comparison.py',HERE/'comparison')
    reference=run(HERE/'logic/verify_reference.py')
    need(reference['all_passed'],'Native checker controls failed')
    with tempfile.TemporaryDirectory(prefix='pa196-essential-')as directory:
        generated_essential=run(HERE/'search/source_analysis/build_essential.py',HERE/'search/source_analysis/upstream',directory)
        need((Path(directory)/'essential.sites.json').read_bytes()==(HERE/'source_reductions/essential158.json').read_bytes(),'Essential factorization reconstruction differs')
    result={'status':'FINITE_PACKET_CHECKS_PASS','tables':tables,'sources':summary,
            'u208_comparison':comparison,'reference_checker_checks':len(reference['checks']),
            'essential_factorization_reconstructed':True,'negative_graph_control':True,
            'scope':'Finite source and comparison facts only; no sub-196 TM or PA-internal biconditional verified.'}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
