#!/usr/bin/env python3
"""Run exactly five reviewed Source154 theory leaves in a new disposable copy.
No wrapper, manifest, compiler, baseline runtime or optional audit is invoked.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

JOBS = [
    ('mp-conventions', 'check_mp_conventions.py', 'mp_conventions_receipt.json'),
    ('membership-blind', 'check_membership_blind_detachment.py', 'membership_blind_receipt.json'),
    ('shifted-even', 'check_shifted_even_codec.py', 'shifted_even_codec_receipt.json'),
    ('negative-atoms', 'check_negative_atoms_core_matrix.py', 'negative_atoms_core_matrix_receipt.json'),
    ('t-template', 'check_t_template.py', 't_template_receipt.json'),
]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def descriptor(p):
    return {'path': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}

def save(p, x):
    p.write_text(json.dumps(x, indent=2) + '\n')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',required=True,type=Path)
    parser.add_argument('--output',required=True,type=Path)
    a=parser.parse_args()
    packet=a.packet.resolve(); out=a.output.resolve()
    assert not out.exists(), 'Use a new output directory; prior attempts must be preserved'
    source=packet/'research/theory'
    assert source.is_dir()
    out.mkdir(parents=True)
    work=out/'work/research/theory'
    shutil.copytree(source,work)
    logs=out/'logs';logs.mkdir()
    outputs=out/'outputs';outputs.mkdir()
    inherited=out/'inherited-receipts';inherited.mkdir()
    # Preserve copied historical outputs and remove only the five expected outputs.
    for _,_,name in JOBS:
        p=work/name
        if p.exists():
            shutil.copyfile(p,inherited/name)
            p.unlink()
    before={name:descriptor(source/name) for _,name,_ in JOBS}
    env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
    env['PYTHONDONTWRITEBYTECODE']='1'
    report={'status':'RUNNING','packet':str(packet),'output':str(out),
            'runner':descriptor(Path(__file__).resolve()),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'wall_limit_seconds_each':60,'assertions_enabled':True,
            'selected_source_before':before,'jobs':[],
            'scope':'Five standalone finite theory checks only; no candidate runtime, proof compiler, wrapper, manifest validation or optional baseline audit.'}
    save(out/'actual.json',report)
    for key,name,result_name in JOBS:
        script=work/name
        assert sha(script)==before[name]['sha256']
        cmd=[sys.executable,'-B',str(script)]
        stdout=logs/(key+'.stdout');stderr=logs/(key+'.stderr')
        start=time.monotonic();timed_out=False
        with stdout.open('wb') as so,stderr.open('wb') as se:
            process=subprocess.Popen(cmd,cwd=work,env=env,stdout=so,stderr=se,start_new_session=True)
            try:
                code=process.wait(timeout=60)
            except subprocess.TimeoutExpired:
                timed_out=True;os.killpg(process.pid,signal.SIGKILL);code=process.wait()
        elapsed=time.monotonic()-start
        produced=work/result_name
        output_record=None
        if produced.exists():
            shutil.copyfile(produced,outputs/result_name)
            output_record=descriptor(outputs/result_name)
        item={'name':key,'argv':cmd,'cwd':str(work),'exit_code':code,'timed_out':timed_out,
              'elapsed_seconds':elapsed,'stdout':descriptor(stdout),'stderr':descriptor(stderr),
              'source':descriptor(script),'fresh_output':output_record}
        report['jobs'].append(item)
        save(out/'actual.json',report)
        print(key,code,'timeout='+str(timed_out),'seconds='+format(elapsed,'.6f'),flush=True)
    report['selected_source_after']={name:descriptor(source/name)for _,name,_ in JOBS}
    report['inputs_unchanged']=report['selected_source_after']==before
    report['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    report['status']='FIVE_SELECTED_THEORY_LEAVES_PASS' if report['inputs_unchanged'] and all(j['exit_code']==0 and not j['timed_out'] and j['fresh_output'] for j in report['jobs']) else 'FIVE_SELECTED_THEORY_LEAVES_FAIL'
    save(out/'actual.json',report)
    print(report['status'],flush=True)
    return 0 if report['status'].endswith('_PASS') else 1

if __name__=='__main__':
    raise SystemExit(main())
