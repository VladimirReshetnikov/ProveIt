#!/usr/bin/env python3
"""Run only the inspected independent checkers in path-preserving temporary copies."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parent
AUTHOR = 'square-product82-counterfamily-recovered-20261004'
AUDIT = 'square-product82-independent-audit-recovered-20261004'
def need(ok, message):
    if not ok:
        raise RuntimeError(message)
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(base):
    return {str(p.relative_to(base)): sha(p) for p in sorted(base.rglob('*')) if p.is_file()}
def same(a,b):
    if type(a) is not type(b):
        return False
    if isinstance(a,dict):
        return a.keys() == b.keys() and all(same(a[k],b[k]) for k in a)
    if isinstance(a,list):
        return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
    return a==b
def run():
    expected=json.loads((ROOT/'PACKET_INVENTORY.json').read_text())['sha256']
    before=inventory(ROOT/'packets')
    need(same(before,expected),'frozen release packet inventory')
    am=json.loads((ROOT/'packets'/AUTHOR/'MANIFEST.json').read_text())['sha256']
    for rel,pin in am.items():
        need(sha(ROOT/'packets'/AUTHOR/rel)==pin,'author manifest '+rel)
    for line in (ROOT/'packets'/AUDIT/'MANIFEST.sha256').read_text().splitlines():
        pin,rel=line.split(maxsplit=1)
        need(sha(ROOT/'packets'/AUDIT/rel)==pin,'audit manifest '+rel)
    outputs={}
    with tempfile.TemporaryDirectory(prefix='report45-replay-') as tmp:
        target=Path(tmp)
        for name in (AUTHOR,AUDIT):
            shutil.copytree(ROOT/'packets'/name,target/name)
        need(same(inventory(target),expected),'path-preserving temporary copies')
        for optimized in (False,True):
            mode='optimized' if optimized else 'normal'
            flags=['-O'] if optimized else []
            for name,script,args in (
                ('counterfamily',target/AUTHOR/'check_counterfamily.py',
                 ['--expect',str(target/AUTHOR/'CHECKS.json')]),
                ('independent_audit',target/AUDIT/'check_independent.py',[]),
                ('counterfamily_tamper',target/AUTHOR/'check_tamper.py',
                 ['--expect',str(target/AUTHOR/'TAMPER_CHECKS.json')])):
                proc=subprocess.run([sys.executable,*flags,str(script),*args],
                                    cwd='/',text=True,capture_output=True)
                need(proc.returncode==0,name+' '+mode+' failed: '+proc.stderr)
                parsed=json.loads(proc.stdout)
                if name=='counterfamily':
                    need(parsed['status']=='PASS','author status')
                    need(parsed['saved_schedule_executed'] is False,'saved schedule stays inert')
                elif name=='counterfamily_tamper':
                    need(parsed=={'status':'PASS','tamper_cases':3},'three intended tamper detections')
                else:
                    original=json.loads((ROOT/'packets'/AUDIT/'receipt.json').read_text())
                    need(same(parsed,original),'type-exact independent audit receipt')
                    need((target/AUDIT/'receipt.json').read_bytes()==
                         (ROOT/'packets'/AUDIT/'receipt.json').read_bytes(),
                         'byte-exact independent audit receipt')
                outputs[name+'_'+mode]={
                    'returncode':proc.returncode,
                    'stdout_sha256':hashlib.sha256(proc.stdout.encode()).hexdigest(),
                    'stderr':proc.stderr}
        need(same(inventory(target),expected),'temporary packet bytes unchanged after replay')
    need(same(inventory(ROOT/'packets'),before),'release packet bytes unchanged')
    for name in ('counterfamily','independent_audit','counterfamily_tamper'):
        need(outputs[name+'_normal']['stdout_sha256']==outputs[name+'_optimized']['stdout_sha256'],
             name+' normal and optimized outputs agree')
    return {'status':'PASS','packet_files':len(expected),'packet_bytes_unchanged':True,
            'sibling_relative_paths_preserved':True,'execution':outputs,
            'upstream_python_executed':False,'saved_source_schedules_executed':False,
            'compiler_recipes_executed':False,
            'scope':'Bounded arithmetic corroboration; the manuscript proves the unbounded theorem.'}
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=json.dumps(run(),indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(result)
    print(result,end='')
if __name__=='__main__':
    main()

