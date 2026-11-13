#!/usr/bin/env python3
"""Pre-review-gated launcher for one bounded static-header batch."""
import argparse
import hashlib
import importlib.util
import json
import os
import re
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result
supervision=module('supervision',here/'supervision.py')
core=module('traversal_core',here/'traversal_core.py')

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def code_hashes():
    return {str(here/name):sha(here/name) for name in
            ('worker.py','traversal_core.py','supervision.py','launch.py')}
def review_gate(path,expected):
    need(path.is_file() and not path.is_symlink(),'independent review gate missing')
    data=json.loads(path.read_text())
    need(data.get('decision')=='PASS_PRELAUNCH_REVIEW' and
         isinstance(data.get('reviewer'),str) and data['reviewer'].strip() and
         data.get('code_hashes')==expected,'invalid or stale independent review gate')
    return sha(path)
def save_json(path,data):
    with path.open('x') as out:json.dump(data,out,indent=2,sort_keys=True);out.write('\n')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--name',required=True)
    ap.add_argument('--parent',type=Path);ap.add_argument('--max-new',type=int,default=16)
    ap.add_argument('--timeout',type=int,default=60);args=ap.parse_args()
    need(re.fullmatch(r'[a-z0-9][a-z0-9_-]{0,50}',args.name) is not None,'invalid run name')
    need(1<=args.max_new<=64 and 1<=args.timeout<=60,'batch or timeout exceeds bound')
    if args.parent is not None:
        need(args.parent.is_absolute() and args.parent.name=='result.json', 'invalid parent path')
    before=code_hashes();gate=here/'review-gate.json';gate_hash=review_gate(gate,before)
    runs=here/'runs';need(not runs.is_symlink(),'runs is symlink');runs.mkdir(exist_ok=True)
    run=runs/args.name;run.mkdir();candidate=run/'candidate.json';terminal=run/'terminal.json'
    sup=None
    try:
        env=dict(os.environ,LEAN_NUM_THREADS='1')
        for key in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
            env.pop(key,None)
        cmd=['ionice','-c','3','nice','-n','19',sys.executable,'-I','-S','-B',str(here/'worker.py'),
             '--output',str(candidate),'--max-new',str(args.max_new)]
        if args.parent is not None:cmd+=['--parent',str(args.parent)]
        sup=supervision.supervise(cmd,run/'worker.log',cwd=here,env=env,timeout_seconds=args.timeout)
        need(sup['exit']==0 and sup['reason'] is None and sup['drained'] and
             sup['drain_error'] is None,'worker or owned-session supervision failed')
        after=code_hashes();need(after==before and review_gate(gate,after)==gate_hash,'code or review gate changed')
        result=json.loads(candidate.read_text())
        repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
        research=repo/'Computability/DiophantineConsistency/research'
        original=json.loads((research/'nine-variable-external-matrix-preflight/header-result.json').read_text())
        declared=sorted(json.loads((research/'nine-variable-current-base-source-survey/result-final.json').read_text())['declared_external'])
        state=core.restore(original,declared,result)
        need(result['status']==('STATIC_HEADERS_COMPLETE' if not state['queue'] else 'STATIC_HEADERS_PARTIAL'),
             'candidate status inconsistent with frontier')
        need(len(result['new_processed'])<=args.max_new and
             (not result['new_processed'] or result['processed'][-len(result['new_processed']):]==result['new_processed']),
             'candidate batch inconsistent')
        published=run/'result.json';candidate.rename(published)
        save_json(terminal,{'status':'PASS_CHECKPOINT','result_sha256':sha(published),
              'review_gate_sha256':gate_hash,'code_hashes_before':before,'code_hashes_after':after,
              'supervision':sup,'max_new':args.max_new,'timeout_seconds':args.timeout})
        print('PASS_CHECKPOINT',published)
    except BaseException as exc:
        if not terminal.exists():
            save_json(terminal,{'status':'FAIL_CHECKPOINT','error':repr(exc),'supervision':sup,
                                'review_gate_sha256':gate_hash,'code_hashes_before':before})
        raise
if __name__=='__main__':main()
