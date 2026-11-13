#!/usr/bin/env python3
"""Proposed guarded header batch worker. Never builds a project module."""
import argparse
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
research=repo/'Computability/DiophantineConsistency/research'
baseline=research/'nine-variable-external-matrix-preflight/header-result.json'
survey=research/'nine-variable-current-base-source-survey/result-final.json'
policy=research/'nine-variable-external-matrix-preflight/policy.json'
inventory=research/'compiled-header-inventory/inventory.py'
reader_source=research/'compiled-header-inventory/stream_imports.lean'
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
pins={baseline:'7c5751dfd7002b3425e71f462f8058078ee0911e5f4ecbcd1e66871a4832b9fe',
      survey:'7aa788ec612ef2d1cf40e65cf16b507099532477cd581dfe2c560d7b934d31ca',
      policy:'d4c513bcd322b6c2e67a6611d47a69cbd195191f6c7d9a4ea37a210471b57db9',
      inventory:'88ebe1423c4bb4237ba2a7ce2b3e5f8fd4df807c151a8ce976075dbdf5938987',
      reader_source:'04c6de3745c83024184666577f5ee8d2d166ed54036544bef2e079de2601da63',
      lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
def sha(p):
    import hashlib
    return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def verify_launch():
    """Workflow guard against accidental unreviewed or unsupervised invocation."""
    fd_text=os.environ.pop('HEADER_WORKER_AUTH_FD',None)
    need(fd_text is not None and fd_text.isdecimal(),'missing supervisor authorization pipe')
    fd=int(fd_text)
    try:token=os.read(fd,256).decode('ascii')
    finally:os.close(fd)
    gate=here/'review-gate.json';need(gate.is_file() and not gate.is_symlink(),'review gate missing')
    code_paths=[here/'worker.py',here/'traversal_core.py',here/'supervision.py',here/'launch.py']
    code_hashes={str(p):sha(p) for p in code_paths}
    review=json.loads(gate.read_text())
    need(review.get('decision')=='PASS_PRELAUNCH_REVIEW' and
         isinstance(review.get('reviewer'),str) and review['reviewer'].strip() and
         review.get('code_hashes')==code_hashes,'invalid or stale review gate')
    parent=os.getppid()
    need(token==str(parent)+':'+sha(gate) and os.getsid(0)==os.getpid() and
         str(here/'launch.py').encode() in Path('/proc',str(parent),'cmdline').read_bytes().split(b'\0'),
         'worker lacks reviewed supervisor session')
    return code_hashes
def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
verified_code_hashes=verify_launch()
# Verify exact pinned helper bytes before executing even its top-level code.
for pinned,expected in pins.items():need(pinned.is_file() and sha(pinned)==expected,'pinned input mismatch '+str(pinned))
inv=load_module('header_inventory',inventory)
core=load_module('traversal_core',here/'traversal_core.py')

class BoundedReader(inv.Reader):
    def __init__(self,env):
        self.errors=tempfile.TemporaryFile(mode='w+t')
        self.process=subprocess.Popen([str(lean),'-M2400','-j1','--run',str(reader_source)],env=env,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.errors,text=True,bufsize=1)

def check_inputs():
    for p,h in pins.items():need(p.is_file() and sha(p)==h,'pinned input mismatch '+str(p))
    src=json.loads(survey.read_text())
    for name,rec in src['project_sources'].items():
        p=repo/rec['source'];need(p.is_file() and sha(p)==rec['source_sha256'],'workspace source drift '+name)
    return src

def checked_parent(path,code_hashes,original,declared):
    """Follow successful receipt links to the pinned original snapshot."""
    if path is None:return None
    runs=(here/'runs').resolve();seen=set();first=None;states=[]
    for _ in range(1000):
        need(path.is_absolute() and path.name=='result.json' and not path.is_symlink() and
             not path.parent.is_symlink() and path.parent.parent.resolve()==runs,
             'parent result outside direct runs child')
        path=path.resolve(strict=True);need(path not in seen,'checkpoint parent cycle');seen.add(path)
        receipt=path.parent/'terminal.json'
        need(receipt.is_file() and not receipt.is_symlink(),'missing parent terminal receipt')
        r=json.loads(receipt.read_text());state=json.loads(path.read_text())
        need(r['status']=='PASS_CHECKPOINT' and r['result_sha256']==sha(path) and
             r['supervision']['exit']==0 and r['supervision']['reason'] is None and
             r['supervision']['drained'] and r['supervision']['drain_error'] is None,
             'parent receipt is not successful')
        need(r['code_hashes_before']==code_hashes and r['code_hashes_after']==code_hashes,
             'parent used different code')
        need(state['baseline_sha256']==pins[baseline] and state['survey_sha256']==pins[survey] and
             state['policy_sha256']==pins[policy],'parent input links mismatch')
        if first is None:first=state
        states.append(state)
        link=state['parent']
        if link is None:
            core.validate_chain(original,declared,list(reversed(states)))
            return first
        path=Path(link['result_path']);other=Path(link['terminal_path'])
        need(other==path.parent/'terminal.json' and path.is_file() and other.is_file() and
             sha(path)==link['result_sha256'] and sha(other)==link['terminal_sha256'],
             'parent chain hash mismatch')
    raise RuntimeError('parent chain exceeds 1000 stages')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--max-new',type=int,required=True);args=ap.parse_args()
    need(1<=args.max_new<=64,'batch limit must be 1..64')
    runs=here/'runs'
    need(args.output.is_absolute() and args.output.name=='candidate.json' and
         not os.path.lexists(args.output) and not runs.is_symlink() and
         not args.output.parent.is_symlink() and args.output.parent.parent.resolve()==runs.resolve(),
         'output must be a fresh candidate in a direct runs child')
    code_paths=[here/'worker.py',here/'traversal_core.py',here/'supervision.py',here/'launch.py']
    code_hashes={str(p):sha(p) for p in code_paths}
    need(code_hashes==verified_code_hashes,'reviewed worker code changed')
    initial=check_inputs();original=json.loads(baseline.read_text());config=json.loads(policy.read_text())
    declared=sorted(initial['declared_external']);need(len(declared)==128,'unexpected declared external seed count')
    previous=checked_parent(args.parent,code_hashes,original,declared)
    if previous is not None:need(previous['declared_seeds']==declared,'previous seed list changed')
    state=core.restore(original,declared,previous)
    source=original if previous is None else previous
    roots=[Path(r['path']) for r in config['roots']];roles=[r['role'] for r in config['roots']]
    need([{'path':str(p),'role':r} for p,r in zip(roots,roles)]==original['roots'],'root policy mismatch')
    need([inv.root_observation(p) for p in roots]==source['root_observations'],'root identity drift')
    throttle=inv.Throttle(16*1024**2);artifacts=dict(source['artifacts']);namespaces=dict(source['namespace_observations'])
    inv.guard_full(artifacts,throttle)
    for top,entry in namespaces.items():
        need([inv.marker(r,top,throttle) for r in roots]==entry['markers'],'namespace marker drift '+top)
    for name,rec in state['modules'].items():
        top=name.split('.')[0];need(top in namespaces,'missing namespace record '+name)
        idx=namespaces[top]['selected'];obj=roots[idx].joinpath(*name.split('.')).with_suffix('.olean')
        need(rec['root']==idx and rec['role']==roles[idx] and rec['path']==str(obj),'selected module path mismatch '+name)
        for suffix in inv.SUFFIXES:need(str(obj)[:-6]+suffix in artifacts,'missing companion guard '+name+suffix)
        need(artifacts[str(obj)] is not None,'missing selected object '+name)
    new=[];reader=None;closed=False
    env=dict(os.environ,LEAN_NUM_THREADS='1')
    for key in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
    try:
        if state['queue']:reader=BoundedReader(env)
        while state['queue'] and len(new)<args.max_new:
            name=state['queue'][0];need(inv.NAME.fullmatch(name),'invalid module name '+name)
            top=name.split('.')[0]
            if top not in namespaces:
                marks=[inv.marker(r,top,throttle) for r in roots]
                idx=next((i for i,x in enumerate(marks) if x['directory'] is not None or x['file'] is not None),None)
                need(idx is not None,'unknown namespace '+top);namespaces[top]={'selected':idx,'markers':marks}
            idx=namespaces[top]['selected'];obj=roots[idx].joinpath(*name.split('.')).with_suffix('.olean');stem=str(obj)[:-6]
            group={stem+suffix:inv.inspect(Path(stem+suffix),throttle) for suffix in inv.SUFFIXES}
            need(group[str(obj)] is not None,'selected object absent '+name)
            for path,item in group.items():
                need(path not in artifacts or artifacts[path]==item,'conflicting companion guard '+path)
                artifacts[path]=item
            paths=[Path(stem+s) if group[stem+s] is not None else None for s in inv.HEADERS]
            inv.guard_metadata(group);headers=reader.read(paths);inv.guard_metadata(group)
            if headers['.olean']['is_module']:
                need('.olean.private' in headers and '.olean.server' in headers,'missing module parts '+name)
            imports=sorted({n for part in headers.values() for n in part['imports']})
            core.append(state,name,{'root':idx,'role':roles[idx],'path':str(obj),'imports':imports,'headers':headers})
            new.append(name)
        if reader is not None:reader.close(True);closed=True
    finally:
        if reader is not None and not closed:reader.close(False)
    inv.guard_full(artifacts,throttle)
    for top,entry in namespaces.items():
        need([inv.marker(r,top,throttle) for r in roots]==entry['markers'],'namespace marker changed '+top)
    need([inv.root_observation(p) for p in roots]==source['root_observations'],'root identity changed')
    check_inputs();need({str(p):sha(p) for p in code_paths}==code_hashes,'worker code changed')
    parent=None
    if args.parent is not None:
        terminal=args.parent.parent/'terminal.json'
        parent={'result_path':str(args.parent),'result_sha256':sha(args.parent),
                'terminal_path':str(terminal),'terminal_sha256':sha(terminal)}
    result={'status':'STATIC_HEADERS_COMPLETE' if not state['queue'] else 'STATIC_HEADERS_PARTIAL',
        'baseline_sha256':pins[baseline],'survey_sha256':pins[survey],'policy_sha256':pins[policy],
        'declared_seeds':declared,'parent':parent,'modules':state['modules'],'artifacts':artifacts,
        'namespace_observations':namespaces,'root_observations':source['root_observations'],
        'processed':state['processed'],'new_processed':new,'frontier':list(state['queue']),
        'reachability':core.reachability(state['modules'],declared),
        'scope':'Point-in-time selected static headers under declared namespace policy; not actual combined import or dynamic-load proof.'}
    # Reconstruct the full queue a second time before publishing the candidate.
    core.restore(original,declared,result)
    core.validate_extension(source,result)
    with args.output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print('CANDIDATE',result['status'],'new',len(new),'visited',len(state['modules']),'frontier',len(state['queue']))

if __name__=='__main__':main()
