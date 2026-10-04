#!/usr/bin/env python3
"""Owned portable relocation/negative-control tests; requires explicit roots."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

GUARDED_RUNNER = r'''
import json,os,pathlib,runpy,sys
denied=json.loads(sys.argv[1]); protected=json.loads(sys.argv[2]); adapter=sys.argv[3]; args=sys.argv[4:]
def inside(path,root):
    return path==root or path.startswith(root+os.sep)
def hook(event,args):
    if event.startswith('socket.'):
        raise RuntimeError('TEST_GUARD_NETWORK_DENIED')
    if event=='open' and isinstance(args[0],(str,bytes,os.PathLike)):
        path=os.path.abspath(os.fsdecode(args[0]))
        if any(inside(path,root) for root in denied):
            raise RuntimeError('TEST_GUARD_HISTORICAL_READ_DENIED: '+path)
        flags=args[2] if len(args)>2 and isinstance(args[2],int) else 0
        mode=args[1] if len(args)>1 and isinstance(args[1],str) else ''
        writing=any(c in mode for c in 'wax+') or flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)
        if writing and any(inside(path,root) for root in protected):
            raise RuntimeError('TEST_GUARD_INPUT_WRITE_DENIED: '+path)
sys.addaudithook(hook)
sys.argv=[adapter]+args
runpy.run_path(adapter,run_name='__main__')
'''

def check(ok, message):
    if not ok:
        raise RuntimeError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot(root):
    result={}
    for path in [root]+sorted(root.rglob('*')):
        st=path.lstat(); rel='.' if path==root else path.relative_to(root).as_posix()
        result[rel]={'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns,
                     'kind':'dir' if path.is_dir() else 'file'}
        if path.is_file():result[rel].update(bytes=st.st_size,sha256=digest(path))
    return result

def permissions(root, readonly):
    for path in root.rglob('*'):
        path.chmod(0o555 if path.is_dir() and readonly else 0o755 if path.is_dir() else 0o444 if readonly else 0o644)
    root.chmod(0o555 if readonly else 0o755)

def safe_path(value):
    check(bool(value), 'empty explicit test path')
    check('..' not in Path(value).parts, 'parent traversal in test path')
    path=Path(os.path.abspath(value)); current=Path(path.anchor)
    for part in path.parts[1:]:
        current=current/part
        check(not current.is_symlink(), 'symlink component in test path: '+str(current))
    return path

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for flag in ('packet','audit','dependencies','adapter','work-dir'):
        ap.add_argument('--'+flag,required=True)
    args=ap.parse_args()
    inputs={k:safe_path(getattr(args,k)) for k in ('packet','audit','dependencies')}
    adapter=safe_path(args.adapter); work=safe_path(args.work_dir)
    check(all(p.is_dir() for p in inputs.values()), 'test input directory absent')
    check(adapter.is_file(), 'adapter file absent')
    check(not work.exists(),'work directory must be absent')
    check(work.parent.is_dir(),'work directory parent must exist')
    # Before any mkdir/copy, prevent a misplaced test directory from mutating
    # an original input or recursively copying itself.
    roots=[*inputs.values(),work]
    for i,left in enumerate(roots):
        for right in roots[i+1:]:
            check(left!=right and left not in right.parents and right not in left.parents,
                  'test roots overlap: '+str(left)+' and '+str(right))
    work.mkdir(); (work/'unrelated-cwd').mkdir(); (work/'tools').mkdir()
    moved_adapter=work/'tools/replay_family59.py'; shutil.copy2(adapter,moved_adapter)
    original={k:snapshot(p) for k,p in inputs.items()}
    historical=[str(p) for p in inputs.values()]
    pins=json.loads((inputs['packet']/'SOURCE_PINS.json').read_text())['read_only_dependencies']
    historical.extend(pin['path'] for pin in pins)
    # Also deny the literal historical roots embedded in the preserved artifacts,
    # even when the test's supplied inputs were themselves already relocated.
    historical.extend(['/workspace/shared/five-signal-rotation-family59-20261004',
                       '/workspace/shared/five-signal-rotation-family59-independent-audit-20261004'])

    def clone(name,readonly=False):
        base=work/name; base.mkdir()
        roots={}
        for key,src in inputs.items():
            roots[key]=base/key;shutil.copytree(src,roots[key],copy_function=shutil.copy2)
            permissions(roots[key],readonly)
        return roots,base/'out'

    def run(roots,out,override=None,optimize=False,omit=None):
        argv=[]
        mapped={**roots,'output':out}
        if override:mapped.update(override)
        for key,value in mapped.items():
            if key!=omit:argv+=['--'+key,str(value)]
        command=[sys.executable,'-B']+(['-O'] if optimize else [])+['-c',GUARDED_RUNNER,json.dumps(historical),json.dumps([str(p) for p in roots.values()]),str(moved_adapter),*argv]
        return subprocess.run(command,cwd=work/'unrelated-cwd',text=True,capture_output=True,timeout=90)

    results=[];positive_hashes=[]
    for index,optimize in [(1,False),(2,False),(3,True)]:
        roots,out=clone('relocated-readonly-'+str(index),readonly=True)
        before={k:snapshot(p) for k,p in roots.items()}
        result=run(roots,out,optimize=optimize)
        check(result.returncode==0,'positive replay failed: '+result.stderr)
        parsed=json.loads(result.stdout)
        check(parsed['status']=='PASS','positive status absent')
        hashes={p.name:digest(p) for p in sorted(out.iterdir())}
        check(len(hashes)==5,'positive output count mismatch')
        for key,p in roots.items():check(snapshot(p)==before[key],'read-only input changed: '+key)
        positive_hashes.append(hashes)
        results.append({'test':'relocated-readonly-'+str(index),'status':'PASS','python_optimized':optimize,
                        'historical_reads_denied_by_hook':True,'network_denied_by_hook':True,'input_writes_denied_by_hook':True,
                        'all_input_files_mode':'0444','all_input_directories_mode':'0555','outputs':hashes})
    check(positive_hashes[0]==positive_hashes[1]==positive_hashes[2],'replays differ byte-for-byte')

    def negative(name,mutate=None,override=None,omit=None,reason=None):
        roots,out=clone('negative-'+name)
        if mutate:mutate(roots,out)
        changes=override(roots,out) if override else None
        effective_value=changes.get('output',out) if changes else out
        targets={out}
        if str(effective_value):
            effective=Path(effective_value)
            targets.update((effective,Path(os.path.abspath(effective))))
        def state(path):
            if not path.exists() and not path.is_symlink():return None
            if path.is_dir():return snapshot(path)
            return {'is_link':path.is_symlink(),'bytes':path.read_bytes()}
        before_targets={p:state(p) for p in targets}
        result=run(roots,out,changes,omit=omit)
        check(result.returncode!=0,'negative control accepted: '+name)
        if reason:check(reason in result.stderr,'unexpected rejection for '+name+': '+result.stderr)
        for p,before in before_targets.items():
            check(state(p)==before,'negative control changed effective/normalized output: '+name)
        results.append({'test':name,'status':'rejected','stderr':result.stderr.strip()})

    for key in ('packet','audit','dependencies','output'):
        negative('missing-flag-'+key,omit=key,reason='required')
        negative('empty-path-'+key,override=lambda r,o,key=key:{key:''},reason='empty explicit path')
    negative('missing-packet-root',override=lambda r,o:{'packet':o.parent/'absent'},reason='absent')
    negative('missing-audit-root',override=lambda r,o:{'audit':o.parent/'absent'},reason='absent')
    negative('missing-dependency-root',override=lambda r,o:{'dependencies':o.parent/'absent'},reason='absent')
    negative('overlapping-input-roots',override=lambda r,o:{'audit':r['packet']},reason='overlap')
    negative('output-inside-packet',override=lambda r,o:{'output':r['packet']/'new-output'},reason='overlap')
    negative('output-inside-audit',override=lambda r,o:{'output':r['audit']/'new-output'},reason='overlap')
    negative('existing-output',mutate=lambda r,o:(o.parent/'existing').mkdir(),override=lambda r,o:{'output':o.parent/'existing'},reason='absent')
    negative('missing-packet-manifest',mutate=lambda r,o:(r['packet']/'PACKET_MANIFEST.json').unlink())
    negative('mutated-packet-manifest',mutate=lambda r,o:(r['packet']/'PACKET_MANIFEST.json').write_text('{}\n'),reason='trust-anchor')
    negative('mutated-proof',mutate=lambda r,o:(r['packet']/'PROOF.md').write_text('altered\n'),reason='authentication')
    negative('missing-fixture',mutate=lambda r,o:next((r['packet']/'evidence').glob('a*_scale*.json')).unlink(),reason='inventory')
    negative('extra-packet-file',mutate=lambda r,o:(r['packet']/'.unexpected').write_text('x'),reason='inventory')
    negative('extra-packet-directory',mutate=lambda r,o:(r['packet']/'unexpected-empty').mkdir(),reason='inventory')
    negative('modified-audit-receipt',mutate=lambda r,o:(r['audit']/'AUDIT_RECEIPT.json').write_text('{}\n'),reason='trust-anchor')
    negative('modified-owned-checker',mutate=lambda r,o:(r['audit']/'audit_static.py').write_text('raise RuntimeError("must never execute")\n'),reason='authentication')
    negative('modified-geometry-checker',mutate=lambda r,o:(r['audit']/'audit_geometry.py').write_text('raise RuntimeError("must never execute")\n'),reason='authentication')
    negative('modified-expected-output',mutate=lambda r,o:(r['audit']/'STATIC_INDEPENDENT_RECEIPT.json').write_text('{}\n'),reason='authentication')
    negative('extra-audit-file',mutate=lambda r,o:(r['audit']/'unexpected').write_text('x'),reason='inventory')
    negative('missing-dependency',mutate=lambda r,o:next(r['dependencies'].iterdir()).unlink(),reason='inventory')
    negative('modified-dependency',mutate=lambda r,o:next(r['dependencies'].iterdir()).write_text('changed\n'),reason='authentication')
    negative('extra-dependency-file',mutate=lambda r,o:(r['dependencies']/'unexpected').write_text('x'),reason='inventory')

    def root_link(r,o):
        (o.parent/'packet-link').symlink_to(r['packet'],target_is_directory=True)
    negative('symlink-input-root',mutate=root_link,override=lambda r,o:{'packet':o.parent/'packet-link'},reason='symlink')
    def proof_link(r,o):
        p=r['packet']/'PROOF.md';p.unlink();p.symlink_to(inputs['packet']/'PROOF.md')
    negative('symlink-science-file',mutate=proof_link,reason='symlink')
    def audit_link(r,o):
        p=r['audit']/'audit_static.py';p.unlink();p.symlink_to(inputs['audit']/'audit_static.py')
    negative('symlink-audit-file',mutate=audit_link,reason='symlink')
    def dep_link(r,o):
        p=next(r['dependencies'].iterdir());name=p.name;p.unlink();p.symlink_to(inputs['dependencies']/name)
    negative('symlink-dependency-file',mutate=dep_link,reason='symlink')
    def output_link(r,o):
        (o.parent/'output-link').symlink_to(o.parent,target_is_directory=True)
    negative('symlink-output-parent',mutate=output_link,override=lambda r,o:{'output':o.parent/'output-link/new'},reason='symlink')
    negative('parent-traversal-input',override=lambda r,o:{'packet':r['packet']/'..'/'packet'},reason='parent traversal')
    negative('parent-traversal-output',override=lambda r,o:{'output':o.parent/'nonexistent'/'..'/'new'},reason='parent traversal')
    def dangling_traversal(r,o):
        (o.parent/'dangling').symlink_to(o.parent/'missing',target_is_directory=True)
    negative('dangling-symlink-before-parent-traversal',mutate=dangling_traversal,
             override=lambda r,o:{'packet':o.parent/'dangling'/'..'/'packet'},reason='parent traversal')
    def special(r,o):os.mkfifo(r['packet']/'unexpected-pipe')
    negative('special-file-in-input',mutate=special,reason='special file')
    # Changing a fixture and honestly updating its manifest still cannot replace
    # the embedded manifest trust anchor.
    def forged_manifest(r,o):
        p=r['packet']/'PROOF.md';p.write_text('forged\n')
        m=r['packet']/'PACKET_MANIFEST.json';data=json.loads(m.read_text())
        for row in data['files']:
            if row['path']=='PROOF.md':row.update(bytes=p.stat().st_size,sha256=digest(p))
        m.write_text(json.dumps(data,indent=2)+'\n')
    negative('self-consistent-forged-manifest',mutate=forged_manifest,reason='trust-anchor')
    harness_results=[]
    for key in ('packet','audit','dependencies'):
        roots,out=clone('harness-work-overlap-'+key)
        misplaced=roots[key]/'forbidden-test-work'
        before={name:snapshot(p) for name,p in roots.items()}
        command=[sys.executable,'-B',str(Path(__file__).resolve()),'--adapter',str(moved_adapter),'--work-dir',str(misplaced)]
        for name,path in roots.items():command+=['--'+name,str(path)]
        result=subprocess.run(command,cwd=work/'unrelated-cwd',capture_output=True,text=True,timeout=15)
        check(result.returncode!=0 and 'overlap' in result.stderr,'harness overlap was not rejected')
        check(not misplaced.exists(),'harness overlap created work directory')
        for name,path in roots.items():check(snapshot(path)==before[name],'harness overlap changed input')
        harness_results.append({'test':'work-dir-inside-'+key,'status':'rejected before any write'})
    for key,p in inputs.items():check(snapshot(p)==original[key],'original input changed: '+key)
    import sympy
    receipt={'status':'PASS','python':sys.version.split()[0],'sympy':sympy.__version__,'effective_uid':os.geteuid(),
             'adapter_sha256':digest(adapter),'test_tool_sha256':digest(Path(__file__)),
             'positive_replays':3,'negative_controls':len(results)-3,'byte_identical_replays':True,
             'harness_preflight_controls':harness_results,
             'original_inputs_preserved':True,'original_paths_not_used_for_replay':True,
             'guard_scope':'Python audit hook blocks historical open events, input open-for-write events, and socket events; this is a test guard, not an OS security sandbox',
             'results':results}
    (work/'PORTABLE_TEST_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))

if __name__=='__main__':main()
