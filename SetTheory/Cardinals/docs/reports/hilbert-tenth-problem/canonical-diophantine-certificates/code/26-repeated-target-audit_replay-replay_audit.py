#!/usr/bin/env python3
"""Portable, path-only replay of three byte-frozen independent auditors.

Place this file in BUNDLE/audit_replay/. Invoke Python with -I and a fresh
external --output directory. No file in BUNDLE is written, imported, or altered.
The frozen independent checker bytes are copied unchanged outside BUNDLE and
executed in isolated child interpreters. Only their two historical Path reads
are redirected to exact pinned data in BUNDLE; no checker text is rewritten.
"""
import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

ROLES={
 'source':{
  'checker':'independent_audit/audit_source.py',
  'checker_sha256':'9923a9315595bcd13bb64d2528c62ffc77d90de2acd2652e66304b10c421b20d',
  'receipt':'independent_audit/source-audit-receipt.json',
  'receipt_sha256':'3befe9724413f4f7688068c542acf20669905def36c7e5192ca144cfd2c8dce9',
  'result':'source-audit-receipt.json',
  'redirect':'source_dag'},
 'arithmetic':{
  'checker':'independent_audit/audit_arithmetic.py',
  'checker_sha256':'e566f7843a950ef4bd95ba4a87d33eb5224fa139288625662f7b1e1817d2675c',
  'receipt':'independent_audit/arithmetic-audit-receipt.json',
  'receipt_sha256':'15cc70d844d3b69f0568d5171e4916db89e1bdfe07980d537b443772ecb61589',
  'result':'arithmetic-audit-receipt.json',
  'redirect':'pell_source'},
 'semantic':{
  'checker':'independent_audit/semantic-challenge/independent_checks.py',
  'checker_sha256':'c0b837bdb83b3677a88e1cfc75189d540462cc16f27887291fe1970a3f49e60d',
  'receipt':'independent_audit/semantic-challenge/independent-check-results.json',
  'receipt_sha256':'4d7fe582a53138e1c7d42e0a1d2011bee6a58740c2e9827655072830ea1e86ff',
  'result':'independent-check-results.json',
  'redirect':None}}
DATA={
 'source_dag':{
  'historical':'/workspace/shared/sandpile-repeated-target-20261004/evidence/polynomial-dag.json',
  'target':'science/evidence/polynomial-dag.json',
  'sha256':'7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6'},
 'pell_source':{
  'historical':'/workspace/shared/sandpile-fixed-arity-independent-audit-20261004/pell-pinned-fetch.json',
  'target':'dependencies/pell-pinned-fetch.json',
  'sha256':'9c8f8911f4435fbaaa4216e1f949eca920b49594192719e6128f3c0c7b85f2c8'}}


def digest(data):return hashlib.sha256(data).hexdigest()

def require(ok,message):
    if not ok:raise RuntimeError(message)

def snapshot(root):
    """Hash every regular file and record modes/mtime for every entry, incl root."""
    result={}
    for p in [root]+sorted(root.rglob('*')):
        st=p.lstat();rel='.' if p==root else p.relative_to(root).as_posix()
        require(not stat.S_ISLNK(st.st_mode),'Symlink not permitted in frozen bundle: '+rel)
        require(stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode),'Nonregular bundle entry: '+rel)
        entry={'kind':'directory' if p.is_dir() else 'file','mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns}
        if p.is_file():entry.update(size=st.st_size,sha256=digest(p.read_bytes()))
        result[rel]=entry
    return result

def check_preserved(before,after):
    changed=sorted(k for k in set(before)|set(after) if before.get(k)!=after.get(k))
    require(not changed,'Bundle preservation guard failed: '+', '.join(changed[:20]))

def verify_inputs(root):
    required={}
    for role,spec in ROLES.items():
        required[spec['checker']]=spec['checker_sha256'];required[spec['receipt']]=spec['receipt_sha256']
    required.update({d['target']:d['sha256'] for d in DATA.values()})
    for rel,h in required.items():
        p=root/rel
        require(p.is_file() and not p.is_symlink(),'Missing frozen input: '+rel)
        require(digest(p.read_bytes())==h,'Frozen input pin mismatch: '+rel)
    return required

def external_path(root,path):
    p=path.resolve()
    require(p!=root and root not in p.parents,'Replay output must be outside the bundle')
    require(p not in root.parents,'Replay output cannot contain the bundle')
    return p


def worker(root,work,role):
    require(sys.flags.isolated==1,'Worker must run in isolated Python (-I)')
    verify_inputs(root)
    work=external_path(root,work)
    spec=ROLES[role];source=root/spec['checker'];copied=work/source.name
    require(copied.is_file(),'Missing unchanged external checker copy')
    code=copied.read_bytes()
    require(digest(code)==spec['checker_sha256'],'External checker-copy pin mismatch')
    require(code==source.read_bytes(),'External checker copy differs from frozen input')
    receipt=work/spec['result']
    require(not receipt.exists(),'Worker result must not already exist')
    originals={name:getattr(Path,name) for name in ('read_bytes','read_text','write_bytes','write_text')}
    redirects={};writes=[]
    allowed_read=copied.resolve();allowed_write=receipt.resolve()
    aliases={d['historical']:(key,root/d['target']) for key,d in DATA.items()}
    def read_target(path):
        # Deliberately no existence probe or fallback at historical locations.
        text=str(path)
        if text in aliases:
            key,target=aliases[text]
            require(spec['redirect']==key,'Unexpected data read for role '+role)
            redirects[key]=redirects.get(key,0)+1
            return target
        require(path.resolve()==allowed_read,'Unapproved checker read')
        return path
    def write_target(path):
        require(path.resolve()==allowed_write,'Unapproved checker write')
        writes.append(spec['result']);return path
    def read_bytes(path):return originals['read_bytes'](read_target(path))
    def read_text(path,*a,**kw):return originals['read_text'](read_target(path),*a,**kw)
    def write_bytes(path,data):return originals['write_bytes'](write_target(path),data)
    def write_text(path,data,*a,**kw):return originals['write_text'](write_target(path),data,*a,**kw)
    replacements={'read_bytes':read_bytes,'read_text':read_text,'write_bytes':write_bytes,'write_text':write_text}
    try:
        for name,fn in replacements.items():setattr(Path,name,fn)
        # Execute the exact frozen bytes, without source substitution or AST edits.
        ns={'__name__':'__main__','__file__':str(copied),'__package__':None,'__cached__':None}
        exec(compile(code,str(copied),'exec'),ns)
    finally:
        for name,fn in originals.items():setattr(Path,name,fn)
    expected={} if spec['redirect'] is None else {spec['redirect']:1}
    require(redirects==expected,'Expected path redirect was not exercised exactly once')
    require(bool(writes),'Frozen checker wrote no receipt')
    require(digest(copied.read_bytes())==spec['checker_sha256'],'External checker changed during execution')
    trace={'role':role,'isolated_python':True,'checker':spec['checker'],'checker_sha256':digest(code),
      'receipt':spec['result'],'read_redirects':redirects,'receipt_writes':len(writes),
      'redirect_targets':{k:DATA[k]['target'] for k in redirects},'frozen_checker_bytes_unchanged':True,
      'source_text_rewritten':False,'historical_path_fallback':False}
    (work/'worker-trace.json').write_text(json.dumps(trace,sort_keys=True,indent=2)+'\n')


def replay(root,output):
    require(root.is_dir(),'Bundle root does not exist')
    output=external_path(root,output)
    require(not output.exists(),'Replay output must be a fresh directory')
    before=snapshot(root);inputs=verify_inputs(root)
    output.mkdir(parents=True,exist_ok=False)
    roles={};failure=None
    try:
        for role,spec in ROLES.items():
            work=output/role;work.mkdir()
            copied=work/Path(spec['checker']).name
            copied.write_bytes((root/spec['checker']).read_bytes())
            child=subprocess.run([sys.executable,'-I',str(Path(__file__).resolve()),'--bundle-root',str(root),
                '--worker',role,'--output',str(work)],capture_output=True,text=True,timeout=120)
            (work/'stdout.log').write_text(child.stdout)
            (work/'stderr.log').write_text(child.stderr)
            require(child.returncode==0,'Isolated '+role+' replay failed; see external '+role+'/stderr.log')
            actual=(work/spec['result']).read_bytes();expected=(root/spec['receipt']).read_bytes()
            require(actual==expected,'Exact receipt comparison failed for '+role)
            trace=json.loads((work/'worker-trace.json').read_text())
            roles[role]={'checker':spec['checker'],'checker_sha256':spec['checker_sha256'],
                'expected_receipt':spec['receipt'],'actual_receipt':role+'/'+spec['result'],
                'receipt_sha256':digest(actual),'receipt_byte_equal':True,'worker':trace}
    except BaseException as exc:
        failure=exc
    after=snapshot(root)
    # Always check preservation, including a failed execution.
    check_preserved(before,after)
    (output/'bundle-snapshot-before.json').write_text(json.dumps(before,sort_keys=True,indent=2)+'\n')
    (output/'bundle-snapshot-after.json').write_text(json.dumps(after,sort_keys=True,indent=2)+'\n')
    if failure is not None:raise failure
    result={'verdict':'PASS','schema':'portable-frozen-independent-audit-replay-v1',
       'adapter_sha256':digest(Path(__file__).read_bytes()),'bundle_paths_are_root_relative':True,
       'source_rewriting':False,'all_frozen_inputs_preserved':True,
       'preservation_checks':['file bytes','file size','file and directory mode','file and directory mtime_ns','entry inventory'],
       'bundle_entries_checked':len(before),'pinned_inputs':inputs,'roles':roles,
       'scope':'Replays the independent source, arithmetic and semantic audits only. No submitted builder, author checker, upstream program, schedule, or Lean is executed.'}
    (output/'replay-receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True,help='Fresh directory outside the bundle')
    parser.add_argument('--bundle-root',type=Path,default=Path(__file__).resolve().parent.parent,
                        help=argparse.SUPPRESS)
    parser.add_argument('--worker',choices=sorted(ROLES),help=argparse.SUPPRESS)
    args=parser.parse_args();root=args.bundle_root.resolve()
    if args.worker:worker(root,args.output,args.worker)
    else:replay(root,args.output)

if __name__=='__main__':main()
