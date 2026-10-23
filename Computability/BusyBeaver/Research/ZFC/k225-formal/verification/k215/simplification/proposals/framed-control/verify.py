#!/usr/bin/env python3
"""Verify package integrity, finite extraction, and deterministic Lean generation.

Default checks require only Python's standard library and do not compile proofs.
All generated output goes outside this package to a fresh work directory.

  python3 verify.py --work /path/to/new-directory
  python3 verify.py --lean /path/to/lean --work /path/to/new-directory
  python3 verify.py --coqc /path/to/coqc --coqchk /path/to/coqchk

The manifest establishes byte identity relative to this archive. It is not a
signature or a theorem. The optional compiler checks certify components only.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parent


def require(condition,message):
    if not condition:raise ValueError(message)


def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()


def manifest_check():
    manifest=ROOT/'MANIFEST.json'
    data=json.loads(manifest.read_text())
    require(data.get('format')=='sha256-size-v1','Unsupported manifest format')
    expected={}
    for item in data['files']:
        rel=PurePosixPath(item['path'])
        require(not rel.is_absolute()and '..'not in rel.parts and str(rel)==item['path'],
                'Unsafe or noncanonical manifest path')
        require(str(rel)!='MANIFEST.json'and str(rel)not in expected,'Duplicate/self-referential manifest item')
        expected[str(rel)]=item
    actual={}
    for path in ROOT.rglob('*'):
        require(not path.is_symlink(),'Symbolic links are not accepted in the release tree')
        if path.is_file()and path.name!='MANIFEST.json':
            actual[path.relative_to(ROOT).as_posix()]=path
        elif path.is_file()and path!=manifest:
            # Only the root manifest is excluded, not nested files of the same name.
            actual[path.relative_to(ROOT).as_posix()]=path
    require(set(actual)==set(expected),
            'Manifest membership mismatch; missing='+str(sorted(set(expected)-set(actual)))+
            '; extra='+str(sorted(set(actual)-set(expected))))
    for name,item in expected.items():
        path=actual[name]
        require(path.stat().st_size==item['bytes']and digest(path)==item['sha256'],
                'Manifest byte identity mismatch: '+name)
    return dict(files=len(expected),sha256=digest(manifest))


def executable(value):
    found=shutil.which(value)
    if found is None and Path(value).is_file():found=str(Path(value).resolve())
    require(found is not None,'Executable was not found: '+value)
    return str(Path(found).resolve())


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work',type=Path,help='Fresh directory outside the delivered package')
    ap.add_argument('--lean',help='Optionally run the complete Lean component build with this Lean 4.32.0 binary')
    ap.add_argument('--coqc',help='Optionally run the Coq compatibility checker; also supply --coqchk')
    ap.add_argument('--coqchk',help='Companion recursive Coq kernel checker')
    ap.add_argument('--coq-private-prefix',type=Path,
        help='Alternative: extracted Coq runtime prefix accepted by rocq/check_component.py')
    args=ap.parse_args()
    require(bool(args.coqc)==bool(args.coqchk),'Supply --coqc and --coqchk together')
    require(not(args.coq_private_prefix and args.coqc),'Choose explicit Coq binaries or --coq-private-prefix')
    integrity=manifest_check()
    if args.work:
        work=args.work.resolve()
        require(work!=ROOT and ROOT not in work.parents,'Work must be outside the delivered package')
        require(not work.exists(),'Work directory already exists; choose a fresh directory')
        work.mkdir(parents=True)
    else:
        work=Path(tempfile.mkdtemp(prefix='k215-framed-verify-')).resolve()
    (work/'logs').mkdir()
    result=dict(status='RUNNING',manifest=integrity,work=str(work),records=[],
                proof_compilers_requested=bool(args.lean or args.coqc or args.coq_private_prefix),
                full_physical_endpoint_rebuilt=False)
    result_path=work/'VERIFY_RESULT.json'
    def save():result_path.write_text(json.dumps(result,indent=2)+'\n')
    def run(name,command,cwd=None):
        tick=time.perf_counter()
        cp=subprocess.run(command,cwd=cwd or ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        log=work/'logs'/(name+'.log');log.write_text(cp.stdout)
        row=dict(name=name,command=command,exit_code=cp.returncode,
                 seconds=round(time.perf_counter()-tick,6),log=str(log.relative_to(work)),log_sha256=digest(log))
        result['records'].append(row);save()
        print(json.dumps(dict(check=name,exit_code=cp.returncode,seconds=row['seconds'])),flush=True)
        require(cp.returncode==0,name+' failed; see '+str(log))
    def equal_files(produced,delivered):
        require(produced.read_bytes()==delivered.read_bytes(),
                'Regeneration mismatch: '+str(delivered.relative_to(ROOT)))
    save()
    try:
        py=[sys.executable,'-I','-B']
        audit_out=work/'audit-replay'
        run('finite-audit',py+[str(ROOT/'audit/audit_frames.py'),'--repo',
            str(ROOT/'audit/snapshots'),'--out',str(audit_out)])
        compared=[]
        for name in ('templates-q1q2.json','templates-q2.json','summary.json'):
            equal_files(audit_out/name,ROOT/'audit/results'/name)
            compared.append(dict(path='audit/results/'+name,sha256=digest(audit_out/name)))
        result['finite_audit_results_identical']=compared
        emit=work/'regenerated-lean';emit.mkdir()
        source_data=ROOT/'audit/results/templates-q1q2.json'
        run('generate-templates',py+[str(ROOT/'lean/scripts/generate_templates.py'),str(source_data),
            '--output',str(emit/'FramedTemplates.lean')])
        shards=json.loads((ROOT/'lean/CALLER_SHARDS.json').read_text())
        run('generate-callers',py+[str(ROOT/'lean/scripts/generate_callers_sharded.py'),
            '--input',str(source_data),'--directory',str(emit),'--batch-size',str(shards['batch_size'])])
        produced={'FramedTemplates.lean','CALLER_SHARDS.json'}|{m+'.lean'for m in shards['modules']}
        actual={p.name for p in emit.iterdir()if p.is_file()}
        require(actual==produced,'Unexpected generated Lean file inventory')
        generation=[]
        for name in sorted(produced):
            equal_files(emit/name,ROOT/'lean'/name)
            generation.append(dict(path='lean/'+name,sha256=digest(emit/name)))
        result['generated_lean_files_identical']=generation
        if args.lean:
            run('lean-component',py+[str(ROOT/'lean/build.py'),'--lean',executable(args.lean),
                '--work',str(work/'lean-build')])
            leaf=work/'lean-build/BUILD_RESULT.json'
            build=json.loads(leaf.read_text())
            require(build['status']=='COMPONENT_KERNEL_CHECK_PASS','Lean builder did not report a completed component check')
            result['lean_component']=dict(status=build['status'],project_modules=build['project_modules'],
                result=str(leaf.relative_to(work)),sha256=digest(leaf))
        if args.coqc or args.coq_private_prefix:
            copied=work/'rocq-component'
            shutil.copytree(ROOT/'rocq',copied,
                ignore=shutil.ignore_patterns('*.vo','*.vos','*.vok','*.glob','*.aux','__pycache__'))
            command=py+[str(copied/'check_component.py')]
            if args.coq_private_prefix:
                command+=['--private-prefix',str(args.coq_private_prefix.resolve())]
            else:
                command+=['--coqc',executable(args.coqc),'--coqchk',executable(args.coqchk)]
            run('coq-component',command,copied)
            checked=copied/'evidence/CHECKED.json'
            record=json.loads(checked.read_text())
            require(record['status']=='PASS','Coq compatibility checker did not report PASS')
            result['coq_compatibility_component']=dict(status='PASS',
                result=str(checked.relative_to(work)),sha256=digest(checked),
                production_rocq_9_1_endpoint_rebuilt=False)
        # No program invoked above is permitted to write the delivered package.
        require(manifest_check()==integrity,'The delivered package changed during verification')
        result['status']='PASS';save()
        print(json.dumps(dict(status='PASS',result=str(result_path),
            manifest_files=integrity['files'],finite_result_files=3,generated_lean_files=len(generation),
            full_physical_endpoint_rebuilt=False)),flush=True)
    except BaseException as exc:
        result['status']='FAILED';result['failure']=str(exc);save()
        raise


if __name__=='__main__':
    try:main()
    except (ValueError,OSError,subprocess.SubprocessError)as error:
        print('VERIFICATION FAILED: '+str(error),file=sys.stderr)
        sys.exit(1)
