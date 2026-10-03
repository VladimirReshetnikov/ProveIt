"""Fail-closed release gate. Uses explicit exceptions and subprocess return codes.
Run under normal Python or -O. No assertions are relied upon.
"""
import argparse
import ast
import hashlib
import json
import pathlib
import subprocess
import sys
import os
import tempfile

ROOT=pathlib.Path(__file__).resolve().parent


def require(condition,message):
    if not condition: raise RuntimeError(message)


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description='Verify without changing packet inputs')
    parser.add_argument('--output-dir',help='Fresh nonexisting output directory; default is a new temporary directory')
    args=parser.parse_args()
    if args.output_dir:
        output=pathlib.Path(args.output_dir).resolve()
        output.mkdir(exist_ok=False)
    else:
        output=pathlib.Path(tempfile.mkdtemp(prefix='one-visit-observation-qa-'))
    # Frozen prior theorem/code retained byte-for-byte as self-contained context.
    context=ROOT/'boundary-context'
    old_manifest=json.loads((context/'manifest-sha256.json').read_text())
    for filename,expected in old_manifest.items():
        require(digest(context/filename)==expected,'Frozen context hash mismatch: '+filename)
    # Every executable gate and active library uses persistent checks in optimized mode.
    programs=['one_visit.py','observations.py','test_boundary_regression.py',
              'test_observations.py','independent_checks.py','verify_release.py','example.py']
    for filename in programs:
        tree=ast.parse((ROOT/filename).read_text())
        require(not any(isinstance(n,ast.Assert) for n in ast.walk(tree)),
                'Removable assert in active release file: '+filename)
    science=programs+['README.md','PROOF.md','complexity-review.md','review.md']
    before={filename:digest(ROOT/filename) for filename in science}
    checks=[]
    commands=[('author',['-m','unittest','-v','test_boundary_regression','test_observations']),
              ('independent',['independent_checks.py'])]
    for label,args in commands:
        outputs=[]
        for optimized in (False,True):
            command=[sys.executable]+(['-O'] if optimized else [])+args
            completed=subprocess.run(command,cwd=ROOT,text=True,capture_output=True,
                                     env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
            log=output/(label+('-optimized.log' if optimized else '-normal.log'))
            log.write_text(completed.stdout+completed.stderr)
            require(completed.returncode==0, 'Failed command: '+' '.join(command)+'; see '+log.name)
            require('\nOK\n' in completed.stderr, 'Missing unittest success marker: '+log.name)
            outputs.append(completed.stdout)
            checks.append({'label':label,'optimized':optimized,'exit_code':completed.returncode,
                           'log':log.name,'log_sha256':digest(log)})
        # Deterministic scientific counts/examples must match; timings in stderr may differ.
        require(outputs[0]==outputs[1],label+' scientific output differs in optimized mode')
    require(before=={filename:digest(ROOT/filename) for filename in science},
            'A scientific input changed during verification')
    for filename,expected in old_manifest.items():
        require(digest(context/filename)==expected,'Frozen context changed during verification: '+filename)
    receipt={'status':'PASS','output_directory':str(output),'frozen_context_entries':len(old_manifest),
             'no_removable_assertions_in':programs,'checks':checks,
             'source_sha256':before,'input_preservation':'byte-identical scientific inputs and frozen context'}
    (output/'release-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
