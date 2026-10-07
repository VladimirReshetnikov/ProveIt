#!/usr/bin/env python3
"""Read-only source replay, including optimization mode and fixture verification."""
import sys
sys.dont_write_bytecode = True
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
ALL_PROGRAMS = ('coefficients.py','exact_checks.py','symbolic_checks.py','numerical_diagnostics.py')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--all',action='store_true',help='Run every program (the default)')
    group.add_argument('--exact',action='store_true',help='Standard-library checks only')
    parser.add_argument('--output',type=Path,help='Write verified replay files into a new directory')
    args = parser.parse_args()
    original_destination = args.output.absolute() if args.output else None
    if original_destination is not None and original_destination.is_symlink():
        raise RuntimeError('--output cannot be a symlink')
    destination = original_destination.resolve() if original_destination else None
    if destination is not None:
        if destination == ROOT or ROOT in destination.parents or destination in ROOT.parents:
            raise RuntimeError('--output must be outside the maintained source tree')
        if destination.exists():
            raise RuntimeError('--output must name a new directory, not an existing one')
    source_before = {p.relative_to(ROOT).as_posix(): p.read_bytes()
                     for p in ROOT.rglob('*') if p.is_file()}
    programs = ('exact_checks.py',) if args.exact else ALL_PROGRAMS
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    results = []
    generated = {}
    for script in programs:
        tree = ast.parse((ROOT/script).read_text(encoding='utf-8'))
        if any(isinstance(node,ast.Assert) for node in ast.walk(tree)):
            raise RuntimeError('An optimization-sensitive assert was found in '+script)
        outputs = []
        for options in ((),('-O',)):
            run = subprocess.run([sys.executable,*options,str(ROOT/script)],cwd=ROOT,
                                 env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            if run.returncode:
                raise RuntimeError(script+' failed'+(' under -O' if options else '')+
                                   ':\n'+run.stderr.decode('utf-8',errors='replace'))
            if run.stderr:
                raise RuntimeError(script+' unexpectedly wrote stderr:\n'+
                                   run.stderr.decode('utf-8',errors='replace'))
            json.loads(run.stdout)
            outputs.append(run.stdout)
        if outputs[0] != outputs[1]:
            raise RuntimeError('Normal/-O byte mismatch for '+script)
        fixture = Path('expected')/(Path(script).stem+'.json')
        if outputs[0] != (ROOT/fixture).read_bytes():
            raise RuntimeError('Recomputed output differs from '+str(fixture))
        generated[fixture] = outputs[0]
        results.append({'program':script,'fixture':fixture.as_posix(),
                        'bytes':len(outputs[0]),'sha256':hashlib.sha256(outputs[0]).hexdigest(),
                        'normal_equals_optimized':True,'equals_expected_fixture':True})
    source_after = {p.relative_to(ROOT).as_posix(): p.read_bytes()
                    for p in ROOT.rglob('*') if p.is_file()}
    if source_after != source_before:
        raise RuntimeError('A replay modified the maintained source tree')
    # Only create the destination after every required verification has passed.
    if destination is not None:
        (destination/'expected').mkdir(parents=True,exist_ok=False)
        for relative, content in generated.items():
            (destination/relative).write_bytes(content)
    result = {'status':'PASS','programs':results,
              'source_modified':False,
              'scope':'Finite exact/symbolic verification and separately labelled diagnostics; not asymptotic proof.'}
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
