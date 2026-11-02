#!/usr/bin/env python3
"""Independently replay and compare the historical optimized-mode fix."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
BASE = 'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/integrality-descent-analysis/'
COMMIT = 'c7f744b053'


def need(ok, message):
    if not ok: raise ValueError(message)


def show(rev, filename):
    return subprocess.run(['git','show',f'{rev}:{BASE}{filename}'],cwd=ROOT,
                          stdout=subprocess.PIPE,check=True).stdout


def main():
    names = subprocess.run(['git','diff-tree','--no-commit-id','--name-only','-r',COMMIT],
                           cwd=ROOT,stdout=subprocess.PIPE,text=True,check=True).stdout.splitlines()
    need(sorted(names)==sorted(BASE+n for n in ('README.md','check_identities.py','guard-fix-observation.json')),
         'unexpected changed paths')
    old = show(COMMIT+'^','check_identities.py')
    new = show(COMMIT,'check_identities.py')
    need(hashlib.sha256(old).hexdigest()=='020f8b2b8314cd4860beb3a3bb456fb964c1a628d4ca6402b15b6339148c45e3', 'parent checker pin')
    need(hashlib.sha256(new).hexdigest()=='d8049c8dd14d4e05c7fc3962f74a9010510ddb3bde83400982bfef952af214cb', 'fixed checker pin')
    marker = b'from math import gcd\n\n'
    guard = b"if not __debug__:\n    raise RuntimeError('optimized Python is unsupported')\n\n"
    need(old.count(marker)==1 and new==old.replace(marker,marker+guard,1), 'only checker change is guard before class and checks')
    old_doc = show(COMMIT+'^','README.md'); new_doc = show(COMMIT,'README.md')
    addition = (b'\nThe [independent review](../../../reviews/ordinary12-integrality-descent-independent/README.md)\n'
                b'also found that the original checker could print success under optimized\n'
                b'Python with its assertions disabled. The checker now rejects optimized mode.\n'
                b'The normal and optimized process outcomes are recorded in\n'
                b'[`guard-fix-observation.json`](guard-fix-observation.json).\n')
    need(new_doc == old_doc+addition, 'only documentation change is appended guard note')
    recorded = json.loads(show(COMMIT,'guard-fix-observation.json'))
    need(recorded['normal']['exit_code']==0 and recorded['optimized']['exit_code']==1, 'original observation exits')
    env = dict(os.environ); env.pop('PYTHONOPTIMIZE',None)
    outcomes = {}
    with tempfile.TemporaryDirectory(prefix='descent-guard-review-') as tmp:
        checker = Path(tmp)/'fixed.py'; checker.write_bytes(new)
        for label,flags,extra in [('normal',[],{}),('O',['-O'],{}),('OO',['-OO'],{}),
                                  ('environment',[],{'PYTHONOPTIMIZE':'1'})]:
            p = subprocess.run([sys.executable,'-B',*flags,str(checker)],env=env|extra,
                               stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            outcomes[label] = {'exit':p.returncode,'stdout':p.stdout,
                               'stderr_last_line':p.stderr.strip().splitlines()[-1] if p.stderr.strip() else ''}
            if label == 'normal':
                need(p.returncode==0 and p.stdout==recorded['normal']['stdout'] and not p.stderr, 'normal check')
            else:
                need(p.returncode==1 and not p.stdout and
                     p.stderr.strip().endswith('RuntimeError: optimized Python is unsupported'), 'optimized guard '+label)
        # This checks that the normal execution still has functioning asserts.
        mutation = Path(tmp)/'mutation.py'; mutation.write_bytes(new+b'\nassert False, "mutation control"\n')
        p = subprocess.run([sys.executable,'-B',str(mutation)],env=env,
                           stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        need(p.returncode!=0 and p.stderr.strip().endswith('AssertionError: mutation control'), 'normal assertion control')
        outcomes['normal_false_assertion'] = {'exit':p.returncode,'stderr_last_line':p.stderr.strip().splitlines()[-1]}
    print(json.dumps({'status':'PASS','reviewed_commit':COMMIT,'changed_paths':names,
          'parent_checker_sha256':hashlib.sha256(old).hexdigest(),
          'fixed_checker_sha256':hashlib.sha256(new).hexdigest(),
          'guard_is_only_code_change':True,'guard_precedes_class_and_checks':True,
          'doc_change_is_appended_note_only':True,'runs':outcomes,
          'scope':'Finite identity checker guard only; no unbounded descent, model transport, or iPRA proof.'},indent=2))


if __name__ == '__main__': main()
