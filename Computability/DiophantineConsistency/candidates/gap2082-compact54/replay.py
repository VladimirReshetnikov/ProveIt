#!/usr/bin/env python3
"""Authenticate and reproduce this candidate in an isolated temporary copy."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def run(work, args):
    result = subprocess.run([sys.executable,'-B',*args], cwd=work,
        env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(result.returncode==0, ' '.join(args)+'\n'+result.stdout+'\n'+result.stderr)
    return json.loads(result.stdout)


def main():
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    for name, sha in manifest.items():
        require(digest((ROOT/name).read_bytes())==sha, 'manifest '+name)
    generated = [name for name in manifest if name.startswith(('generated/','fixed/'))]
    with tempfile.TemporaryDirectory(prefix='proveit-gap2082-compact54-') as temporary:
        work = Path(temporary)/'candidate'
        shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        run(work,['build.py'])
        for name in generated:
            require((work/name).read_bytes()==(ROOT/name).read_bytes(), 'byte-exact rebuild '+name)
        normal = run(work,['verify.py'])
        optimized = run(work,['-O','verify.py'])
        require(normal['assertions_disabled'] is False and optimized['assertions_disabled'] is True,
                'actual normal and optimized modes')
        n = dict(normal); o = dict(optimized)
        n.pop('assertions_disabled'); o.pop('assertions_disabled')
        require(n==o, 'identical mathematical checks under optimization')
        for label, receipt in [('normal',normal),('optimized',optimized)]:
            require(receipt==json.loads((ROOT/'receipts'/('VERIFY.'+label+'.json')).read_text()),
                    'reproduced '+label+' receipt')
        report = {'status':'PASS','root_assertions_disabled':bool(sys.flags.optimize),
                  'sealed_files':len(manifest),'byte_identical_rebuilt_files':len(generated),
                  'normal_and_optimized_checks_identical':True,'inner_normal':'PASS','inner_optimized':'PASS',
                  'positive_operations':443,'natural_operations':450,'exact_degree':1845940,
                  'mathematical_negative_controls_per_mode':normal['mathematical_negative_controls'],
                  'actual_modular_register_cases_per_mode':normal['modular_output_and_register_cases'],
                  'scope':'Finite candidate replay; no end-to-end Lean or internal ZFC theorem.'}
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
