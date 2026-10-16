"""Freshly compile the supplied pinned Tarski dependency closure offline.

Example: python reproduce_lean.py --lean /path/to/lean --output verification.json
Requires Lean 4.32.0. Source files are never modified; oleans live in a fresh
temporary directory. The generated theorem terms are checked by Lean, not
accepted on the strength of the Python generator or Metamath page parsing.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
MODULES = [
    'FirstOrder/Fol', 'BusyBeaver/ZFC/Kalmar',
    'BusyBeaver/ZFC/TarskiCalculus', 'BusyBeaver/ZFC/Lukasiewicz',
    'BusyBeaver/ZFC/TarskiClassicalBridge', 'BusyBeaver/ZFC/TarskiDerived',
    'BusyBeaver/ZFC/TarskiLeibniz', 'BusyBeaver/ZFC/TarskiClean',
    'BusyBeaver/ZFC/TarskiComplete', 'BusyBeaver/ZFC/TarskiCompleteClosed',
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    version = subprocess.run([args.lean, '--version'], check=True,
                             capture_output=True, text=True).stdout.strip()
    if 'version 4.32.0,' not in version:
        raise SystemExit('Expected Lean 4.32.0; found: ' + version)
    source_root = ROOT / 'lean'
    pins = json.loads((ROOT / 'pinned-lean-inputs.json').read_text())
    for ent in pins['files']:
        suffix = ('FirstOrder/Fol.lean' if ent['path'].startswith('Logic/')
                  else 'BusyBeaver/ZFC/' + Path(ent['path']).name)
        data = (source_root / suffix).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != ent['sha']:
            raise SystemExit('Pinned dependency mismatch: ' + suffix)
    records = []
    audits = {}
    with tempfile.TemporaryDirectory(prefix='zfc-tarski-closed-') as tmp:
        build = Path(tmp)
        env = dict(os.environ)
        env['LEAN_PATH'] = str(build)
        for module in MODULES:
            source = source_root / (module + '.lean')
            output = build / (module + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            run = subprocess.run([args.lean, '-o', str(output), str(source)],
                                 cwd=source_root, env=env, capture_output=True, text=True)
            log = run.stdout + run.stderr
            if run.returncode != 0 or 'sorryAx' in log or 'declaration uses `sorry`' in log:
                raise SystemExit('Failed ' + module + '\n' + log)
            pattern = (r"'([^']+)' (does not depend on any axioms|"
                       r'depends on axioms:\s*\[([^\]]*)\])')
            for m in re.finditer(pattern, log):
                deps = [x.strip() for x in (m.group(3) or '').split(',') if x.strip()]
                if any(x not in {'propext', 'Classical.choice', 'Quot.sound'} for x in deps):
                    raise SystemExit('Unexpected axiom dependency: ' + m.group(0))
                audits[m.group(1)] = deps
            records.append({'module':module,'exit_code':run.returncode,
                            'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                            'output':log})
    required = ['SetTheory.BusyBeaver.ZFC.Tarski.classical_from_rows',
                'SetTheory.BusyBeaver.ZFC.Tarski.completeness_closed',
                'SetTheory.BusyBeaver.ZFC.Tarski.theorem_iff_semantic_consequence']
    if any(name not in audits for name in required):
        raise SystemExit('Missing expected theorem audit')
    if audits[required[0]]:
        raise SystemExit('The propositional reconstruction must be axiom-free')
    result = {'lean_version':version,'pinned_commit':pins['commit'],
              'fresh_dependency_closure':True,'modules':records,'audits':audits,
              'conclusion':'Unconditional named-variable Tarski calculus completeness; no TM endpoint.'}
    text = json.dumps(result,indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
        print('Verified',len(MODULES),'modules and',len(audits),'audited theorem roots.')
        print('Saved',args.output)
    else:
        print(text,end='')

if __name__ == '__main__':
    main()
