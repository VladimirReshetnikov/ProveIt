#!/usr/bin/env python3
"""Reproduce local symbolic checks and whole-source measurements, offline."""
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def main():
    if not __debug__:
        raise RuntimeError("Run the evidence harness without Python -O")
    commands = [ROOT / 'code/verify_reset.py',
                ROOT / 'code/matched_reset/validate.py']
    for path in commands:
        run = subprocess.run([sys.executable, str(path)], cwd=ROOT,
                             text=True, capture_output=True, timeout=60)
        if run.returncode:
            raise RuntimeError(path.name + '\n' + run.stdout + run.stderr)
        print(path.name + ': PASS')
    spec = importlib.util.spec_from_file_location('measure', ROOT/'code/audit_frontier.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    audit = json.loads((ROOT/'evidence/frontier_audit.json').read_text())
    known = {p['sha256']: p for p in audit['leading_complete_sources']}
    measured = []
    for path in sorted((ROOT/'reference').glob('*.py')):
        row = module.measure(path)
        original = known.get(row['sha256'])
        if original is None:
            raise RuntimeError('Unrecognized comparator: ' + path.name)
        for key in ('normalized_tokens', 'ast_nodes', 'normalized_bytes'):
            if row[key] != original[key]:
                raise RuntimeError('Metric drift for ' + path.name + ': ' + key)
        measured.append({'file': path.name, **row})
    symbolic = json.loads((ROOT/'certificates/reset_certificate.json').read_text())
    matched = json.loads((ROOT/'code/matched_reset/validation.json').read_text())
    result = {'status': 'PASS', 'python': platform.python_version(),
              'symbolic_equations': symbolic['equations'],
              'symbolic_equation_inductions': symbolic['equation_inductions'],
              'corrupted_equations_rejected': symbolic['corrupted_equations_rejected'],
              'matched_in_process_cases': matched['in_process_cases'],
              'matched_public_cli_runs': matched['public_cli_runs'],
              'matched_saving': matched['saving'],
              'frozen_complete_sources_remeasured': measured}
    (ROOT/'evidence/reproduction.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()
                      if k != 'frozen_complete_sources_remeasured'}, indent=2))

if __name__ == '__main__':
    main()
