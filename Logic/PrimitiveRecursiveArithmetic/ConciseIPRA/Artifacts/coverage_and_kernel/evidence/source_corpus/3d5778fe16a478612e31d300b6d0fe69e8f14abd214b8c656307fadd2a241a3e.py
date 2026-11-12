"""Reproduce the delivered finite checks and whole-program measurements."""
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys
import zlib

ROOT = Path(__file__).resolve().parent


def main():
    subprocess.run([sys.executable, str(ROOT / 'code/verify.py')], check=True)
    subprocess.run([sys.executable, str(ROOT / 'check_obstruction.py')], check=True)
    spec = importlib.util.spec_from_file_location('independent_measure', ROOT / 'audit/audit_corpus.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    rows = []
    for path in [ROOT / 'code/checker.py', ROOT / 'code/readable_checker.py'] + sorted((ROOT / 'audit/reference').glob('*.py')):
        raw = path.read_bytes()
        rows.append({'path': str(path.relative_to(ROOT)), **module.measure(raw)})
    measured = rows[0]
    expected = {'normalized_tokens': 284, 'ast_nodes': 323,
                'normalized_bytes': 668, 'raw_bytes': 668,
                'gzip9_raw_bytes': 391}
    if platform.python_version() == '3.12.14' and zlib.ZLIB_RUNTIME_VERSION == '1.3.2':
        for key, value in expected.items():
            if measured[key] != value:
                raise ValueError(f'{key}: expected {value}, got {measured[key]}')
    raw = (ROOT / 'code/checker.py').read_bytes()
    if hashlib.sha256(raw).hexdigest() != 'e3a77de47e95c99d27455b88b219a7d906ab862b0267c321722a87eaf2be8d6b':
        raise ValueError('The delivered checker source has changed')
    compressed = gzip.compress(raw, compresslevel=9, mtime=0)
    if gzip.decompress(compressed) != raw:
        raise ValueError('Gzip round trip failed')
    (ROOT / 'code/checker.py.gz').write_bytes(compressed)
    examples = json.loads((ROOT / 'code/cases.json').read_text())['cases']
    names = {'I0_arbitrary_seed': 'I0_arbitrary_seed.json',
             'DI_fresh_witness_cannot_depend_on_step_parameter': 'forged_witness_reject.json',
             'contextual_induction_seed_congruence': 'contextual_induction.json'}
    for case in examples:
        if case['name'] in names:
            (ROOT / 'examples' / names[case['name']]).write_text(json.dumps(case['packet']) + '\n')
    result = {'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
              'gzip_recipe': 'gzip.compress(raw_source, compresslevel=9, mtime=0)',
              'metrics': rows, 'passed': True,
              'scope': 'Finite execution evidence and exact source metrics, not a formal soundness proof.'}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'passed': True, 'checker': measured,
                      'gzip_file': 'code/checker.py.gz'}, indent=2))


if __name__ == '__main__':
    main()
