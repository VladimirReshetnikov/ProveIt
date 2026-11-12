"""Reproduce the finite evidence and full-source metrics, without network access."""
from pathlib import Path
import importlib.util
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    for script in ('code/test_qe.py', 'code/test_kernels.py'):
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    spec = importlib.util.spec_from_file_location('source_measure', ROOT / 'reference/source_measure.py')
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    paths = ['reference/baseline_tokens.py', 'reference/baseline_structure.py',
             'reference/baseline_bytes.py', 'code/kernel_tokens.py',
             'code/kernel_structure.py', 'code/kernel_bytes.py',
             'code/qe_restricted.py']
    rows = [{'file': path, **measure.metrics(ROOT / path)} for path in paths]
    result = {'python': platform.python_version(), 'implementation': platform.python_implementation(),
              'programs': rows, 'all_validation_commands_succeeded': True,
              'scope': 'Finite executable evidence, not a formalized universal metatheory.'}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'python': result['python'], 'all_validation_commands_succeeded': True,
                      'complete_programs_measured': len(rows)}, indent=2))


if __name__ == '__main__':
    main()
