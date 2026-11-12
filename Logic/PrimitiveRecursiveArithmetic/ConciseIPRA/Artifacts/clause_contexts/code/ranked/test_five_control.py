"""Matched five-pattern control verification against pinned source fixtures."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

from translate_recursive import formula_forward, term_forward

ROOT = Path(__file__).resolve().parent
HORN = ROOT.parent / 'horn'


def proof_forward(p):
    tag = p[0]
    if tag == 'r':
        return [tag, term_forward(p[1])]
    if tag == 'u':
        return [tag, p[1], term_forward(p[2]), proof_forward(p[3])]
    if tag == 'x':
        return [tag, proof_forward(p[1]), proof_forward(p[2])]
    if tag == 'e':
        return [tag, formula_forward(p[1]), proof_forward(p[2]), proof_forward(p[3])]
    return [tag, formula_forward(p[1]), term_forward(p[2]), proof_forward(p[3])]


def main():
    spec = importlib.util.spec_from_file_location('horn_translations', HORN / 'translate.py')
    translator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(translator)
    files = sorted((HORN / 'examples').glob('*.json'))
    for path in files:
        certificate = translator.to_control(json.loads(path.read_text()))
        target = {'goal': formula_forward(certificate['goal']),
                  'proof': proof_forward(certificate['proof'])}
        for optimized in (False, True):
            command = [sys.executable] + (['-O'] if optimized else [])
            command.append(str(ROOT / 'control_five_recursive_arity.py'))
            result = subprocess.run(command, input=json.dumps(target), text=True,
                                    capture_output=True, timeout=10)
            assert result.returncode == 0 and result.stdout == 'ACCEPT\n', (path, optimized)
    result = {'pinned_source_fixtures': len(files), 'standalone_processes': 2 * len(files),
              'optimized_python_checked': True}
    (ROOT / 'verification_five_control.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
