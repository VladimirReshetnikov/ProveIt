#!/usr/bin/env python3
"""Adversarial tests for the extension inventory, output safety and certificate checks."""
import sys
sys.dontwritebytecode = True
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('exact_degree_replay', ROOT / 'replay.py')
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


def main():
    replay.verify_extension()
    replay.verify_dependencies()
    tests = []
    def rejects(name, function):
        try:
            function()
        except Exception:
            tests.append({'test': name, 'status': 'PASS_REJECTED'})
        else:
            raise RuntimeError('Tampering accepted: ' + name)
    with tempfile.TemporaryDirectory(prefix='grill-degree-integrity-') as directory:
        temporary = Path(directory)
        copy = temporary / 'exact-degree'
        shutil.copytree(ROOT, copy)
        replay.verify_extension(copy)
        for filename in ('frozen/DEGREE_PROOF.md', 'frozen/degree_certificate.json',
                         'frozen/check_degree.py.txt', 'replay_code/check_leading.py', 'PROVENANCE.json'):
            target = copy / filename
            original = target.read_bytes()
            target.write_bytes(original + b'\n')
            rejects('byte mutation: ' + filename, lambda: replay.verify_extension(copy))
            target.write_bytes(original)
        target = copy / 'frozen/degree_certificate_optimized.json'
        original = target.read_bytes()
        target.unlink()
        rejects('missing frozen certificate', lambda: replay.verify_extension(copy))
        target.write_bytes(original)
        extra = copy / 'extra.txt'
        extra.write_text('unexpected')
        rejects('extra file', lambda: replay.verify_extension(copy))
        extra.unlink()
        extra = copy / 'empty-extra-directory'
        extra.mkdir()
        rejects('extra empty directory', lambda: replay.verify_extension(copy))
        extra.rmdir()
        link = copy / 'unexpected-link'
        link.symlink_to(copy / 'README.md')
        rejects('symlink', lambda: replay.verify_extension(copy))
        link.unlink()
        cache = copy / 'replay_code/__pycache__'
        cache.mkdir()
        (cache / 'stale.pyc').write_bytes(b'stale')
        rejects('stale interpreter cache', lambda: replay.verify_extension(copy))
        shutil.rmtree(cache)
        anchor = copy / 'INVENTORY.sha256'
        original = anchor.read_bytes()
        anchor.write_text('0'*64+'\n')
        rejects('inventory anchor mutation', lambda: replay.verify_extension(copy))
        anchor.write_bytes(original)
        replay.verify_extension(copy)
        modular = replay.read_json(ROOT / 'frozen/degree_certificate.json')
        symbolic = replay.read_json(ROOT / 'frozen/independent-review/independent_leading_result.json')
        replay.validate_certificates(modular, symbolic)
        modular['trials'][0]['output']['leading_value'] = 0
        rejects('zero leading coefficient', lambda: replay.validate_certificates(modular, symbolic))
        modular = replay.read_json(ROOT / 'frozen/degree_certificate.json')
        symbolic['complete_exact_degree'] += 1
        rejects('false symbolic degree', lambda: replay.validate_certificates(modular, symbolic))
        # Real CLI checks must fail before doing any computation or writing in-package.
        flags = [sys.executable, '-I', '-B'] + (['-O'] if sys.flags.optimize else [])
        source = ROOT.parent / 'reproducibility/frozen/arithmetic'
        for script in ('check_degree.py', 'check_leading.py'):
            target = copy / 'replay_code' / script
            proc = subprocess.run(flags + [str(target), '--source-dir', str(source), '--output', str(copy/'forbidden.json')],
                                  cwd=temporary, capture_output=True, text=True, timeout=10)
            replay.need(proc.returncode != 0 and 'Output must be outside the complete release' in proc.stderr,
                        'Checker did not reject in-release output: ' + script)
            replay.need(not (copy/'forbidden.json').exists(), 'Checker wrote forbidden output')
            tests.append({'test': 'output safety: '+script, 'status': 'PASS_REJECTED'})
    replay.verify_extension()
    replay.verify_dependencies()
    print(json.dumps({'status': 'PASS_ADVERSARIAL_INTEGRITY', 'optimized': bool(sys.flags.optimize),
                      'tests': tests, 'delivered_files_modified': False}, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
