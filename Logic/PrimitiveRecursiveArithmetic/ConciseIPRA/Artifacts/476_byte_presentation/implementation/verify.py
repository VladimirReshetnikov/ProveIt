"""Reproduce the five exact source refactorings and inherited certificate tests."""
import ast
import concurrent.futures
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NAMES = ['native_tokens', 'native_ast', 'strict_size', 'native_bytes', 'strict_bytes']
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def metrics(path):
    text = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {'path': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(text).readline)),
            'ast': sum(1 for _ in ast.walk(ast.parse(text))),
            'bytes': len(text.encode()),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}

def run(task):
    name, folder, group, case, optimize = task
    path = ROOT / folder / (name + '.py')
    payload = (ROOT / 'fixtures' / group / case['file']).read_bytes()
    cmd = [sys.executable, '-I', '-S', '-B'] + (['-O'] if optimize else []) + [str(path)]
    try:
        p = subprocess.run(cmd, input=payload, capture_output=True, timeout=30)
        accept = p.returncode == 0 and p.stdout == b'ACCEPT\n'
        return {'name': name, 'folder': folder, 'group': group, 'file': case['file'],
                'optimized': optimize, 'expected': case['expected'], 'accepted': accept,
                'passed': accept == case['expected']}
    except subprocess.TimeoutExpired:
        return {'name': name, 'folder': folder, 'group': group, 'file': case['file'],
                'optimized': optimize, 'passed': False, 'timeout': True}

def main():
    audits = []
    measurements = []
    tasks = []
    for name in NAMES:
        old = (ROOT / 'controls' / (name + '.py')).read_text()
        new = (ROOT / (name + '.py')).read_text()
        if 'g += [0]' in old:
            expected = old.replace('g += [0]', "g += b'" + chr(92) + "x00'")
        else:
            expected = old.replace('k=0, v=0:', 'k=0, v=1:').replace(
                '], [k]), k) for m', '], [k]), k, 0) for m').replace(
                'c([0], q(), v=1)', 'c([0], q())')
        audits.append({'name': name, 'exact_transform': ast.dump(ast.parse(expected)) == ast.dump(ast.parse(new))})
        measurements += [metrics(ROOT / 'controls' / (name + '.py')), metrics(ROOT / (name + '.py'))]
        groups = ['native'] if name.startswith('native') else ['strict_proofs', 'strict_boundary']
        for group in groups:
            for case in json.loads((ROOT / 'fixtures' / group / 'cases.json').read_text()):
                for folder in ['controls', '.']:
                    for optimize in [False, True]:
                        tasks.append((name, folder, group, case, optimize))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        checks = list(pool.map(run, tasks))
    failures = [c for c in checks if not c['passed']]
    report = {'python': platform.python_version(), 'metrics': measurements,
              'audits': audits, 'executions': len(checks), 'failures': failures,
              'checks': checks, 'scope': 'Finite regression evidence; exact-trace proofs are in PROOF.txt.'}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'checks'}, indent=2))
    if failures or not all(a['exact_transform'] for a in audits):
        raise SystemExit(1)

if __name__ == '__main__':
    main()
