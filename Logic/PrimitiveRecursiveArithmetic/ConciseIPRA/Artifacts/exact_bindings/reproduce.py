"""Portable verification and source-size census; no network required."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def measure(path):
    tree = ast.parse(path.read_text())
    normalized = ast.unparse(tree) + '\n'
    return dict(tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(
                             io.StringIO(normalized).readline)),
                ast_nodes=sum(1 for _ in ast.walk(tree)),
                normalized_bytes=len(normalized.encode()),
                sha256=hashlib.sha256(path.read_bytes()).hexdigest())

def main():
    expected = json.loads((ROOT / 'evidence/metrics.json').read_text())
    measured = {name: measure(ROOT / 'code' / name) for name in expected}
    if measured != expected:
        raise SystemExit('Delivered checker measurements or hashes differ')
    for name in ('proper_tokens.py', 'proper_bytes.py', 'proper_nodes.py'):
        if (ROOT / 'code' / name).read_bytes() != (
                ROOT / 'verification/actual_binding' / name).read_bytes():
            raise SystemExit('Main checker and reproduction copy differ: ' + name)
    for main_name, test_name in [('checker_bytes.py', 'exact_bytes.py'),
                                 ('checker_ast.py', 'exact_ast.py')]:
        if (ROOT / 'code' / main_name).read_bytes() != (
                ROOT / 'verification/signed_mask' / test_name).read_bytes():
            raise SystemExit('Mask checker and reproduction copy differ')
    receipts = {}
    for family in ('actual_binding', 'signed_mask'):
        folder = ROOT / 'verification' / family
        run = subprocess.run([sys.executable, 'verify.py'], cwd=folder,
                             capture_output=True, text=True)
        if run.returncode:
            raise SystemExit(family + ' failed:\n' + run.stdout + run.stderr)
        data = json.loads((folder / 'verification.json').read_text())
        receipts[family] = {k: v for k, v in data.items()
                            if k not in ('results', 'compiled', 'process_results')}
        print(family + ': PASS')
    cases = json.loads((ROOT / 'verification/token_mask/cases.json').read_text())
    jobs = [(case, mode) for case in cases for mode in (False, True)]
    def check(job):
        case, mode = job
        run = subprocess.run([sys.executable, *(['-O'] if mode else []),
                              str(ROOT / 'code/checker_tokens.py')],
                             input=json.dumps(case['certificate']),
                             capture_output=True, text=True, timeout=20)
        accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
        return {'name': case['name'], 'optimized': mode,
                'expected': case['expected'], 'accepted': accepted}
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(check, jobs))
    failures = [r for r in results if r['expected'] != r['accepted']]
    if failures:
        raise SystemExit('Token mask failures: ' + json.dumps(failures))
    receipt = {'python': sys.version, 'metrics': measured,
               'family_receipts': receipts, 'token_mask_process_runs': len(results),
               'failures': failures}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('token_mask: PASS')
    print(json.dumps({'metrics': measured, 'token_mask_process_runs': len(results),
                      'failures': failures}, indent=2))

if __name__ == '__main__':
    main()
