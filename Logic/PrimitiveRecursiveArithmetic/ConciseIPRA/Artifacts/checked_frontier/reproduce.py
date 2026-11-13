"""Verify package identity and reproduce the supplied mathematical checker evidence."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
BASELINES = {
    'baselines/tokens248.py': (248, 277, 609),
    'baselines/ast270.py': (254, 270, 608),
    'baselines/bytes487.py': (276, 308, 487),
    'baselines/strict654.py': (334, 387, 654),
}


def main():
    manifest = ROOT / 'MANIFEST.sha256'
    if manifest.exists():
        rows = [line.split('  ', 1) for line in manifest.read_text().splitlines()]
        for expected, name in rows:
            actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            if actual != expected:
                raise SystemExit('Manifest mismatch: ' + name)
        print('Manifest verified:', len(rows), 'files')
    if platform.python_version() != '3.12.14':
        print('Reference metrics use Python 3.12.14; current version:',
              platform.python_version())
    metrics = []
    for name, expected in BASELINES.items():
        raw = (ROOT / name).read_bytes()
        text = ast.unparse(ast.parse(raw)) + '\n'
        values = (sum(t.type not in SKIP for t in
                      tokenize.generate_tokens(io.StringIO(text).readline)),
                  len(list(ast.walk(ast.parse(text)))), len(text.encode()))
        if values != expected:
            raise SystemExit('Baseline metric mismatch: ' + name + ' ' + repr(values))
        metrics.append({'file': name, 'tokens': values[0], 'ast_nodes': values[1],
                        'normalized_bytes': values[2],
                        'sha256': hashlib.sha256(raw).hexdigest()})
    (ROOT / 'evidence/baseline_metrics.json').write_text(
        json.dumps({'python': platform.python_version(), 'metrics': metrics}, indent=2) + '\n')
    for script in ['checkers/verify_refinements.py', 'evidence/check_trace_simulation.py']:
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    print('Reproduced the baseline metrics, exact transformations, 440 process checks, and 15 trace runs.')


if __name__ == '__main__':
    main()
