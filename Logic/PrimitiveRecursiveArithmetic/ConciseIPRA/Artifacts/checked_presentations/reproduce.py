"""Recompute sizes, verify packaged source identity, and run both suites."""
import argparse
import ast
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PAIRS = {
    'strict_tokens.py': 'strict/code/strict_tokens.py',
    'strict_ast.py': 'strict/code/strict_ast.py',
    'strict_bytes.py': 'strict/code/strict_bytes.py',
    'compact_stream.py': 'compact/code/checker240.py',
    'compact_whole.py': 'compact/code/checker245_whole.py',
}
EXPECTED = {
    'strict_tokens.py': (319, 370, 630),
    'strict_ast.py': (327, 358, 642),
    'strict_bytes.py': (335, 380, 605),
    'compact_stream.py': (240, 266, 592),
    'compact_whole.py': (245, 272, 591),
}
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
        tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
        tokenize.ENDMARKER}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normal = (ast.unparse(tree) + '\n').encode()
    significant = sum(t.type not in SKIP for t in tokenize.generate_tokens(
        io.StringIO(normal.decode()).readline))
    return {'file': str(path.relative_to(ROOT)), 'tokens': significant,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normal),
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normal).hexdigest()}


def check_manifest():
    failures = []
    entries = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        digest, relative = line.split('  ', 1)
        entries += 1
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            failures.append(relative)
    print(json.dumps({'manifest_entries': entries, 'failures': failures}, indent=2))
    if failures:
        raise SystemExit(1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metrics-only', action='store_true')
    parser.add_argument('--verify-manifest', action='store_true')
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    if args.verify_manifest:
        check_manifest()
        return
    measurements = []
    for name, tested_path in PAIRS.items():
        path = ROOT / 'code' / name
        if path.read_bytes() != (ROOT / tested_path).read_bytes():
            raise RuntimeError('Listed and tested source copies differ: ' + name)
        row = measure(path)
        actual = (row['tokens'], row['ast_nodes'], row['normalized_bytes'])
        if actual != EXPECTED[name]:
            raise RuntimeError(f'Unexpected source measurement for {name}: {actual}')
        measurements.append(row)
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence / 'metrics.json').write_text(json.dumps(
        {'python': sys.version, 'metrics': measurements}, indent=2) + '\n')
    print(json.dumps({'metrics': measurements}, indent=2))
    if not args.metrics_only:
        for component in ('strict', 'compact'):
            subprocess.run([sys.executable, str(ROOT / component / 'verify.py')],
                           cwd=ROOT / component, check=True)
        summary = {'strict': json.loads((ROOT / 'strict/evidence/verification.json').read_text()),
                   'compact': json.loads((ROOT / 'compact/evidence/verification.json').read_text())}
        (evidence / 'reproduction.json').write_text(json.dumps(summary, indent=2) + '\n')
    if args.pdf:
        for _ in range(2):
            subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                            '-jobname=ipra_checked_presentations', 'report.tex'],
                           cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
