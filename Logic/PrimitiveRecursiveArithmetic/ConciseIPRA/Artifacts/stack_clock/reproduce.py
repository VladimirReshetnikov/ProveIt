"""Measure complete modules and run the portable verification suite."""
from pathlib import Path
import argparse
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = ast.unparse(tree) + '\n'
    skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
            tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {
        'tokens': sum(token.type not in skip for token in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': len(list(ast.walk(tree))),
        'normalized_bytes': len(normalized.encode('utf-8')),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metrics-only', action='store_true')
    args = parser.parse_args()
    paths = ['code/checker.py', 'reference/retained_control.py',
             'reference/exact_token_control.py', 'reference/exact_node_control.py',
             'reference/compact_control460.py', 'reference/seeded_sequent_control455.py']
    results = {name: measure(ROOT / name) for name in paths}
    claims = json.loads((ROOT / 'CLAIMS.json').read_text())
    if results['code/checker.py']['source_sha256'] != claims['metrics']['source_sha256']:
        raise SystemExit('Checker source differs from the reviewed version.')
    if results['reference/retained_control.py']['source_sha256'] != claims['control_metrics']['source_sha256']:
        raise SystemExit('Control source differs from the frozen upstream version.')
    report = {'python': sys.version, 'complete_modules': results}
    (ROOT / 'evidence' / 'reproduced_metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    if not args.metrics_only:
        subprocess.run([sys.executable, str(ROOT / 'verify.py')], cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
