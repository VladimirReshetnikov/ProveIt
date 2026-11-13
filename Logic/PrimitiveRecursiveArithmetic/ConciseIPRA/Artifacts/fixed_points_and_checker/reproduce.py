"""Reproduce the report's finite measurements and tests, offline."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}


def measure(path):
    raw = path.read_bytes()
    normal = (ast.unparse(ast.parse(raw)) + '\n').encode()
    return {
        'file': str(path.relative_to(ROOT)),
        'significant_tokens': sum(t.type not in SKIP for t in
            tokenize.generate_tokens(io.StringIO(normal.decode()).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normal))),
        'normalized_bytes': len(normal),
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normal).hexdigest(),
    }


def main():
    targets = [ROOT/'code'/n for n in
               ('checker_tokens241.py', 'control_tokens242.py', 'control_ast262.py')]
    targets += sorted((ROOT/'reference'/'checkers').glob('*.py'))
    measurements = {'python': sys.version, 'programs': [measure(p) for p in targets]}
    (ROOT/'evidence'/'measurements.json').write_text(json.dumps(measurements, indent=2)+'\n')
    for r in measurements['programs']:
        print(f"{r['file']}: {r['significant_tokens']} tokens, "
              f"{r['ast_nodes']} AST nodes, {r['normalized_bytes']} bytes", flush=True)
    subprocess.run([sys.executable, '-I', '-S', '-B', str(ROOT/'code'/'verify.py')], check=True)
    subprocess.run([sys.executable, '-I', '-S', '-B', str(ROOT/'code'/'seed_sanity.py')], check=True)
    print('All finite checks passed. Mathematical soundness rests on the written proofs.')


if __name__ == '__main__':
    main()
