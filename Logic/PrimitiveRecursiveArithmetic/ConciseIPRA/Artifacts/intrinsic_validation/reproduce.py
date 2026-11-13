"""Measure the complete checker and its controls; verify packaged file hashes."""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
OMIT = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
FILES = ['code/checker.py', 'reference/proper_tokens.py',
         'reference/proper_nodes.py', 'reference/proper_bytes.py']


def measure(path):
    source = path.read_text(encoding='utf-8')
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + '\n'
    tokens = sum(t.type not in OMIT for t in
                 tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {'tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized.encode('utf-8')),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest()}


def main():
    manifest = ROOT / 'MANIFEST.sha256'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest, relative = line.split('  ', 1)
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != digest:
                raise SystemExit('Manifest mismatch: ' + relative)
    measured = {name: measure(ROOT / name) for name in FILES}
    candidate = measured['code/checker.py']
    if platform.python_version() == '3.12.14':
        assert (candidate['tokens'], candidate['ast_nodes'],
                candidate['normalized_bytes']) == (316, 360, 591)
    controls = [measured[name] for name in FILES[1:]]
    envelope = {key: min(row[key] for row in controls)
                for key in ('tokens', 'ast_nodes', 'normalized_bytes')}
    assert all(candidate[key] < envelope[key] for key in envelope)
    print(json.dumps({'python': platform.python_version(), 'measurements': measured,
                      'control_envelope': envelope,
                      'candidate_below_exact_binding_envelope': True,
                      'candidate_below_compact_envelope': False}, indent=2))
    if '--tests' in sys.argv:
        subprocess.run([sys.executable, str(ROOT / 'tests' / 'verify.py')],
                       cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
