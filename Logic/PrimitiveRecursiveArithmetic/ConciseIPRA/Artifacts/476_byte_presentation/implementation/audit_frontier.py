"""Static source census of the pinned ConciseIPRA subtree and its incoming ZIPs.

Usage: python3 audit_frontier.py /path/to/ProveIt [output.json]
No candidate source is imported or executed. This is a source signature screen,
not a mathematical soundness classifier; known unsound examples remain marked.
"""
import ast
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
import zipfile
from pathlib import Path

PIN = '2fa4637b3bf922beea0052a5210c22b14482950b'
SUBTREE = Path('Logic/PrimitiveRecursiveArithmetic/ConciseIPRA')
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}

def measure(name, raw):
    tree = ast.parse(raw)
    reads = any(isinstance(n, ast.Call) and (
        isinstance(n.func, ast.Name) and n.func.id in ('load', 'loads', 'input') or
        isinstance(n.func, ast.Attribute) and n.func.attr in ('load', 'loads'))
        for n in ast.walk(tree))
    prints = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and
        n.func.id == 'print' and any(isinstance(x, ast.Constant) and x.value == 'ACCEPT'
        for x in n.args) for n in ast.walk(tree))
    if not (reads and prints):
        return None
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
                node.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    normalized_tree = ast.parse(normalized)
    return {'source': name, 'tokens': sum(t.type not in SKIP for t in
        tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast': sum(1 for _ in ast.walk(normalized_tree)), 'bytes': len(normalized.encode()),
        'raw_sha256': hashlib.sha256(raw).hexdigest(),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
        'known_experiment': '/experiments/' in name or '/counterexample/' in name or 'unsound' in name}

def main():
    repo = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(__file__).with_name('frontier_census.json')
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if head != PIN:
        raise ValueError('This audit requires the pinned commit ' + PIN)
    streams = []
    archives = []
    for path in sorted((repo / SUBTREE / 'Artifacts').rglob('*.py')):
        streams.append((path.relative_to(repo).as_posix(), path.read_bytes()))
    for path in sorted((repo / SUBTREE / 'docs/incoming').glob('*.zip')):
        raw = path.read_bytes()
        archives.append({'path': path.relative_to(repo).as_posix(), 'bytes': len(raw),
                         'sha256': hashlib.sha256(raw).hexdigest(),
                         'git_blob_sha1': hashlib.sha1(('blob ' + str(len(raw)) + '\0').encode() + raw).hexdigest()})
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            for member in sorted(archive.namelist()):
                if member.endswith('.py'):
                    streams.append((path.relative_to(repo).as_posix() + '!' + member, archive.read(member)))
    rows = []
    failures = []
    for name, raw in streams:
        try:
            row = measure(name, raw)
            if row is not None:
                rows.append(row)
        except Exception as error:
            review = {'source': name, 'error': type(error).__name__ + ': ' + str(error),
                      'raw_sha256': hashlib.sha256(raw).hexdigest()}
            try:
                intact = ast.unparse(ast.parse(raw)) + '\n'
                review['metrics_retaining_docstrings'] = {
                    'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(intact).readline)),
                    'ast': sum(1 for _ in ast.walk(ast.parse(intact))),
                    'bytes': len(intact.encode())}
            except Exception:
                pass
            failures.append(review)
    candidates = [r for r in rows if not r['known_experiment']]
    envelope = {key: min(r[key] for r in candidates) for key in ('tokens', 'ast', 'bytes')}
    report = {'commit': head, 'python': platform.python_version(),
              'python_occurrences': len(streams),
              'distinct_raw_python_sources': len({hashlib.sha256(raw).hexdigest() for _,raw in streams}),
              'signature_matches': len(rows),
              'distinct_normalized_signature_matches': len({r['normalized_sha256'] for r in rows}),
              'screened_coordinate_minima': envelope,
              'minimizers': {key: [r for r in candidates if r[key] == envelope[key]] for key in envelope},
              'archives': archives, 'parse_failures': failures, 'rows': rows,
              'scope': 'Static direct-input/literal-ACCEPT signature screen, not proof of soundness or universal minimality. Packed loaders and alternative output protocols require separate accounting.'}
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('rows','minimizers')}, indent=2))

if __name__ == '__main__':
    main()
