"""Census every Python source in a local frozen ConciseIPRA checkout.

Usage: python3 audit_baseline.py /path/to/ProveIt --output census.json
This script parses sources but never imports or executes them. Eligibility as
a complete sound proof checker remains a separate mathematical judgment.
"""
from pathlib import Path
import argparse
import ast
import gzip
import hashlib
import io
import json
import platform
import subprocess
import tokenize
import zipfile

SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('checkout', type=Path)
    parser.add_argument('--output', type=Path, default=Path('census.json'))
    args = parser.parse_args()
    base = args.checkout.resolve()
    root = base / 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA'
    if (base / 'Artifacts').is_dir():
        root = base
    if not (root / 'Artifacts').is_dir():
        raise SystemExit('ConciseIPRA/Artifacts was not found at the supplied checkout.')
    commit = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'],
                                     text=True).strip()

    def sources():
        for path in sorted((root / 'Artifacts').rglob('*')):
            if path.is_file() and path.name.endswith(('.py', '.py.gz')):
                raw = path.read_bytes()
                yield path.relative_to(root).as_posix(), (
                    gzip.decompress(raw) if path.name.endswith('.gz') else raw)
        for path in sorted((root / 'docs/incoming').glob('*.zip')):
            with zipfile.ZipFile(path) as archive:
                for name in archive.namelist():
                    if name.endswith(('.py', '.py.gz')):
                        raw = archive.read(name)
                        yield path.relative_to(root).as_posix() + '!' + name, (
                            gzip.decompress(raw) if name.endswith('.gz') else raw)

    records, errors, count = {}, [], 0
    for name, raw in sources():
        count += 1
        digest = hashlib.sha256(raw).hexdigest()
        if digest in records:
            records[digest]['paths'].append(name)
            continue
        try:
            tree = ast.parse(raw)
            normalized = ast.unparse(tree) + '\n'
            data = normalized.encode()
            records[digest] = {
                'paths': [name], 'sha256': digest,
                'normalized_sha256': hashlib.sha256(data).hexdigest(),
                'raw_bytes': len(raw), 'normalized_bytes': len(data),
                'tokens': sum(t.type not in SKIP for t in
                              tokenize.generate_tokens(io.StringIO(normalized).readline)),
                'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
                'gzip9_raw_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
                'gzip9_normalized_bytes': len(gzip.compress(data, compresslevel=9, mtime=0)),
                'accept_literal': any(isinstance(n, ast.Constant) and n.value == 'ACCEPT'
                                      for n in ast.walk(tree)),
                'packed': any(isinstance(n, ast.Name) and n.id in ('exec', 'eval')
                              for n in ast.walk(tree)),
                'imports': [ast.unparse(n) for n in ast.walk(tree)
                            if isinstance(n, (ast.Import, ast.ImportFrom))],
            }
        except Exception as error:
            errors.append({'path': name, 'error': repr(error)})
    result = {
        'python': platform.python_version(), 'snapshot': commit,
        'source_paths': count, 'distinct_raw_sources': len(records),
        'distinct_normalized_sources': len({r['normalized_sha256']
                                           for r in records.values()}),
        'normalization': 'Whole module, ast.unparse plus LF, no docstring removal',
        'records': list(records.values()), 'errors': errors,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('records', 'errors')},
                     indent=2))
    print('Parse errors:', len(errors))


if __name__ == '__main__':
    main()
