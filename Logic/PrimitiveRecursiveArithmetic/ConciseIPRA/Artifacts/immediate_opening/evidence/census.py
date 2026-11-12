"""Reproduce the source-size census without executing audited programs.

Usage:
    python3 evidence/census.py --repo /path/to/ProveIt

The supplied path may also be its ConciseIPRA subdirectory. The census reads
Artifacts/**/*.py and every Python member in docs/incoming/*.zip directly;
it does not extract ZIPs or import any audited module. Use the pinned commit
in provenance.json for the frozen comparison. This portable rerun uses path
labels beginning with repository/ and archives/; the original census.json
retains the working-path labels from its original execution. Raw SHA-256
identities and normalized metrics are the comparison keys.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import io
import json
import platform
import tokenize
import zipfile

SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def sources(root):
    for path in sorted((root / 'Artifacts').rglob('*.py')):
        yield 'repository/' + path.relative_to(root).as_posix(), path.read_bytes()
    for path in sorted((root / 'docs/incoming').glob('*.zip')):
        with zipfile.ZipFile(path) as archive:
            for name in sorted(archive.namelist()):
                if name.endswith('.py') and not name.endswith('/'):
                    yield 'archives/' + path.name + '!' + name, archive.read(name)


def metric(raw, label):
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and type(node.body[0].value.value) is str):
                node.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    compile(normalized, label, 'exec')
    tree = ast.parse(normalized)
    return {
        'tokens': sum(t.type not in SKIP for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast': sum(1 for _ in ast.walk(tree)),
        'bytes': len(normalized.encode('utf-8')),
        'imports': [ast.unparse(n) for n in ast.walk(tree)
                    if isinstance(n, (ast.Import, ast.ImportFrom))],
        'accept_literal': any(
            isinstance(n, ast.Constant) and n.value == 'ACCEPT'
            for n in ast.walk(tree)
        ),
        'packed': any(
            isinstance(n, ast.Name) and n.id in ('exec', 'eval')
            for n in ast.walk(tree)
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('census_rerun.json'))
    args = parser.parse_args()
    root = args.repo.resolve()
    subdirectory = root / 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA'
    if subdirectory.is_dir():
        root = subdirectory
    if not (root / 'Artifacts').is_dir() or not (root / 'docs/incoming').is_dir():
        parser.error('--repo must identify ProveIt or its ConciseIPRA directory')
    records = {}
    errors = []
    seen = set()
    count = 0
    for label, raw in sources(root):
        count += 1
        sha = hashlib.sha256(raw).hexdigest()
        seen.add(sha)
        if sha in records:
            records[sha]['paths'].append(label)
            continue
        try:
            records[sha] = {
                'paths': [label], 'sha256': sha, **metric(raw, label),
            }
        except Exception as exc:
            errors.append({'path': label, 'sha256': sha, 'error': str(exc)})
    result = {
        'python': platform.python_version(),
        'source_paths': count,
        'distinct_raw_sources': len(seen),
        'normalized_sources': len(records),
        'records': list(records.values()),
        'errors': errors,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({
        'source_paths': count,
        'distinct_raw_sources': len(seen),
        'normalized_sources': len(records),
        'excluded_paths': len(errors),
        'output': str(args.output),
    }, indent=2))


if __name__ == '__main__':
    main()
