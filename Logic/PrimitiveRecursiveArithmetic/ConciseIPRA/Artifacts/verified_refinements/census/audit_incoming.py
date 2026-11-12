"""Statically inspect every Python member of the pinned incoming ZIP archives."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import tokenize
import urllib.request
import zipfile
from census import RemoveDocstrings, SKIP, git_blob_hash, PIN, ROOT, WORK


def main():
    metadata = ROOT / 'incoming_metadata.json'
    if not metadata.is_file():
        metadata = WORK / 'baseline/tree_docs.json'
    tree = json.loads(metadata.read_text())
    archives = [e for e in tree['tree'] if e['path'].endswith('.zip')]
    records = []
    bysha = {}
    for item in archives:
        path = ROOT / 'archives' / Path(item['path']).name
        existing = WORK / 'baseline/docs' / item['path']
        if not path.is_file() and existing.is_file():
            path = existing
        if path.is_file():
            data = path.read_bytes()
        else:
            url = ('https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'
                   + PIN + '/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/'
                   + item['path'])
            with urllib.request.urlopen(url, timeout=30) as r:
                data = r.read()
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        actual = git_blob_hash(data)
        if actual != item['sha']:
            raise ValueError((str(path), actual, item['sha']))
        record = {'path': item['path'], 'git_blob_sha': actual,
                  'git_blob_verified': True, 'bytes': len(data),
                  'sha256': hashlib.sha256(data).hexdigest(), 'python_members': 0}
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for name in z.namelist():
                if not name.endswith('.py'):
                    continue
                source = z.read(name)
                record['python_members'] += 1
                sha = hashlib.sha256(source).hexdigest()
                row = bysha.setdefault(sha, {'sha256': sha, 'data': source, 'occurrences': []})
                row['occurrences'].append({'archive': item['path'], 'member': name})
        records.append(record)
    rows = []
    for sha, row in sorted(bysha.items()):
        data = row.pop('data')
        row['raw_bytes'] = len(data)
        try:
            text = ast.unparse(RemoveDocstrings().visit(ast.parse(data))) + '\n'
            tree = ast.parse(text)
            row['significant_tokens'] = sum(t.type not in SKIP for t in
                tokenize.generate_tokens(io.StringIO(text).readline))
            row['ast_nodes'] = sum(1 for _ in ast.walk(tree))
            row['normalized_bytes'] = len(text.encode())
            row['normalized_sha256'] = hashlib.sha256(text.encode()).hexdigest()
            row['imports'] = sorted(set(
                (n.module or '') if isinstance(n, ast.ImportFrom) else a.name
                for n in ast.walk(tree) if isinstance(n, (ast.Import, ast.ImportFrom))
                for a in (n.names if isinstance(n, ast.Import) else [None])))
            marker = any(isinstance(n, ast.Constant) and n.value == 'ACCEPT'
                         for n in ast.walk(tree))
            printing = any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                           and n.func.id == 'print' for n in ast.walk(tree))
            row['possible_complete_acceptance_module'] = marker and printing and 'json' in row['imports']
        except Exception as exc:
            row['error'] = type(exc).__name__ + ': ' + str(exc)
        rows.append(row)
    candidates = [r for r in rows if r.get('possible_complete_acceptance_module')]
    result = {'pin': PIN, 'python': platform.python_version(),
              'scope': 'Every Python file inside every ZIP archive in the pinned docs subtree, without a raw-size cutoff; static analysis only, no imported/downloaded code execution.',
              'archives': records, 'python_member_paths': sum(r['python_members'] for r in records),
              'unique_python_sources': len(rows), 'errors': [r for r in rows if 'error' in r],
              'possible_complete_acceptance_modules': len(candidates),
              'candidate_coordinate_minima': {k: min(r[k] for r in candidates)
                  for k in ['significant_tokens', 'ast_nodes', 'normalized_bytes']},
              'candidates': candidates, 'rows': rows}
    (ROOT / 'incoming_census.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['python_member_paths', 'unique_python_sources',
        'possible_complete_acceptance_modules', 'candidate_coordinate_minima']}))


if __name__ == '__main__':
    main()
