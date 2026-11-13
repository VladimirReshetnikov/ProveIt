"""Measure the entire frozen artifact Python corpus without executing it."""
from pathlib import Path
import ast, hashlib, io, json, sys, tokenize, zipfile

ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}

def measure(source):
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
            node.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    return {'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized.encode())}

def main():
    inventory = json.loads((ROOT / 'reference/artifacts-tree.json').read_text())
    if inventory.get('truncated'):
        raise RuntimeError('Truncated source inventory')
    by_sha = {}
    for row in inventory['tree']:
        if row['path'].endswith('.py'):
            by_sha.setdefault(row['sha'], []).append(row['path'])
    records = []
    for sha, paths in sorted(by_sha.items()):
        data = (ROOT / 'reference/artifact_python' / (sha + '.py')).read_bytes()
        digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if digest != sha:
            raise RuntimeError('Wrong Git blob: ' + sha)
        source = data.decode()
        records.append({'git_blob_sha1': sha, 'paths': paths,
                        'sha256': hashlib.sha256(data).hexdigest(),
                        **measure(source), 'literal_ACCEPT': 'ACCEPT' in source,
                        'needs_manual_classification': True})
    report = {'commit': '167c76930834c17648fcc2509ab16260da4c727d',
              'python': sys.version.split()[0],
              'source_instances': sum(map(len, by_sha.values())),
              'unique_sources': len(records),
              'metric': 'Strip docstrings, ast.unparse plus one LF; significant tokenize tokens, all AST nodes, UTF-8 bytes.',
              'qualification': 'A size census is not a theorem that each source is a sound standalone checker. Helpers, tests, partial kernels, and packed execution wrappers are not ordinary complete acceptance modules.',
              'records': records}
    (ROOT / 'evidence/artifact_source_census.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Verified and measured', len(records), 'unique Git blobs representing', report['source_instances'], 'Python files.')
    incoming = []
    receipts = json.loads((ROOT / 'evidence/incoming_receipts.json').read_text())
    for receipt in receipts:
        archive = ROOT / 'reference/incoming_archives' / Path(receipt['path']).name
        data = archive.read_bytes()
        git_hash = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if git_hash != receipt['git_blob_sha1'] or hashlib.sha256(data).hexdigest() != receipt['sha256']:
            raise RuntimeError('Wrong incoming archive: ' + archive.name)
        with zipfile.ZipFile(archive) as contents:
            for item in contents.infolist():
                if item.filename.endswith('.py'):
                    raw = contents.read(item)
                    incoming.append({'archive': archive.name, 'member': item.filename,
                                     'sha256': hashlib.sha256(raw).hexdigest(),
                                     **measure(raw.decode())})
    (ROOT / 'evidence/incoming_python_census.json').write_text(json.dumps(incoming, indent=2) + '\n')
    print('Authenticated', len(receipts), 'incoming archives and measured', len(incoming), 'Python members.')

if __name__ == '__main__':
    main()
