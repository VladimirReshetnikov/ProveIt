"""Offline, non-executing inventory of frozen source archives and Python code."""
import ast
import hashlib
import io
import json
from pathlib import Path
import tokenize
import zipfile

ROOT = Path(__file__).resolve().parent
SEEN = set()
ROWS = []


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def scan(data, name):
    digest = hashlib.sha256(data).hexdigest()
    if digest in SEEN:
        return
    SEEN.add(digest)
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        for member in archive.namelist():
            if member.endswith('/'):
                continue
            payload = archive.read(member)
            label = name + '!' + member
            if member.endswith('.zip'):
                scan(payload, label)
            elif member.endswith('.py'):
                row = {'path': label, 'source_sha256': hashlib.sha256(payload).hexdigest()}
                try:
                    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(payload)))
                    normalized = ast.unparse(tree) + '\n'
                    row.update(normalized_tokens=sum(t.type not in ignored for t in
                               tokenize.generate_tokens(io.StringIO(normalized).readline)),
                               ast_nodes=sum(1 for _ in ast.walk(tree)),
                               normalized_bytes=len(normalized.encode()))
                except (SyntaxError, UnicodeError) as error:
                    row['parse_error'] = str(error)
                ROWS.append(row)


def main():
    manifest = json.loads((ROOT / 'evidence/source_manifest.json').read_text())
    for entry in manifest['drafts']:
        payload = (ROOT / 'reference/corpus' / entry['name']).read_bytes()
        git_blob = hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest()
        if len(payload) != entry['size'] or git_blob != entry['sha']:
            raise SystemExit('Archive identity mismatch: ' + entry['name'])
        scan(payload, entry['name'])
    summary = {'commit': manifest['commit'], 'root_archives': len(manifest['drafts']),
               'distinct_zip_contents': len(SEEN), 'python_occurrences': len(ROWS),
               'distinct_python_hashes': len({r['source_sha256'] for r in ROWS})}
    if (summary['distinct_zip_contents'], summary['python_occurrences'],
            summary['distinct_python_hashes']) != (14, 342, 164):
        raise SystemExit('Inventory changed: ' + json.dumps(summary))
    (ROOT / 'evidence/corpus_replay.json').write_text(
        json.dumps({'summary': summary, 'sources': ROWS}, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
