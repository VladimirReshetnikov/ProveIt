"""Read-only source census. Source is parsed but never imported or executed."""
import ast
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zipfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('concise_ipra_root', type=Path, help='ConciseIPRA directory in the pinned repository checkout')
parser.add_argument('--output', type=Path, default=Path('audit_frontier_reproduced.json'))
args = parser.parse_args()
ROOT = args.concise_ipra_root.resolve()
DEST = args.output
if not ROOT.is_dir():
    raise SystemExit('The supplied ConciseIPRA directory does not exist.')
OMIT = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
rows, failures, archive_info = [], [], []

def inspect(label, raw):
    try:
        source = raw.decode('utf-8-sig')
        tree = ast.parse(source)
        normalized = ast.unparse(tree) + '\n'
        tokens = sum(t.type not in OMIT for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
        rows.append(dict(path=label, tokens=tokens, ast_nodes=sum(1 for _ in ast.walk(tree)),
            normalized_bytes=len(normalized.encode('utf-8')), source_sha256=hashlib.sha256(raw).hexdigest(),
            normalized_sha256=hashlib.sha256(normalized.encode('utf-8')).hexdigest(),
            executable_marker=('ACCEPT' in source), has_eval=any(isinstance(n,ast.Name) and n.id in ('eval','exec') for n in ast.walk(tree))))
    except Exception as e:
        failures.append(dict(path=label,error=type(e).__name__+': '+str(e)[:180]))

def visit(label, raw):
    if label.endswith('.zip'):
        archive_info.append(dict(path=label, size=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
        try:
            with zipfile.ZipFile(io.BytesIO(raw)) as z:
                for i in z.infolist():
                    if not i.is_dir() and i.filename.endswith(('.py','.py.gz','.py.normalized.gz','.zip')):
                        visit(label+'!'+i.filename,z.read(i))
        except Exception as e: failures.append(dict(path=label,error=str(e)))
    elif label.endswith(('.py.gz','.py.normalized.gz')):
        try: inspect(label, gzip.decompress(raw))
        except Exception as e: failures.append(dict(path=label,error=str(e)))
    elif label.endswith('.py'): inspect(label,raw)

for p in sorted(ROOT.rglob('*')):
    if p.is_file() and p.name.endswith(('.py','.py.gz','.py.normalized.gz','.zip')):
        visit(str(p.relative_to(ROOT)),p.read_bytes())
result = dict(python=platform.python_version(), root=str(ROOT),
    metric='whole-module ast.unparse + LF, significant normalized-source tokens, ast.walk nodes',
    entries=len(rows), unique_source_contents=len({r['source_sha256'] for r in rows}),
    archives=archive_info,failures=failures,rows=rows)
DEST.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('rows','archives')},indent=2))
for key in ('tokens','ast_nodes','normalized_bytes'):
    unique={}
    for row in rows:
        if row['executable_marker'] and not any(s in row['path'].lower() for s in ('unsound','diagnostic','negative')):
            unique.setdefault(row['normalized_sha256'],row)
    print('\n'+key)
    for row in sorted(unique.values(),key=lambda r:r[key])[:25]:
        print(row['tokens'],row['ast_nodes'],row['normalized_bytes'],row['path'])
